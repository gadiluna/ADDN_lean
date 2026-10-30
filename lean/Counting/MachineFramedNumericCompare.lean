import Counting.StackBinaryCompareRoutine
import Counting.MachineFramedCompare
import Counting.StackEncodingPairMachine

/-! Executable comparisons on the actual sequential pair-of-frames codec.
Malformed inputs and trailing data produce false, with a total time bound. -/
namespace Counting.StackMachine.Compare.NumericFramed
open EncodingPrograms

def answer (a b : List Bool) : Bool := Binary.compareBits true a b

def compareRoutine : Routine 3 := Routine.ofProgram (Binary.compareProgram 2 2 3 1)

def compareCost (a b : List Bool) : Nat := 2*max a.length b.length+3

theorem compareCost_le (a b : List Bool) : compareCost a b ≤ 2*(a.length+b.length)+5 := by
  have bound : max a.length b.length ≤ a.length+b.length := by omega
  dsimp only [compareCost]
  omega

theorem compare_executes (store : Fin 5 → List Bool) :
    Routine.Executes compareRoutine store (compareCost (store 2) (store 3))
      (Function.update (Function.update (Function.update store 2 []) 3 []) 1
        (answer (store 2) (store 3)::store 1)) :=
  Routine.binary_compare_executes 2 2 3 1 (by decide) (by decide) (by decide) store

def routine : Routine 3 :=
  Routine.sequence (pairRoutine 0 pairRecognitionRegisters)
    (Routine.sequence (compareRoutine)
      (Routine.sequence (Routine.ofProgram (combineFlagsProgram 3 1))
        (Routine.sequence (Routine.ofProgram (equalityProgram 3 0 4 1))
          (Routine.ofProgram (combineFlagsProgram 3 1)))))

def check (input : List Bool) : Bool :=
  let parsed := parsePair input
  (parsed.accepted && answer parsed.first parsed.second) && decide (parsed.suffix=[])

def parsedStore (parsed : PairParseResult) : Fin 5 → List Bool :=
  ![parsed.suffix,[parsed.accepted],parsed.first,parsed.second,[]]

def comparedStore (parsed : PairParseResult) : Fin 5 → List Bool :=
  ![parsed.suffix,[answer parsed.first parsed.second,parsed.accepted],[],[],[]]

def combinedStore (parsed : PairParseResult) : Fin 5 → List Bool :=
  ![parsed.suffix,[parsed.accepted && answer parsed.first parsed.second],[],[],[]]

def checkedStore (parsed : PairParseResult) : Fin 5 → List Bool :=
  ![[],[decide (parsed.suffix=[]),parsed.accepted && answer parsed.first parsed.second],[],[],[]]

/-- Parsing, numeric order, suffix checking, conjunctions and four sequencing
jumps are all included. No decoder is evaluated by the stack program. -/
theorem computes : ComputesIn (routine).program
    (fun input => [check input]) (fun length => 8*length+33) := by
  intro input
  let store : Fin 5 → List Bool := fun r => if r=0 then input else []
  let parsed := parsePair input
  have initialParsed : pairExpected 0 pairRecognitionRegisters store = parsedStore parsed := by
    funext r
    fin_cases r <;> simp [pairExpected,pairRecognitionRegisters,parsedStore,store,parsed]
  obtain ⟨parseTime,parseBound,parseRun⟩ := pair_executes_spec 0 pairRecognitionRegisters
    pairRecognitionRegisters_injective store (by rfl)
  rw [initialParsed] at parseRun
  have comparison : Routine.Executes (compareRoutine) (parsedStore parsed)
      (compareCost parsed.first parsed.second) (comparedStore parsed) := by
    have executed := compare_executes (parsedStore parsed)
    have result : Function.update (Function.update (Function.update (parsedStore parsed) 2 []) 3 []) 1
        (answer parsed.first parsed.second::(parsedStore parsed) 1) = comparedStore parsed := by
      funext r
      fin_cases r <;> rfl
    simpa only [show parsedStore parsed 2=parsed.first from rfl,
      show parsedStore parsed 3=parsed.second from rfl,result] using executed
  have combined : Routine.Executes (Routine.ofProgram (combineFlagsProgram 3 1)) (comparedStore parsed) 3
      (combinedStore parsed) := by
    have executed := combineFlags_executes 3 1 (comparedStore parsed) parsed.accepted
      (answer parsed.first parsed.second) [] (by rfl)
    convert executed using 1
    funext r
    fin_cases r <;> rfl
  have checked : Routine.Executes (Routine.ofProgram (equalityProgram 3 0 4 1)) (combinedStore parsed)
      (equalityCost parsed.suffix []) (checkedStore parsed) := by
    have executed := equality_executes 3 0 4 1 (by decide) (by decide) (by decide) (combinedStore parsed)
    convert executed using 1
    · rfl
    · funext r
      fin_cases r <;> rfl
  have finished := combineFlags_executes 3 1 (checkedStore parsed)
    (parsed.accepted && answer parsed.first parsed.second) (decide (parsed.suffix=[])) [] (by rfl)
  have composed := parseRun.sequence (comparison.sequence (combined.sequence (checked.sequence finished)))
  obtain ⟨finish,ran,halted,result⟩ := composed
  refine ⟨parseTime+1+(compareCost parsed.first parsed.second+1+(3+1+(equalityCost parsed.suffix []+1+3))),
    finish,?_,⟨ran,halted⟩,?_⟩
  · have firstBound := compareCost_le parsed.first parsed.second
    have suffixBound := equalityCost_le parsed.suffix []
    have sizeBound := parsePair_length_bound input
    change parseTime ≤ 6*input.length+13 at parseBound
    change parsed.first.length+parsed.second.length+parsed.suffix.length ≤ input.length at sizeBound
    simp only [List.length_nil] at suffixBound
    dsimp only
    omega
  · rw [result]
    rfl

/-- The bound counts physical tape transitions, including bootstrap and
cleanup, uniformly for all binary words rather than only valid pairs. -/
theorem computesCleanIn : Complexity.ComputesCleanIn (Compiler.compile (routine).program)
    (fun input => [check input]) (Complexity.polynomial 32000 2) := by
  have compiled := Compiler.computesCleanIn (computes)
  intro input
  obtain ⟨steps,finish,bounded,halted,tape⟩ := compiled input
  refine ⟨steps,finish,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+3+(8*input.length+33)+4)^2 ≤ 32000*(input.length+1)^2
  have base : input.length+3+(8*input.length+33)+4 ≤ 40*(input.length+1) := by omega
  calc
    _ ≤ 20*(40*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem check_frames (a b : List Bool) :
    check (Encoding.frame a++Encoding.frame b) = answer a b := by
  have parsed := parsePair_frames a b []
  simp only [List.append_nil] at parsed
  simp only [check,parsed,Bool.true_and,decide_true,Bool.and_true]

theorem check_trailing (a b suffix : List Bool) (nonempty : suffix ≠ []) :
    check (Encoding.frame a++Encoding.frame b++suffix) = false := by
  simp only [check,parsePair_frames,nonempty,decide_false,Bool.and_false]

/-- Exact agreement with the public codec, including every malformed word
and every nonempty trailing suffix. -/
theorem check_true_iff (input : List Bool) :
    check input=true ↔ ∃ a b,
      (Encoding.product frameCodec frameCodec).decodeExact input=some (a,b) ∧ answer a b=true := by
  constructor
  · intro accepted
    have parts : (parsePair input).accepted=true ∧
        answer (parsePair input).first (parsePair input).second=true ∧ (parsePair input).suffix=[] := by
      simpa only [check,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using accepted
    refine ⟨(parsePair input).first,(parsePair input).second,?_,parts.2.1⟩
    rw [Encoding.Codec.decodeExact_iff]
    have sound := Framed.parsePair_sound input parts.1
    rw [parts.2.2,List.append_nil] at sound
    exact sound.symm
  · rintro ⟨a,b,decoded,accepted⟩
    have encoded := (Encoding.Codec.decodeExact_iff _ input (a,b)).mp decoded
    change Encoding.frame a++Encoding.frame b=input at encoded
    rw [←encoded,check_frames]
    exact accepted

/-- The public natural-pair layout uses the same charged parser and returns
numeric order, including unequal binary widths and zero operands. -/
theorem natural_correct (first second : Nat) :
    check ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) = decide (first≤second) := by
  change check (Encoding.frame first.bits++Encoding.frame second.bits) = _
  rw [check_frames]
  apply Bool.eq_iff_iff.mpr
  rw [answer,Binary.compareBits_le,Encoding.value_bits,Encoding.value_bits,decide_eq_true_eq]

end Counting.StackMachine.Compare.NumericFramed
