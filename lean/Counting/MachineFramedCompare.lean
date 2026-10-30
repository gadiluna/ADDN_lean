import Counting.StackCompareLength
import Counting.StackEncodingPairMachine

/-! Executable comparisons on the actual sequential pair-of-frames codec.
Malformed inputs and trailing data produce false, with a total time bound. -/
namespace Counting.StackMachine.Compare.Framed
open EncodingPrograms

inductive Kind where
  | equality
  | lengthLE
  deriving DecidableEq, Repr

def answer (kind : Kind) (a b : List Bool) : Bool := match kind with
  | .equality => decide (a=b)
  | .lengthLE => decide (a.length≤b.length)

def compareRoutine (kind : Kind) : Routine 3 := match kind with
  | .equality => Routine.ofProgram (equalityProgram 3 2 3 1)
  | .lengthLE => Routine.ofProgram (lengthLEProgram 3 2 3 1)

def compareCost (kind : Kind) (a b : List Bool) : Nat := match kind with
  | .equality => equalityCost a b
  | .lengthLE => a.length+b.length+3

theorem compareCost_le (kind : Kind) (a b : List Bool) : compareCost kind a b ≤ a.length+b.length+5 := by
  cases kind with
  | equality => exact equalityCost_le a b
  | lengthLE => dsimp [compareCost]; omega

theorem compare_executes (kind : Kind) (store : Fin 5 → List Bool) :
    Routine.Executes (compareRoutine kind) store (compareCost kind (store 2) (store 3))
      (Function.update (Function.update (Function.update store 2 []) 3 []) 1
        (answer kind (store 2) (store 3)::store 1)) := by
  cases kind with
  | equality => exact equality_executes 3 2 3 1 (by decide) (by decide) (by decide) store
  | lengthLE => exact lengthLE_executes 3 2 3 1 (by decide) (by decide) (by decide) store

def routine (kind : Kind) : Routine 3 :=
  Routine.sequence (pairRoutine 0 pairRecognitionRegisters)
    (Routine.sequence (compareRoutine kind)
      (Routine.sequence (Routine.ofProgram (combineFlagsProgram 3 1))
        (Routine.sequence (Routine.ofProgram (equalityProgram 3 0 4 1))
          (Routine.ofProgram (combineFlagsProgram 3 1)))))

def check (kind : Kind) (input : List Bool) : Bool :=
  let parsed := parsePair input
  (parsed.accepted && answer kind parsed.first parsed.second) && decide (parsed.suffix=[])

def parsedStore (parsed : PairParseResult) : Fin 5 → List Bool :=
  ![parsed.suffix,[parsed.accepted],parsed.first,parsed.second,[]]

def comparedStore (parsed : PairParseResult) (kind : Kind) : Fin 5 → List Bool :=
  ![parsed.suffix,[answer kind parsed.first parsed.second,parsed.accepted],[],[],[]]

def combinedStore (parsed : PairParseResult) (kind : Kind) : Fin 5 → List Bool :=
  ![parsed.suffix,[parsed.accepted && answer kind parsed.first parsed.second],[],[],[]]

def checkedStore (parsed : PairParseResult) (kind : Kind) : Fin 5 → List Bool :=
  ![[],[decide (parsed.suffix=[]),parsed.accepted && answer kind parsed.first parsed.second],[],[],[]]

/-- Parsing, both comparisons, status conjunctions and four sequencing
jumps are all included. No decoder is evaluated by the stack program. -/
theorem computes (kind : Kind) : ComputesIn (routine kind).program
    (fun input => [check kind input]) (fun length => 7*length+33) := by
  intro input
  let store : Fin 5 → List Bool := fun r => if r=0 then input else []
  let parsed := parsePair input
  have initialParsed : pairExpected 0 pairRecognitionRegisters store = parsedStore parsed := by
    funext r
    fin_cases r <;> simp [pairExpected,pairRecognitionRegisters,parsedStore,store,parsed]
  obtain ⟨parseTime,parseBound,parseRun⟩ := pair_executes_spec 0 pairRecognitionRegisters
    pairRecognitionRegisters_injective store (by rfl)
  rw [initialParsed] at parseRun
  have comparison : Routine.Executes (compareRoutine kind) (parsedStore parsed)
      (compareCost kind parsed.first parsed.second) (comparedStore parsed kind) := by
    have executed := compare_executes kind (parsedStore parsed)
    have result : Function.update (Function.update (Function.update (parsedStore parsed) 2 []) 3 []) 1
        (answer kind parsed.first parsed.second::(parsedStore parsed) 1) = comparedStore parsed kind := by
      funext r
      fin_cases r <;> rfl
    simpa only [show parsedStore parsed 2=parsed.first from rfl,
      show parsedStore parsed 3=parsed.second from rfl,result] using executed
  have combined : Routine.Executes (Routine.ofProgram (combineFlagsProgram 3 1)) (comparedStore parsed kind) 3
      (combinedStore parsed kind) := by
    have executed := combineFlags_executes 3 1 (comparedStore parsed kind) parsed.accepted
      (answer kind parsed.first parsed.second) [] (by rfl)
    convert executed using 1
    funext r
    fin_cases r <;> rfl
  have checked : Routine.Executes (Routine.ofProgram (equalityProgram 3 0 4 1)) (combinedStore parsed kind)
      (equalityCost parsed.suffix []) (checkedStore parsed kind) := by
    have executed := equality_executes 3 0 4 1 (by decide) (by decide) (by decide) (combinedStore parsed kind)
    convert executed using 1
    · rfl
    · funext r
      fin_cases r <;> rfl
  have finished := combineFlags_executes 3 1 (checkedStore parsed kind)
    (parsed.accepted && answer kind parsed.first parsed.second) (decide (parsed.suffix=[])) [] (by rfl)
  have composed := parseRun.sequence (comparison.sequence (combined.sequence (checked.sequence finished)))
  obtain ⟨finish,ran,halted,result⟩ := composed
  refine ⟨parseTime+1+(compareCost kind parsed.first parsed.second+1+(3+1+(equalityCost parsed.suffix []+1+3))),
    finish,?_,⟨ran,halted⟩,?_⟩
  · have firstBound := compareCost_le kind parsed.first parsed.second
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
theorem computesCleanIn (kind : Kind) : Complexity.ComputesCleanIn (Compiler.compile (routine kind).program)
    (fun input => [check kind input]) (Complexity.polynomial 32000 2) := by
  have compiled := Compiler.computesCleanIn (computes kind)
  intro input
  obtain ⟨steps,finish,bounded,halted,tape⟩ := compiled input
  refine ⟨steps,finish,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+3+(7*input.length+33)+4)^2 ≤ 32000*(input.length+1)^2
  have base : input.length+3+(7*input.length+33)+4 ≤ 40*(input.length+1) := by omega
  calc
    _ ≤ 20*(40*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem check_frames (kind : Kind) (a b : List Bool) :
    check kind (Encoding.frame a++Encoding.frame b) = answer kind a b := by
  have parsed := parsePair_frames a b []
  simp only [List.append_nil] at parsed
  simp only [check,parsed,Bool.true_and,decide_true,Bool.and_true]

theorem check_trailing (kind : Kind) (a b suffix : List Bool) (nonempty : suffix ≠ []) :
    check kind (Encoding.frame a++Encoding.frame b++suffix) = false := by
  simp only [check,parsePair_frames,nonempty,decide_false,Bool.and_false]

theorem parsePair_sound (input : List Bool) (valid : (parsePair input).accepted=true) :
    input = Encoding.frame (parsePair input).first++Encoding.frame (parsePair input).second++(parsePair input).suffix := by
  cases first : Encoding.unframe input with
  | none => simp [parsePair,first] at valid
  | some pair =>
      obtain ⟨a,rest⟩ := pair
      cases second : Encoding.unframe rest with
      | none => simp [parsePair,first,second] at valid
      | some pair =>
          obtain ⟨b,suffix⟩ := pair
          simp only [parsePair,first,second]
          rw [Machine.unframe_sound input a rest first,Machine.unframe_sound rest b suffix second,List.append_assoc]

/-- Exact agreement with the public codec, including every malformed word
and every nonempty trailing suffix. -/
theorem check_true_iff (kind : Kind) (input : List Bool) :
    check kind input=true ↔ ∃ a b,
      (Encoding.product frameCodec frameCodec).decodeExact input=some (a,b) ∧ answer kind a b=true := by
  constructor
  · intro accepted
    have parts : (parsePair input).accepted=true ∧
        answer kind (parsePair input).first (parsePair input).second=true ∧ (parsePair input).suffix=[] := by
      simpa only [check,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using accepted
    refine ⟨(parsePair input).first,(parsePair input).second,?_,parts.2.1⟩
    rw [Encoding.Codec.decodeExact_iff]
    have sound := parsePair_sound input parts.1
    rw [parts.2.2,List.append_nil] at sound
    exact sound.symm
  · rintro ⟨a,b,decoded,accepted⟩
    have encoded := (Encoding.Codec.decodeExact_iff _ input (a,b)).mp decoded
    change Encoding.frame a++Encoding.frame b=input at encoded
    rw [←encoded,check_frames]
    exact accepted

end Counting.StackMachine.Compare.Framed
