import Counting.StackRationalPairSpec
import Counting.StackCompare
import Counting.StackEncodingPairMachine
import Counting.StackCompilerComplete

namespace Counting.StackMachine.RationalArithmetic.Equality
open Routine Pair

abbrev compare (left right : Fin 9) : Routine 7 :=
  ofProgram (Compare.equalityProgram 7 left right 6)
abbrev combine : Routine 7 := ofProgram (EncodingPrograms.combineFlagsProgram 7 6)
abbrev routine : Routine 7 := sequence parser
  (sequence (compare 0 2) (sequence (compare 1 3)
    (sequence combine (sequence (compare 4 5)
      (sequence combine (move 6 6 1 7))))))

def check (input : List Bool) : Bool :=
  (decide ((first input).first=(second input).first) &&
    decide ((first input).second=(second input).second)) &&
    decide (firstSign input=secondSign input)

theorem numerator_executes (a b c d sa sc flags : List Bool) :
    Executes (compare 0 2) (Pair.file a b c d sa sc flags) (Compare.equalityCost a c)
      (Pair.file [] b [] d sa sc (decide (a=c)::flags)) := by
  have executed := Compare.equality_executes 7 0 2 6 (by decide) (by decide) (by decide)
    (Pair.file a b c d sa sc flags)
  have result : Function.update (Function.update (Function.update
      (Pair.file a b c d sa sc flags) 0 []) 2 []) 6 (decide (a=c)::flags) =
      Pair.file [] b [] d sa sc (decide (a=c)::flags) := by
    funext r; fin_cases r <;> rfl
  exact result ▸ executed

theorem denominator_executes (b d sa sc flags : List Bool) :
    Executes (compare 1 3) (Pair.file [] b [] d sa sc flags) (Compare.equalityCost b d)
      (Pair.file [] [] [] [] sa sc (decide (b=d)::flags)) := by
  have executed := Compare.equality_executes 7 1 3 6 (by decide) (by decide) (by decide)
    (Pair.file [] b [] d sa sc flags)
  have result : Function.update (Function.update (Function.update
      (Pair.file [] b [] d sa sc flags) 1 []) 3 []) 6 (decide (b=d)::flags) =
      Pair.file [] [] [] [] sa sc (decide (b=d)::flags) := by
    funext r; fin_cases r <;> rfl
  exact result ▸ executed

theorem sign_executes (sa sc : Bool) (flags : List Bool) :
    Executes (compare 4 5) (Pair.file [] [] [] [] [sa] [sc] flags)
      (Compare.equalityCost [sa] [sc]) (Pair.file [] [] [] [] [] [] (decide (sa=sc)::flags)) := by
  have executed := Compare.equality_executes 7 4 5 6 (by decide) (by decide) (by decide)
    (Pair.file [] [] [] [] [sa] [sc] flags)
  have result : Function.update (Function.update (Function.update
      (Pair.file [] [] [] [] [sa] [sc] flags) 4 []) 5 []) 6
      (decide ([sa]=[sc])::flags) = Pair.file [] [] [] [] [] [] (decide (sa=sc)::flags) := by
    funext r; fin_cases r <;> simp [Pair.file]
  exact result ▸ executed

theorem combine_executes (sa sc : List Bool) (firstFlag secondFlag : Bool) :
    Executes combine (Pair.file [] [] [] [] sa sc [secondFlag,firstFlag]) 3
      (Pair.file [] [] [] [] sa sc [firstFlag && secondFlag]) := by
  have executed := EncodingPrograms.combineFlags_executes 7 6
    (Pair.file [] [] [] [] sa sc [secondFlag,firstFlag]) firstFlag secondFlag [] rfl
  have result : Function.update (Pair.file [] [] [] [] sa sc [secondFlag,firstFlag]) 6
      [firstFlag && secondFlag] = Pair.file [] [] [] [] sa sc [firstFlag && secondFlag] := by
    funext r; fin_cases r <;> rfl
  exact result ▸ executed

theorem computes : ComputesIn routine.program
    (fun input => Encoding.boolean.encode (check input)) (Complexity.polynomial 100 1) := by
  intro input
  let a := (first input).first
  let b := (first input).second
  let c := (second input).first
  let d := (second input).second
  let sa := firstSign input
  let sc := secondSign input
  let firstFlag := decide (a=c)
  let secondFlag := decide (b=d)
  let signFlag := decide (sa=sc)
  obtain ⟨parseTime,parseBound,parsed⟩ := parser_executes input
  have num := numerator_executes a b c d [sa] [sc] []
  have den := denominator_executes b d [sa] [sc] [firstFlag]
  have joined := combine_executes [sa] [sc] firstFlag secondFlag
  have signed := sign_executes sa sc [firstFlag && secondFlag]
  have finalFlag := combine_executes [] [] (firstFlag && secondFlag) signFlag
  have moved := move_executes 6 6 1 7 (by decide) (by decide) (by decide)
    (Pair.file [] [] [] [] [] [] [(firstFlag && secondFlag) && signFlag]) rfl
  obtain ⟨finish,ran,halted,stored⟩ := parsed.sequence
    (num.sequence (den.sequence (joined.sequence (signed.sequence (finalFlag.sequence moved)))))
  refine ⟨parseTime+1+(Compare.equalityCost a c+1+(Compare.equalityCost b d+1+
      (3+1+(Compare.equalityCost [sa] [sc]+1+(3+1+(6*1+4)))))),finish,?_,⟨?_,halted⟩,?_⟩
  · have numCost := Compare.equalityCost_le a c
    have denCost := Compare.equalityCost_le b d
    have signCost := Compare.equalityCost_le [sa] [sc]
    have sizes := Pair.parsed_lengths input
    change a.length+b.length+c.length+d.length+_ ≤ input.length at sizes
    simp only [List.length_cons,List.length_nil] at signCost
    change _ ≤ 100*(input.length+1)^1
    simp only [pow_one]
    omega
  · have start : initial routine.program input=⟨0,Pair.file input [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    rfl

theorem check_rationals (a b : Rat) :
    check ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = decide (a=b) := by
  simp only [check,first_rationals,second_rationals,firstSign_rationals,secondSign_rationals]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨num,den⟩,sign⟩
    apply Encoding.rational_injective
    simp only [Encoding.rational_encode,Encoding.integer_encode,Encoding.natural]
    rw [num,den,sign]
  · intro equal
    subst b
    exact ⟨⟨rfl,rfl⟩,rfl⟩

end Counting.StackMachine.RationalArithmetic.Equality

namespace Counting.Machine
open StackMachine.RationalArithmetic.Equality

def rationalEqualityProgram : Program := StackMachine.Compiler.compile routine.program

/-- Equality uses the existing sequential product-of-rationals codec. All
binary words have a total polynomial-time extension; canonicality checking
is not attributed to this comparison. -/
theorem rationalEquality_computesCleanIn : Complexity.ComputesCleanIn rationalEqualityProgram
    (fun input => Encoding.boolean.encode (check input)) (Complexity.polynomial 250880 2) := by
  have compiled := StackMachine.Compiler.computesCleanIn computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+7+100*(input.length+1)^1+4)^2 ≤ 250880*(input.length+1)^2
  simp only [pow_one]
  have base : input.length+7+100*(input.length+1)+4 ≤ 112*(input.length+1) := by omega
  calc
    _ ≤ 20*(112*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem rationalEquality_rationals_clean (a b : Rat) :
    ∃ time output,
      time ≤ 250880*((Encoding.product Encoding.rational Encoding.rational).encode (a,b)).length.succ^2 ∧
      HaltsAt rationalEqualityProgram ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((Encoding.boolean.encode (decide (a=b))).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalEquality_computesCleanIn
    ((Encoding.product Encoding.rational Encoding.rational).encode (a,b))
  refine ⟨time,output,bounded,halted,?_⟩
  dsimp only at tape
  rw [check_rationals] at tape
  exact tape

end Counting.Machine
