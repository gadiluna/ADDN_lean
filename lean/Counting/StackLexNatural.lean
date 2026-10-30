import Counting.StackLexPair

namespace Counting.StackMachine.Lexicographic
open Routine

theorem compareBits_natural (left right : Nat) :
    Binary.compareBits true left.bits right.bits=decide (left≤right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Binary.compareBits_le,Encoding.value_bits,decide_eq_true_eq]

theorem bits_equal_natural (left right : Nat) :
    decide (left.bits=right.bits)=decide (left=right) := by
  simp only [Encoding.bits_injective.eq_iff]

def naturalPairResult (store : Store 8) (left right : Nat) (unresolved answer : Bool) : Store 8 :=
  Function.update (Function.update (Function.update (Function.update store 0 []) 1 [])
    2 [unresolved && decide (left=right)])
    3 [if unresolved && !(decide (left=right)) then decide (left≤right) else answer]

/-- The physical pair comparator implements numeric comparison on canonical
binary inputs, including zero and arbitrarily large values. -/
theorem pair_naturals (store : Store 8) (left right : Nat) (unresolved answer : Bool)
    (leftAt : store 0=left.bits) (rightAt : store 1=right.bits)
    (openAt : store 2=[unresolved]) (answerAt : store 3=[answer])
    (empty : ∀ r : Fin 10,4≤r.val → store r=[]) :
    Executes pair store (pairCost left.bits right.bits unresolved)
      (naturalPairResult store left right unresolved answer) := by
  have run := pair_executes store unresolved answer openAt answerAt empty
  simpa only [leftAt,rightAt,pairResult,compareBits_natural,bits_equal_natural,naturalPairResult] using run

end Counting.StackMachine.Lexicographic
