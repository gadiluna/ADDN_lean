import Counting.ExternalInitialLayout
import Counting.ExternalInitialAdjacent

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine FiniteConstraints Tableau InitialRows

/-- Consecutive witness cells forbid a bit after the first blank. -/
def initialBinaryAllowed (program : Machine.Program) (tuple : Fin 2 → Fin (Cellular.alphabet program)) : Bool :=
  decide (((Cellular.cellEquiv program).symm (tuple 0)).1=Machine.Symbol.blank →
    ((Cellular.cellEquiv program).symm (tuple 1)).1=Machine.Symbol.blank)

def initialBinaryTemplate (program : Machine.Program) : List (List (Nat × Bool)) :=
  ((tuples (Cellular.alphabet program) 2).filter (fun tuple => !initialBinaryAllowed program tuple)).map
    (fun tuple => (List.finRange 2).map (fun position => (Cellular.alphabet program*position.val+(tuple position).val,false)))

theorem initialBinary_raw {width : Nat} (setup : Setup width) (program : Machine.Program)
    (place : Fin (setup.capacity-1)) :
    shiftedClauses (Cellular.alphabet program*(setup.offset.val+setup.header.length+place.val))
      (initialBinaryTemplate program)=
      (setup.binary program (adjacentLeft setup.capacity place) (adjacentRight setup.capacity place)).toCNF.map
        (List.map CNFEncoding.literalRaw) := by
  unfold initialBinaryTemplate Setup.binary Constraint.toCNF
  simp only [shiftedClauses,List.map_map,Function.comp_def]
  apply congrArg (List.map · ((tuples (Cellular.alphabet program) 2).filter
    (fun tuple => !initialBinaryAllowed program tuple)))
  funext tuple
  simp only [shiftedLiterals,List.map_map,Function.comp_def]
  apply congrArg (List.map · (List.finRange 2))
  funext index
  fin_cases index <;>
    simp [CNFEncoding.literalRaw,lit,bitIndex,finProdFinEquiv,
      Setup.witnessIndex,adjacentLeft,adjacentRight,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def initialBinaryBytes (program : Machine.Program) (base : Nat) :=
  Encoding.sequence clauseCodec (shiftedClauses (Cellular.alphabet program*base) (initialBinaryTemplate program))

theorem initialBinaryBytes_eq {time width : Nat} (setup : Setup width) (program : Machine.Program)
    (place : Fin (setup.capacity-1)) :
    initialBinaryBytes program (setup.offset.val+setup.header.length+place.val)=
      Encoding.sequence clauseCodec ((initialConstraint (T:=time)
        (setup.binary program (adjacentLeft setup.capacity place) (adjacentRight setup.capacity place))).toCNF.map
          (List.map CNFEncoding.literalRaw)) := by
  rw [initialConstraint_raw]
  unfold initialBinaryBytes
  rw [initialBinary_raw]

end Counting.External.CookLevin.StackGenerator
