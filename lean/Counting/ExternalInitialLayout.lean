import Counting.ExternalInitialCell
import Counting.ExternalTableau

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine FiniteConstraints Tableau InitialRows

/-- Moving a constraint to tableau row zero does not change its numeric literal identifiers. -/
theorem initialConstraint_raw {time width alphabet : Nat} (constraint : Constraint width alphabet) :
    (initialConstraint (T:=time) constraint).toCNF.map (List.map CNFEncoding.literalRaw)=
      constraint.toCNF.map (List.map CNFEncoding.literalRaw) := by
  simp [initialConstraint,Constraint.toCNF,List.map_map,Function.comp_def,CNFEncoding.literalRaw,
    lit,bitIndex,index,finProdFinEquiv]

theorem initialBytes_eq {time width : Nat} (setup : Setup width) (program : Machine.Program) (place : Fin width) :
    initialBytes program (decide (place.val=setup.offset.val))
      (initialKind place.val setup.offset.val setup.header setup.capacity) place.val=
      Encoding.sequence clauseCodec
        ((initialConstraint (T:=time) (setup.unary program place)).toCNF.map (List.map CNFEncoding.literalRaw)) := by
  rw [initialConstraint_raw]
  unfold initialBytes
  rw [unaryConstraint_raw (nodes:=width) place]
  have same : unaryConstraint place (initialAllowed program (decide (place.val=setup.offset.val))
      (initialKind place.val setup.offset.val setup.header setup.capacity))=setup.unary program place := by
    unfold unaryConstraint Setup.unary
    congr 1
    funext tuple
    exact initialAllowed_eq setup program place (tuple 0)
  rw [same]

theorem initialCellBound_polynomial (program : Machine.Program) {width : Nat} (setup : Setup width) (place : Fin width) :
    initialCellBound program place.val setup.offset.val setup.header.length setup.capacity ≤
      (initialCoefficient program+213)*(width+1)^2 := by
  have p := Nat.le_of_lt place.isLt
  have o := Nat.le_of_lt setup.offset.isLt
  have fits := setup.fits
  have square : place.val+1≤width+1 := by omega
  have power := Nat.pow_le_pow_left square 2
  have multiplied := Nat.mul_le_mul_left (initialCoefficient program) power
  unfold initialCellBound
  nlinarith

end Counting.External.CookLevin.StackGenerator
