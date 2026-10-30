import Counting.StackAuditCompleteCostTools
import Counting.StackAuditComplete

namespace Counting.StackMachine.AuditComplete

def anchorInputBound (size : Nat) : Nat := 8*size
def solverOutputBound (size : Nat) : Nat :=
  anchorInputBound size+AnchorSolve.polynomialCoefficient*(anchorInputBound size)^4500
def postInputBound (size : Nat) : Nat := 10*size+solverOutputBound size
def weightsOutputBound (size : Nat) : Nat :=
  postInputBound size+AuditPostSolver.completeCoefficient*(postInputBound size)^51
def descendantInputBound (size : Nat) : Nat := 10*size+weightsOutputBound size
def descendantCostBound (size : Nat) : Nat :=
  40*descendantInputBound size+AuditDescendant.completeCoefficient*(descendantInputBound size)^7+
    41*(size+weightsOutputBound size+1)+2
def suffixCostBound (size : Nat) : Nat :=
  30*postInputBound size+AuditPostSolver.completeCoefficient*(postInputBound size)^51+
    descendantCostBound size+4
def selectedCostBound (size : Nat) : Nat :=
  30*anchorInputBound size+AnchorSolve.polynomialCoefficient*(anchorInputBound size)^4500+
    suffixCostBound size+2
def afterPrefixCostBound (size : Nat) : Nat :=
  20*(size+1)+100*(size+size+1)+selectedCostBound size+9
def rawCostBound (size : Nat) : Nat :=
  51*size+AuditPrefix.completeCoefficient*size^7+afterPrefixCostBound size+2
def completeCostBound (size : Nat) : Nat := 65*rawCostBound size+64*size+129

theorem anchorInputBound_poly : PolyBound anchorInputBound := PolyBound.identity.scale 8
theorem solverOutputBound_poly : PolyBound solverOutputBound :=
  anchorInputBound_poly.add ((anchorInputBound_poly.power 4500).scale AnchorSolve.polynomialCoefficient)
theorem postInputBound_poly : PolyBound postInputBound :=
  (PolyBound.identity.scale 10).add solverOutputBound_poly
theorem weightsOutputBound_poly : PolyBound weightsOutputBound :=
  postInputBound_poly.add ((postInputBound_poly.power 51).scale AuditPostSolver.completeCoefficient)
theorem descendantInputBound_poly : PolyBound descendantInputBound :=
  (PolyBound.identity.scale 10).add weightsOutputBound_poly
theorem descendantCostBound_poly : PolyBound descendantCostBound :=
  (((descendantInputBound_poly.scale 40).add
    ((descendantInputBound_poly.power 7).scale AuditDescendant.completeCoefficient)).add
      (((PolyBound.identity.add weightsOutputBound_poly).add (PolyBound.constant 1)).scale 41)).add (PolyBound.constant 2)
theorem suffixCostBound_poly : PolyBound suffixCostBound :=
  (((postInputBound_poly.scale 30).add
    ((postInputBound_poly.power 51).scale AuditPostSolver.completeCoefficient)).add
      descendantCostBound_poly).add (PolyBound.constant 4)
theorem selectedCostBound_poly : PolyBound selectedCostBound :=
  (((anchorInputBound_poly.scale 30).add
    ((anchorInputBound_poly.power 4500).scale AnchorSolve.polynomialCoefficient)).add
      suffixCostBound_poly).add (PolyBound.constant 2)
theorem afterPrefixCostBound_poly : PolyBound afterPrefixCostBound :=
  ((((PolyBound.identity.add (PolyBound.constant 1)).scale 20).add
    (((PolyBound.identity.add PolyBound.identity).add (PolyBound.constant 1)).scale 100)).add
      selectedCostBound_poly).add (PolyBound.constant 9)
theorem rawCostBound_poly : PolyBound rawCostBound :=
  (((PolyBound.identity.scale 51).add ((PolyBound.identity.power 7).scale AuditPrefix.completeCoefficient)).add
    afterPrefixCostBound_poly).add (PolyBound.constant 2)
theorem completeCostBound_poly : PolyBound completeCostBound :=
  ((rawCostBound_poly.scale 65).add (PolyBound.identity.scale 64)).add (PolyBound.constant 129)

end Counting.StackMachine.AuditComplete
