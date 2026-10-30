import Counting.ExternalInitialUnaryLoop
import Counting.ExternalInitialBinaryLoop

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau InitialRows

/-- Prepending makes the binary block run first; the resulting bytes retain
unary-before-binary order from the mathematical setup. -/
def initialRowRoutine (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  sequence (initialBinaryRow extra w program) (initialUnaryRow extra w program)

def initialRowBound (program : Machine.Program) (width capacity : Nat) :=
  initialBinaryRowBound program width capacity+1+initialUnaryRowBound program width

theorem initialRowRoutine_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    {time width : Nat} (setup : Setup width) (store : Fin (extra+24) → List Bool)
    (offsetValue : store (w 1)=List.replicate setup.offset.val true) (headerValue : store (w 2)=setup.header)
    (capacityValue : store (w 3)=List.replicate setup.capacity true)
    (widthValue : store (w 4)=List.replicate width true) (placeEmpty : store (w 0)=[])
    (empty : ∀ i ∈ ([6,7,8,9,10,11,12,13,14,15,17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialRowBound program width setup.capacity,
      Executes (initialRowRoutine extra w program) store transitions
        (Function.update store (w 5)
          ((List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
            ((initialConstraint (T:=time) (setup.unary program place)).toCNF.map (List.map CNFEncoding.literalRaw)))++
           (List.finRange (setup.capacity-1)).flatMap (fun place => Encoding.sequence clauseCodec
             ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity place)
               (adjacentRight setup.capacity place))).toCNF.map (List.map CNFEncoding.literalRaw)))++store (w 5))) := by
  obtain ⟨binaryTime,binaryBound,binaryRun⟩ := initialBinaryRow_executes extra w program (time:=time) setup store
    offsetValue headerValue capacityValue placeEmpty
    (fun i hi => empty i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let middle := Function.update store (w 5)
    ((List.finRange (setup.capacity-1)).flatMap (fun place => Encoding.sequence clauseCodec
      ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity place)
        (adjacentRight setup.capacity place))).toCNF.map (List.map CNFEncoding.literalRaw)))++store (w 5))
  obtain ⟨unaryTime,unaryBound,unaryRun⟩ := initialUnaryRow_executes extra w program (time:=time) setup middle
    (by simp [middle,w.injective.eq_iff,offsetValue])
    (by simp [middle,w.injective.eq_iff,headerValue])
    (by simp [middle,w.injective.eq_iff,capacityValue])
    (by simp [middle,w.injective.eq_iff,widthValue])
    (by simp [middle,w.injective.eq_iff,placeEmpty])
    (by
      intro i hi
      have different : i ≠ 5 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [middle,w.injective.eq_iff,different] using empty i hi)
  have combined := binaryRun.sequence unaryRun
  refine ⟨binaryTime+1+unaryTime,by unfold initialRowBound; omega,?_⟩
  simpa only [initialRowRoutine,middle,Function.update_self,Function.update_idem,List.append_assoc] using combined

theorem initialRowBound_polynomial (program : Machine.Program) {width : Nat} (setup : Setup width) :
    initialRowBound program width setup.capacity ≤
      (initialCoefficient program+initialBinaryCoefficient program+270)*(width+1)^3 := by
  have fits := setup.fits
  have capacity : setup.capacity≤width := by omega
  have predecessor : setup.capacity-1≤width := (Nat.sub_le _ _).trans capacity
  have multiplied := Nat.mul_le_mul_right ((initialBinaryCoefficient program+17)*(width+1)^2+2) predecessor
  unfold initialRowBound initialBinaryRowBound initialUnaryRowBound
  nlinarith

end Counting.External.CookLevin.StackGenerator
