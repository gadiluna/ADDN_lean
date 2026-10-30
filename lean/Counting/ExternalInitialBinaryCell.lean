import Counting.ExternalInitialBinaryTemplate
import Counting.ExternalInitialBinaryBase

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine InitialRows

def initialBinarySelection : Fin 6 ↪ Fin 24 := ⟨![6,17,5,18,19,20],by decide⟩
def InitialWorkspace.binaryRoles (w : InitialWorkspace extra) : PolynomialWorkspace (extra+18) := initialBinarySelection.trans w

def initialBinaryCoefficient (program : Machine.Program) :=
  scaledClausesCoefficient (Cellular.alphabet program) (initialBinaryTemplate program)

def initialBinaryCell (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  sequence (initialBinaryBase extra w) (sequence
    (scaledClauses (extra+18) w.binaryRoles (Cellular.alphabet program) (initialBinaryTemplate program)) (clear (w 6)))

def initialBinaryCellBound (program : Machine.Program) (place offset headerLength : Nat) :=
  initialBinaryCoefficient program*(offset+headerLength+place+1)^2+6*(offset+headerLength+place)+11

theorem initialBinaryCell_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    (place offset : Nat) (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (empty : ∀ i ∈ ([6,17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialBinaryCellBound program place offset (store (w 2)).length,
      Executes (initialBinaryCell extra w program) store transitions
        (Function.update store (w 5)
          (initialBinaryBytes program (offset+(store (w 2)).length+place)++store (w 5))) := by
  let base := offset+(store (w 2)).length+place
  let measured := Function.update store (w 6) (List.replicate base true)
  let payload := initialBinaryBytes program base++store (w 5)
  let emitted := Function.update measured (w 5) payload
  have first := initialBinaryBase_executes extra w place offset store placeValue offsetValue
    (empty 6 (by simp)) (empty 20 (by simp))
  obtain ⟨emitTime,emitBound,emitRun⟩ := scaledClauses_executes (extra+18) w.binaryRoles (Cellular.alphabet program)
    (initialBinaryTemplate program) measured
    (by simp [measured,InitialWorkspace.binaryRoles,initialBinarySelection,w.injective.eq_iff,empty 17 (by simp)])
    (by simp [measured,InitialWorkspace.binaryRoles,initialBinarySelection,w.injective.eq_iff,empty 18 (by simp)])
    (by simp [measured,InitialWorkspace.binaryRoles,initialBinarySelection,w.injective.eq_iff,empty 19 (by simp)])
    (by simp [measured,InitialWorkspace.binaryRoles,initialBinarySelection,w.injective.eq_iff,empty 20 (by simp)])
  have second : Executes (scaledClauses (extra+18) w.binaryRoles (Cellular.alphabet program) (initialBinaryTemplate program))
      measured emitTime emitted := by
    simpa [InitialWorkspace.binaryRoles,initialBinarySelection,measured,emitted,payload,initialBinaryBytes,w.injective.eq_iff] using emitRun
  have third := clear_executes (w 6) emitted
  have restored : Function.update emitted (w 6) []=Function.update store (w 5) payload := by
    funext r
    by_cases a : r=w 6
    · subst r; simp [w.injective.eq_iff,empty 6 (by simp)]
    · by_cases b : r=w 5 <;> simp [emitted,measured,a,b]
  rw [restored] at third
  have combined := first.sequence (second.sequence third)
  refine ⟨5*offset+5*(store (w 2)).length+5*place+8+1+(emitTime+1+((emitted (w 6)).length+1)),?_,combined⟩
  simp [InitialWorkspace.binaryRoles,initialBinarySelection,measured] at emitBound
  simp only [emitted,Function.update_of_ne (show w 6 ≠ w 5 by simp [w.injective.eq_iff]),
    measured,Function.update_self,List.length_replicate]
  unfold initialBinaryCellBound initialBinaryCoefficient
  dsimp only [base] at emitBound ⊢
  omega

theorem initialBinaryCellBound_polynomial (program : Machine.Program) {width : Nat} (setup : Setup width)
    (place : Fin (setup.capacity-1)) :
    initialBinaryCellBound program place.val setup.offset.val setup.header.length ≤
      (initialBinaryCoefficient program+17)*(width+1)^2 := by
  have fits := setup.fits
  have within := place.isLt
  have base : setup.offset.val+setup.header.length+place.val ≤ width := by omega
  have power := Nat.pow_le_pow_left (show setup.offset.val+setup.header.length+place.val+1≤width+1 by omega) 2
  have multiplied := Nat.mul_le_mul_left (initialBinaryCoefficient program) power
  unfold initialBinaryCellBound
  nlinarith

end Counting.External.CookLevin.StackGenerator
