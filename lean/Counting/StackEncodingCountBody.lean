import Counting.StackEncodingBoundedCountSpec
import Counting.StackEmitNatural
import Counting.StackComparePreserving

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

abbrev CountWorkspace (extra : Nat) := Fin 11 ↪ Fin (extra+11)

def countEmitRoles (extra : Nat) (w : CountWorkspace extra) : Routine.PowerWorkspace (extra+6) :=
  ⟨fun i => w (![1,2,3,4,5] i),by intro a b same; exact (by decide : Function.Injective (![(1:Fin 11),2,3,4,5])) (w.injective same)⟩

def countCompareRoles (extra : Nat) (w : CountWorkspace extra) : Fin 6 ↪ Fin (extra+11) :=
  ⟨fun i => w (![0,2,6,7,8,9] i),by intro a b same; exact (by decide : Function.Injective (![(0:Fin 11),2,6,7,8,9])) (w.injective same)⟩

/-- Roles: framed binary target, capped unary accumulator, generated frame,
three emitter temporaries, condition, three comparison temporaries, budget.
Only the unary accumulator may change; every work register is restored. -/
def countBody (extra : Nat) (w : CountWorkspace extra) : Routine (extra+9) :=
  Routine.sequence (Routine.emitNatural (extra+6) (countEmitRoles extra w))
    (Routine.sequence (Compare.preservingEquality (extra+5) (countCompareRoles extra w))
      (Routine.sequence (Routine.clear (w 2))
        (branchRoutine (w 6) (Routine.skip (extra+9)) (Routine.pushBit (w 1) true))))

def countBodyResult (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11) → List Bool) : Fin (extra+11) → List Bool :=
  if Encoding.natural.encode (store (w 1)).length = store (w 0) then store
  else Function.update store (w 1) (true::store (w 1))

/-- The binary number is compared with a counter grown by at most one.
Generating its binary encoding is paid for by the existing emitter proof. -/
theorem countBody_executes (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11) → List Bool)
    (empty : ∀ i : Fin 11, i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → store (w i)=[]) :
    ∃ time ≤ 60*((store (w 1)).length+(store (w 0)).length+1)^2,
      Routine.Executes (countBody extra w) store time (countBodyResult extra w store) := by
  let code := Encoding.natural.encode (store (w 1)).length
  let emitted := Function.update store (w 2) code
  have emit2 : store (w 2)=[] := empty 2 (by decide)
  have emit3 : store (w 3)=[] := empty 3 (by decide)
  have emit4 : store (w 4)=[] := empty 4 (by decide)
  have emit5 : store (w 5)=[] := empty 5 (by decide)
  obtain ⟨emitTime,emitBound,emitRun⟩ := Routine.emitNatural_executes (extra+6) (countEmitRoles extra w) store
    emit3 emit4 emit5
  have emit : Routine.Executes (Routine.emitNatural (extra+6) (countEmitRoles extra w)) store emitTime emitted := by
    simpa only [countEmitRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,Matrix.cons_val_one,
      emit2,List.append_nil] using emitRun
  have emittedAt (i : Fin 11) (neq : i≠2) : emitted (w i)=store (w i) := by
    simp only [emitted,Function.update_of_ne (fun same => neq (w.injective same))]
  have comparison := Compare.preservingEquality_executes (extra+5) (countCompareRoles extra w) emitted
    (by simpa [countCompareRoles] using (emittedAt 7 (by decide)).trans (empty 7 (by decide)))
    (by simpa [countCompareRoles] using (emittedAt 8 (by decide)).trans (empty 8 (by decide)))
    (by simpa [countCompareRoles] using (emittedAt 9 (by decide)).trans (empty 9 (by decide)))
  let checked := Function.update emitted (w 6) (decide (store (w 0)=code)::store (w 6))
  have compare : Routine.Executes (Compare.preservingEquality (extra+5) (countCompareRoles extra w)) emitted
      (Compare.preservingCost (store (w 0)) code) checked := by
    simpa [countCompareRoles,emitted,checked,w.injective.eq_iff] using comparison
  have checkedCode : checked (w 2)=code := by simp [checked,emitted,w.injective.eq_iff]
  have cleared : Function.update checked (w 2) [] =
      Function.update store (w 6) (decide (store (w 0)=code)::store (w 6)) := by
    funext r
    by_cases a : r=w 2
    · subst r; simp [w.injective.eq_iff,emit2]
    · by_cases b : r=w 6
      · subst r; simp [checked,w.injective.eq_iff]
      · simp [checked,emitted,a,b]
  have clear := Routine.clear_executes (w 2) checked
  rw [checkedCode,cleared] at clear
  let ready := Function.update store (w 6) (decide (store (w 0)=code)::store (w 6))
  have consumed : Function.update ready (w 6) (store (w 6)) = store := by
    simp only [ready,Function.update_idem,Function.update_eq_self]
  have branch : ∃ branchTime≤2,
      Routine.Executes (branchRoutine (w 6) (Routine.skip (extra+9)) (Routine.pushBit (w 1) true))
        ready branchTime (countBodyResult extra w store) := by
    by_cases equal : store (w 0)=code
    · have condition : ready (w 6)=true::store (w 6) := by simp [ready,equal]
      have skip : Routine.Executes (Routine.skip (extra+9))
          (Function.update ready (w 6) (store (w 6))) 0 store := by
        rw [consumed]; exact Routine.skip_executes store
      refine ⟨1,by decide,?_⟩
      have run := branch_executes_true (w 6) (Routine.skip (extra+9)) (Routine.pushBit (w 1) true)
        ready store (store (w 6)) 0 condition skip
      unfold countBodyResult
      rw [if_pos (show Encoding.natural.encode (store (w 1)).length=store (w 0) from equal.symm)]
      exact run
    · have condition : ready (w 6)=false::store (w 6) := by simp [ready,equal]
      have push : Routine.Executes (Routine.pushBit (w 1) true)
          (Function.update ready (w 6) (store (w 6))) 1
          (Function.update store (w 1) (true::store (w 1))) := by
        rw [consumed]; exact Routine.pushBit_executes (w 1) true store
      refine ⟨2,by decide,?_⟩
      have run := branch_executes_false (w 6) (Routine.skip (extra+9)) (Routine.pushBit (w 1) true)
        ready _ (store (w 6)) 1 condition push
      unfold countBodyResult
      rw [if_neg (show Encoding.natural.encode (store (w 1)).length≠store (w 0) from Ne.symm equal)]
      exact run
  obtain ⟨branchTime,branchBound,branchRun⟩:=branch
  have combined := emit.sequence (compare.sequence (clear.sequence branchRun))
  refine ⟨emitTime+1+(Compare.preservingCost (store (w 0)) code+1+(code.length+1+1+branchTime)),?_,combined⟩
  have compareBound := Compare.preservingCost_le (store (w 0)) code
  have sizeBound : (store (w 1)).length.size ≤ (store (w 1)).length := Nat.size_le.mpr Nat.lt_two_pow_self
  have codeLength : code.length=2*(store (w 1)).length.size+1 := Encoding.natural_length _
  simp only [countEmitRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero] at emitBound
  nlinarith [sq_nonneg ((store (w 0)).length : Int)]

end Counting.StackMachine.EncodingPrograms
