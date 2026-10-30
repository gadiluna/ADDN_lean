import Counting.ExternalCNFFresh

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Current identifier, width, iteration counter, temporary terminal index,
three encoded literals, copy scratch, and three emitter scratch registers. -/
abbrev PrepareWorkspace (extra : Nat) := Fin 11 ↪ Fin (extra+11)

def preparePositions (which : Fin 3) : Fin 5 ↪ Fin 11 :=
  ⟨![![0,4,8,9,10],![3,5,8,9,10],![3,6,8,9,10]] which,by
    intro i j equal;fin_cases which <;> fin_cases i <;> fin_cases j <;> simp_all⟩
def prepareRoles (extra : Nat) (w : PrepareWorkspace extra) (which : Fin 3) : PowerWorkspace (extra+6) :=
  (preparePositions which).trans w

def prepareClause (extra : Nat) (w : PrepareWorkspace extra) : Routine (extra+9) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+8) (w 1) (w 2) (w 7)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+8) (w 0) (w 3) (w 7)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+8) (w 1) (w 3) (w 7)))
        (sequence (emitLiteral (extra+6) (prepareRoles extra w 0) true)
          (sequence (emitLiteral (extra+6) (prepareRoles extra w 1) true)
            (sequence (emitLiteral (extra+6) (prepareRoles extra w 2) false) (clear (w 3)))))))

def prepareResult (extra : Nat) (w : PrepareWorkspace extra) (store : Fin (extra+11) → List Bool) :=
  let codec := Encoding.product Encoding.natural Encoding.boolean
  let current := (store (w 0)).length
  let terminal := current+(store (w 1)).length
  Function.update (Function.update (Function.update (Function.update store (w 2) (store (w 1)))
    (w 4) (codec.encode (current,true))) (w 5) (codec.encode (terminal,true)))
    (w 6) (codec.encode (terminal,false))

theorem prepareClause_executes (extra : Nat) (w : PrepareWorkspace extra) (store : Fin (extra+11) → List Bool)
    (empty : ∀ i∈([2,3,4,5,6,7,8,9,10] : List (Fin 11)),store (w i)=[]) :
    ∃ time ≤ 150*((store (w 0)).length+(store (w 1)).length+2)^2,
      Executes (prepareClause extra w) store time (prepareResult extra w store) := by
  let codec := Encoding.product Encoding.natural Encoding.boolean
  let current := (store (w 0)).length
  let width := (store (w 1)).length
  let s1 := Function.update store (w 2) (store (w 1))
  have ne (i j : Fin 11) (h : i≠j) : w i≠w j := fun equal => h (w.injective equal)
  have copy1 := copy_executes (extra+8) (w 1) (w 2) (w 7) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) store (empty _ (by decide))
  rw [empty 2 (by decide),List.append_nil] at copy1
  have copy2 := copy_executes (extra+8) (w 0) (w 3) (w 7) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) s1
    (by simp [s1,w.injective.eq_iff,empty 7 (by decide)])
  let s2 := Function.update s1 (w 3) (store (w 0))
  have copy2as : Executes (ofProgram (ListPrograms.copyProgram (extra+8) (w 0) (w 3) (w 7))) s1 (5*current+2) s2 := by simpa [s2,s1,w.injective.eq_iff,empty 3 (by decide),current] using copy2
  have copy3 := copy_executes (extra+8) (w 1) (w 3) (w 7) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) s2
    (by simp [s2,s1,w.injective.eq_iff,empty 7 (by decide)])
  let s3 := Function.update s2 (w 3) (store (w 1)++store (w 0))
  have copy3as : Executes (ofProgram (ListPrograms.copyProgram (extra+8) (w 1) (w 3) (w 7))) s2 (5*width+2) s3 := by simpa [s3,s2,s1,w.injective.eq_iff,width] using copy3
  obtain ⟨t0,b0,r0⟩ := emitLiteral_executes (extra+6) (prepareRoles extra w 0) true s3
    (by simp [prepareRoles,preparePositions,s3,s2,s1,w.injective.eq_iff,empty 8 (by decide)])
    (by simp [prepareRoles,preparePositions,s3,s2,s1,w.injective.eq_iff,empty 9 (by decide)])
    (by simp [prepareRoles,preparePositions,s3,s2,s1,w.injective.eq_iff,empty 10 (by decide)])
  let s4 := Function.update s3 (w 4) (codec.encode (current,true))
  have r0as : Executes (emitLiteral (extra+6) (prepareRoles extra w 0) true) s3 t0 s4 := by
    simpa [prepareRoles,preparePositions,s4,s3,s2,s1,w.injective.eq_iff,empty 4 (by decide),codec,current] using r0
  obtain ⟨t1,b1,r1⟩ := emitLiteral_executes (extra+6) (prepareRoles extra w 1) true s4
    (by simp [prepareRoles,preparePositions,s4,s3,s2,s1,w.injective.eq_iff,empty 8 (by decide)])
    (by simp [prepareRoles,preparePositions,s4,s3,s2,s1,w.injective.eq_iff,empty 9 (by decide)])
    (by simp [prepareRoles,preparePositions,s4,s3,s2,s1,w.injective.eq_iff,empty 10 (by decide)])
  let s5 := Function.update s4 (w 5) (codec.encode (current+width,true))
  have r1as : Executes (emitLiteral (extra+6) (prepareRoles extra w 1) true) s4 t1 s5 := by
    simpa [prepareRoles,preparePositions,s5,s4,s3,s2,s1,w.injective.eq_iff,empty 5 (by decide),codec,current,width,Nat.add_comm] using r1
  obtain ⟨t2,b2,r2⟩ := emitLiteral_executes (extra+6) (prepareRoles extra w 2) false s5
    (by simp [prepareRoles,preparePositions,s5,s4,s3,s2,s1,w.injective.eq_iff,empty 8 (by decide)])
    (by simp [prepareRoles,preparePositions,s5,s4,s3,s2,s1,w.injective.eq_iff,empty 9 (by decide)])
    (by simp [prepareRoles,preparePositions,s5,s4,s3,s2,s1,w.injective.eq_iff,empty 10 (by decide)])
  let s6 := Function.update s5 (w 6) (codec.encode (current+width,false))
  have r2as : Executes (emitLiteral (extra+6) (prepareRoles extra w 2) false) s5 t2 s6 := by
    simpa [prepareRoles,preparePositions,s6,s5,s4,s3,s2,s1,w.injective.eq_iff,empty 6 (by decide),codec,current,width,Nat.add_comm] using r2
  have clearing := clear_executes (w 3) s6
  have finalStore : Function.update s6 (w 3) []=prepareResult extra w store := by
    funext r
    by_cases a : r=w 3
    · subst r;simp [prepareResult,w.injective.eq_iff,empty 3 (by decide)]
    · simp [s6,s5,s4,s3,s2,s1,prepareResult,Function.update_apply,a,codec,current,width]
  rw [finalStore] at clearing
  have clearTime : (s6 (w 3)).length+1=current+width+1 := by simp [s6,s5,s4,s3,s2,s1,w.injective.eq_iff,current,width,Nat.add_comm]
  rw [clearTime] at clearing
  have combined := copy1.sequence (copy2as.sequence (copy3as.sequence (r0as.sequence (r1as.sequence (r2as.sequence clearing)))))
  refine ⟨5*width+2+1+(5*current+2+1+(5*width+2+1+(t0+1+(t1+1+(t2+1+(current+width+1)))))),?_,combined⟩
  have bound0 : t0≤22*(current+1)^2 := by simpa [prepareRoles,preparePositions,s3,s2,s1,w.injective.eq_iff,current] using b0
  have bound1 : t1≤22*(current+width+1)^2 := by simpa [prepareRoles,preparePositions,s4,s3,s2,s1,w.injective.eq_iff,current,width,Nat.add_comm] using b1
  have bound2 : t2≤22*(current+width+1)^2 := by simpa [prepareRoles,preparePositions,s5,s4,s3,s2,s1,w.injective.eq_iff,current,width,Nat.add_comm] using b2
  change _≤150*(current+width+2)^2
  have squares := Nat.pow_le_pow_left (by omega : current+1≤current+width+1) 2
  nlinarith only [bound0,bound1,bound2,squares]

end Counting.External.CNFMachine
