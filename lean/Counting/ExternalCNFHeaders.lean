import Counting.StackEmitSyntax

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Explicit variable and clause counts, output, and three empty scratch registers. -/
abbrev HeaderWorkspace (extra : Nat) := Fin 6 ↪ Fin (extra+6)
def headerEmitPositions (which : Bool) : Fin 5 ↪ Fin 6 :=
  ⟨if which then ![0,2,3,4,5] else ![1,2,3,4,5],by
    intro i j equal;cases which <;> fin_cases i <;> fin_cases j <;> simp_all⟩
def headerEmitRoles (extra : Nat) (w : HeaderWorkspace extra) (which : Bool) : PowerWorkspace (extra+1) :=
  (headerEmitPositions which).trans w

def formulaHeaders (extra : Nat) (w : HeaderWorkspace extra) : Routine (extra+4) :=
  sequence (emitNatural (extra+1) (headerEmitRoles extra w false))
    (emitVariableTable (extra+1) (headerEmitRoles extra w true))

theorem formulaHeaders_executes (extra : Nat) (w : HeaderWorkspace extra) (variableCount clauses : Nat)
    (store : Fin (extra+6) → List Bool) (universeEq : store (w 0)=List.replicate variableCount true)
    (count : (store (w 1)).length=clauses) (e3 : store (w 3)=[]) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    ∃ time ≤ 20*(clauses+1)^2+1+28*(variableCount+1)^2,
      Executes (formulaHeaders extra w) store time
        (Function.update store (w 2) ((Encoding.list Encoding.boolean).encode (List.replicate variableCount true)++
          Encoding.natural.encode clauses++store (w 2))) := by
  obtain ⟨t0,b0,r0⟩ := emitNatural_executes (extra+1) (headerEmitRoles extra w false) store e3 e4 e5
  change t0≤20*((store (w 1)).length+1)^2 at b0
  rw [count] at b0
  let next := Function.update store (w 2) (Encoding.natural.encode clauses++store (w 2))
  have r0as : Executes (emitNatural (extra+1) (headerEmitRoles extra w false)) store t0 next := by
    simpa [headerEmitRoles,headerEmitPositions,count,next] using r0
  obtain ⟨t1,b1,r1⟩ := emitVariableTable_executes (extra+1) (headerEmitRoles extra w true) variableCount next
    (by simp [headerEmitRoles,headerEmitPositions,next,w.injective.eq_iff,universeEq])
    (by simp [headerEmitRoles,headerEmitPositions,next,w.injective.eq_iff,e3])
    (by simp [headerEmitRoles,headerEmitPositions,next,w.injective.eq_iff,e4])
    (by simp [headerEmitRoles,headerEmitPositions,next,w.injective.eq_iff,e5])
  have combined := r0as.sequence r1
  refine ⟨t0+1+t1,by omega,?_⟩
  simpa [formulaHeaders,headerEmitRoles,headerEmitPositions,next,List.append_assoc] using combined

end Counting.External.CNFMachine
