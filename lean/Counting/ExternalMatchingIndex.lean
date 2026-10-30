import Counting.StackEncodingBoundedNatural
import Counting.StackRoutineLists

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

abbrev IndexWorkspace (extra : Nat) := Fin 13 ↪ Fin (extra+13)
def indexCountPositions : Fin 11 ↪ Fin 13 := ⟨![0,2,5,6,7,8,4,9,10,11,3],by decide⟩
def IndexWorkspace.countRoles (w : IndexWorkspace extra) : CountWorkspace (extra+2) := indexCountPositions.trans w

def readIndex (extra : Nat) (w : IndexWorkspace extra) : Routine (extra+11) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+10) (w 1) (w 3) (w 5)))
    (sequence (boundedCount (extra+2) w.countRoles) (clear (w 4)))

theorem readIndex_executes (extra : Nat) (w : IndexWorkspace extra) (store : Fin (extra+13) → List Bool)
    (index : Nat) (header : store (w 0)=Encoding.natural.encode index)
    (fits : index ≤ (store (w 1)).length)
    (empty : ∀ i∈([2,3,4,5,6,7,8,9,10,11] : List (Fin 13)),store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+(store (w 1)).length+1)^3,
      Executes (readIndex extra w) store time (Function.update store (w 2) (List.replicate index true)) := by
  let copied := Function.update store (w 3) (store (w 1))
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+10) (w 1) (w 3) (w 5))) store
      (5*(store (w 1)).length+2) copied := by
    simpa +instances only [copied,empty 3 (by decide),List.append_nil,ListPrograms.copyProgram] using
      copy_executes (extra+10) (w 1) (w 3) (w 5) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 5 (by decide))
  have work (i : Fin 11) (member : i∈({2,3,4,5,7,8,9}:Finset (Fin 11))) : copied (w.countRoles i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [IndexWorkspace.countRoles,indexCountPositions,copied,w.injective.eq_iff,empty]
  obtain ⟨countTime,countBound,countRun⟩ := boundedNatural_executes (extra+2) w.countRoles copied index
    (by simpa [IndexWorkspace.countRoles,indexCountPositions,copied,w.injective.eq_iff] using header)
    (by simp [IndexWorkspace.countRoles,indexCountPositions,copied,w.injective.eq_iff,empty 2 (by decide)]) work
  let counted := Function.update (Function.update store (w 2) (List.replicate index true)) (w 4) [true]
  have countedEq : boundedNaturalResult (extra+2) w.countRoles copied index=counted := by
    funext r
    by_cases e3 : r=w 3
    · subst r;simp [boundedNaturalResult,IndexWorkspace.countRoles,indexCountPositions,counted,w.injective.eq_iff,empty 3 (by decide)]
    · simp [boundedNaturalResult,IndexWorkspace.countRoles,indexCountPositions,copied,counted,w.injective.eq_iff,
        e3,Function.update_apply,fits,empty 4 (by decide)]
  rw [countedEq] at countRun
  have clearRun := clear_executes (w 4) counted
  have current : counted (w 4)=[true] := by simp [counted]
  rw [current,List.length_singleton] at clearRun
  have final : Function.update counted (w 4) []=Function.update store (w 2) (List.replicate index true) := by
    funext r
    by_cases e4 : r=w 4
    · subst r;simp [w.injective.eq_iff,empty 4 (by decide)]
    · simp [counted,e4]
  rw [final] at clearRun
  have composed := copy.sequence (countRun.sequence clearRun)
  refine ⟨5*(store (w 1)).length+2+1+(countTime+1+2),?_,composed⟩
  have bound : countTime ≤ 64*((store (w 0)).length+(store (w 1)).length+1)^3 := by
    simpa [IndexWorkspace.countRoles,indexCountPositions,copied,←header,Nat.add_comm] using countBound
  have linear : (store (w 0)).length+(store (w 1)).length+1 ≤
      ((store (w 0)).length+(store (w 1)).length+1)^3 := Nat.le_self_pow (by decide) _
  omega

end Counting.External.MatchingMachine
