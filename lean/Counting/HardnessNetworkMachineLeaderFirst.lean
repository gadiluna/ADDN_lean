import Counting.HardnessNetworkMachineLeaderLoop

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def emitLeaderFirst (extra : Nat) (w : LeaderWorkspace extra) : Routine (extra+38) :=
  sequence (pushBit (w 33) true)
    (sequence (emitLeaderBlock extra w) (discardBit (w 33)))

theorem emitLeaderFirst_executes (extra : Nat) (w : LeaderWorkspace extra)
    (store : Fin (extra+40) → List Bool) (value : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode value++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈leaderBlockScratch,store (w i)=[]) :
    ∃ time ≤ leaderBlockCost (store (w 0)).length ((store (w 33)).length+1)+4,
      Executes (emitLeaderFirst extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 35)
          ((Encoding.sequence Encoding.natural (List.replicate ((store (w 33)).length+1) value)).reverse++store (w 35))) := by
  have pushing:=pushBit_executes (w 33) true store
  let enlarged:=Function.update store (w 33) (true::store (w 33))
  have blockEmpty (i : Fin 40) (member : i∈leaderBlockScratch) : enlarged (w i)=[] := by
    have different : i≠33 := by intro eq;subst i;simp [leaderBlockScratch] at member
    simpa [enlarged,w.injective.eq_iff,different] using empty i member
  obtain ⟨blockTime,blockBound,blockRun⟩:=emitLeaderBlock_executes extra w enlarged value accepted suffix tail
    (by simp [enlarged,w.injective.eq_iff,source]) (by simp [enlarged,w.injective.eq_iff,status]) blockEmpty
  let result:=Function.update (Function.update enlarged (w 0) suffix) (w 35)
    ((Encoding.sequence Encoding.natural (List.replicate ((store (w 33)).length+1) value)).reverse++store (w 35))
  have blockAs : Executes (emitLeaderBlock extra w) enlarged blockTime result := by
    simpa [enlarged,w.injective.eq_iff,result] using blockRun
  have skipping:=discardBit_executes (w 33) result
  have final : Function.update result (w 33) (result (w 33)).tail=
      Function.update (Function.update store (w 0) suffix) (w 35)
        ((Encoding.sequence Encoding.natural (List.replicate ((store (w 33)).length+1) value)).reverse++store (w 35)) := by
    funext r
    by_cases e33 : r=w 33
    · subst r;simp [result,enlarged,w.injective.eq_iff]
    · simp [result,enlarged,Function.update_apply,e33,w.injective.eq_iff]
  rw [final] at skipping
  refine ⟨1+1+(blockTime+1+1),?_,pushing.sequence (blockAs.sequence skipping)⟩
  have bounded : blockTime ≤ leaderBlockCost (store (w 0)).length ((store (w 33)).length+1) := by
    simpa [enlarged,w.injective.eq_iff] using blockBound
  omega

end Counting.HardnessNetworkMachine
