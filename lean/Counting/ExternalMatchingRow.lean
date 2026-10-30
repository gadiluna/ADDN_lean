import Counting.ExternalMatchingPortLoop
import Counting.StackRoutineLists

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev RowWorkspace (extra : Nat) := Fin 15 ↪ Fin (extra+15)
def RowWorkspace.port (w : RowWorkspace extra) : PortWorkspace (extra+2) :=
  (⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 15=>i.val) h)⟩ : Fin 13 ↪ Fin 15).trans w

def emitRow (extra : Nat) (w : RowWorkspace extra) : Routine (extra+13) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+12) (w 13) (w 12) (w 9)))
    (sequence (emitPorts (extra+2) w.port)
      (sequence (clear (w 2)) (sequence (pushBit (w 0) true) (pushBit (w 1) true))))

def rowResult (extra : Nat) (w : RowWorkspace extra) (store : Fin (extra+15) → List Bool) :=
  Function.update (Function.update (Function.update store (w 0) (true::store (w 0)))
    (w 1) (true::store (w 1))) (w 6)
    ((Encoding.sequence (Encoding.list Encoding.natural)
      (portRows (store (w 0)).length (store (w 1)).length 0 (store (w 13)).length)).reverse++store (w 6))

def rowCost (a b q : Nat) := q*(300*(a+b+q+1)^2+4)+6*q+10

theorem emitRow_executes (extra : Nat) (w : RowWorkspace extra) (store : Fin (extra+15) → List Bool)
    (unary : store (w 13)=List.replicate (store (w 13)).length true)
    (empty : ∀ i∈([2,3,4,5,7,8,9,10,11,12] : List (Fin 15)),store (w i)=[]) :
    ∃ time ≤ rowCost (store (w 0)).length (store (w 1)).length (store (w 13)).length,
      Executes (emitRow extra w) store time (rowResult extra w store) := by
  let q := (store (w 13)).length
  let copied := Function.update store (w 12) (List.replicate q true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+12) (w 13) (w 12) (w 9))) store (5*q+2) copied := by
    simpa +instances only [copied,q,←unary,empty 12 (by decide),List.append_nil,ListPrograms.copyProgram] using
      copy_executes (extra+12) (w 13) (w 12) (w 9) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 9 (by decide))
  have portEmpty (i : Fin 13) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 13))) : copied (w.port i)=[] := by
    have different : i.val≠12 := by fin_cases i <;> simp_all
    have mem : (⟨i.val,by omega⟩ : Fin 15)∈([2,3,4,5,7,8,9,10,11,12] : List (Fin 15)) := by
      fin_cases i <;> simp_all
    simpa [RowWorkspace.port,copied,w.injective.eq_iff,Fin.ext_iff,different] using empty _ mem
  obtain ⟨loopTime,loopBound,loopRun⟩ := emitPorts_executes (extra+2) w.port q
    ((store (w 0)).length+(store (w 1)).length+q) copied
    (by simp [RowWorkspace.port,copied])
    (by simp [RowWorkspace.port,copied,w.injective.eq_iff,empty 2 (by decide)]) portEmpty
  let stream := (Encoding.sequence (Encoding.list Encoding.natural)
    (portRows (store (w 0)).length (store (w 1)).length 0 q)).reverse++store (w 6)
  let filled := Function.update (Function.update store (w 2) (List.replicate q true)) (w 6) stream
  have loopAs : Executes (emitPorts (extra+2) w.port) copied loopTime filled := by
    have result : portsResult (extra+2) w.port copied q=filled := by
      funext r
      by_cases e6 : r=w 6
      · subst r;simp [portsResult,RowWorkspace.port,copied,filled,stream,w.injective.eq_iff,empty 2 (by decide)]
      · by_cases e2 : r=w 2
        · subst r;simp [portsResult,RowWorkspace.port,copied,filled,w.injective.eq_iff,empty 2 (by decide)]
        · by_cases e12 : r=w 12
          · subst r;simp [portsResult,RowWorkspace.port,filled,w.injective.eq_iff,empty 12 (by decide)]
          · simp [portsResult,RowWorkspace.port,copied,filled,e6,e2,e12]
    simpa only [result] using loopRun
  let cleaned := Function.update store (w 6) stream
  have clearRun : Executes (clear (w 2)) filled (q+1) cleaned := by
    have clean := clear_executes (w 2) filled
    have result : Function.update filled (w 2) []=cleaned := by
      funext r
      by_cases e2 : r=w 2
      · subst r;simp [filled,cleaned,w.injective.eq_iff,empty 2 (by decide)]
      · simp [filled,cleaned,e2,Function.update_apply]
    simpa only [filled,Function.update_of_ne (w.injective.ne (by decide : (2:Fin 15)≠6)),
      Function.update_self,List.length_replicate,result] using clean
  have increment0 := pushBit_executes (w 0) true cleaned
  have increment1 := pushBit_executes (w 1) true (Function.update cleaned (w 0) (true::cleaned (w 0)))
  have combined := copy.sequence (loopAs.sequence (clearRun.sequence (increment0.sequence increment1)))
  refine ⟨5*q+2+1+(loopTime+1+(q+1+1+(1+1+1))),?_,?_⟩
  · change _ ≤ rowCost (store (w 0)).length (store (w 1)).length q
    unfold rowCost
    omega
  · have result : Function.update (Function.update cleaned (w 0) (true::cleaned (w 0))) (w 1)
        (true::(Function.update cleaned (w 0) (true::cleaned (w 0))) (w 1))=rowResult extra w store := by
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [rowResult,cleaned,w.injective.eq_iff]
      · by_cases e1 : r=w 1
        · subst r;simp [rowResult,cleaned,w.injective.eq_iff]
        · simp [rowResult,cleaned,stream,q,e0,e1,Function.update_apply]
    rw [result] at combined
    exact combined

theorem rowCost_le (a b q : Nat) : rowCost a b q ≤ 320*(a+b+q+1)^3 := by
  let S := a+b+q+1
  have qS : q ≤ S := by dsimp [S];omega
  have lower : S ≤ S^3 := Nat.le_self_pow (by decide) S
  have positive : 1 ≤ S^3 := Nat.one_le_pow _ _ (by dsimp [S];omega)
  have product : q*S^2 ≤ S^3 := by calc
    q*S^2 ≤ S*S^2 := Nat.mul_le_mul_right _ qS
    _ = S^3 := by ring
  have expanded : rowCost a b q=300*(q*S^2)+10*q+10 := by unfold rowCost;dsimp [S];ring
  rw [expanded]
  change _ ≤ 320*S^3
  omega

end Counting.External.MatchingMachine
