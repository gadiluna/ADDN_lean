import Counting.ExternalMatchingEmitter
import Counting.StackRoutineBasic
import Counting.StackRoutineSemantics

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

abbrev PortWorkspace (extra : Nat) := Fin 13 ↪ Fin (extra+13)
def PortWorkspace.edge (w : PortWorkspace extra) : EdgeWorkspace (extra+1) :=
  (⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 13=>i.val) h)⟩ : Fin 12 ↪ Fin 13).trans w

def emitPort (extra : Nat) (w : PortWorkspace extra) : Routine (extra+11) :=
  sequence (emitEdge (extra+1) w.edge) (pushBit (w 2) true)

def portRows (first second start : Nat) : Nat → List (List Nat)
  | 0 => []
  | count+1 => [first,second,start]::portRows first second (start+1) count

def emitPorts (extra : Nat) (w : PortWorkspace extra) : Routine (extra+11) :=
  forEach (w 12) (emitPort extra w)

def portsResult (extra : Nat) (w : PortWorkspace extra) (store : Fin (extra+13) → List Bool) (count : Nat) :=
  Function.update (Function.update (Function.update store (w 12) [])
    (w 2) (List.replicate count true++store (w 2)))
    (w 6) ((Encoding.sequence (Encoding.list Encoding.natural)
      (portRows (store (w 0)).length (store (w 1)).length (store (w 2)).length count)).reverse++store (w 6))

theorem emitPorts_executes (extra : Nat) (w : PortWorkspace extra) (count limit : Nat)
    (store : Fin (extra+13) → List Bool)
    (counter : store (w 12)=List.replicate count true)
    (bounded : (store (w 0)).length+(store (w 1)).length+(store (w 2)).length+count ≤ limit)
    (empty : ∀ i∈([3,4,5,7,8,9,10,11] : List (Fin 13)),store (w i)=[]) :
    ∃ time ≤ count*(300*(limit+1)^2+4)+1,
      Executes (emitPorts extra w) store time (portsResult extra w store count) := by
  induction count generalizing store with
  | zero =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 12) (emitPort extra w) store counter
    have unchanged : portsResult extra w store 0=store := by
      simp only [portsResult,portRows,Encoding.sequence,List.reverse_nil,List.nil_append,List.replicate_zero]
      have counterEmpty : store (w 12)=[] := counter
      rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | succ count ih =>
    let consumed := Function.update store (w 12) (List.replicate count true)
    have consumedEmpty (i : Fin 12) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 12))) :
        consumed (w.edge i)=[] := by
      have hi : i.val<12 := i.isLt
      have mem : (⟨i.val,by omega⟩ : Fin 13)∈([3,4,5,7,8,9,10,11] : List (Fin 13)) := by
        fin_cases i <;> simp_all
      simpa [PortWorkspace.edge,consumed,w.injective.eq_iff,show i.val≠12 by omega,Fin.ext_iff] using empty _ mem
    obtain ⟨edgeTime,edgeBound,edgeRun⟩ := emitEdge_executes (extra+1) w.edge consumed consumedEmpty
    let edge := (Encoding.list Encoding.natural).encode
      [(store (w 0)).length,(store (w 1)).length,(store (w 2)).length]
    let emitted := Function.update consumed (w 6) (edge.reverse++store (w 6))
    have emittedRun : Executes (emitEdge (extra+1) w.edge) consumed edgeTime emitted := by
      simpa [PortWorkspace.edge,consumed,emitted,edge,w.injective.eq_iff] using edgeRun
    let next := Function.update emitted (w 2) (true::store (w 2))
    have body : Executes (emitPort extra w) consumed (edgeTime+2) next := by
      simpa [emitPort,next,emitted,consumed,w.injective.eq_iff] using emittedRun.sequence (pushBit_executes (w 2) true emitted)
    have nextCounter : next (w 12)=List.replicate count true := by simp [next,emitted,consumed,w.injective.eq_iff]
    have nextBound : (next (w 0)).length+(next (w 1)).length+(next (w 2)).length+count ≤ limit := by
      simpa [next,emitted,consumed,w.injective.eq_iff,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bounded
    have nextEmpty (i : Fin 13) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 13))) : next (w i)=[] := by
      have a : i≠2 := by intro eq;subst i;simp at member
      have b : i≠6 := by intro eq;subst i;simp at member
      have c : i≠12 := by intro eq;subst i;simp at member
      simpa [next,emitted,consumed,w.injective.eq_iff,a,b,c] using empty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next nextCounter nextBound nextEmpty
    obtain ⟨bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := body
    have firstRun := repeat_iteration (w 12) (emitPort extra w) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) (edgeTime+2) bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitPorts extra w).program) (edgeTime+2+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have edgeLimit : edgeTime ≤ 300*(limit+1)^2 := by
      have boundAs : edgeTime ≤ 300*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^2 := by
        simpa [PortWorkspace.edge,consumed,w.injective.eq_iff] using edgeBound
      apply boundAs.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    refine ⟨edgeTime+2+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · nlinarith only [edgeLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases c : r=w 12
      · subst r;simp [portsResult,w.injective.eq_iff]
      · by_cases p : r=w 2
        · subst r
          simp [portsResult,next,emitted,consumed,w.injective.eq_iff,List.replicate_succ,←List.append_assoc]
          calc
            _ = (List.replicate count true++[true])++store (w 2) := by simp [List.append_assoc]
            _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
        · by_cases o : r=w 6
          · subst r
            simp [portsResult,next,emitted,consumed,w.injective.eq_iff,portRows,Encoding.sequence,edge,
              List.reverse_append,List.append_assoc]
          · simp [portsResult,next,emitted,consumed,c,p,o]

end Counting.External.MatchingMachine
