import Counting.HardnessNetworkMachineRepeat
import Counting.StackRepeatBit

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev SerializeWorkspace (extra : Nat) := Fin 9 ↪ Fin (extra+9)
def markerHeaderPositions : Fin 6 ↪ Fin 9 := ⟨![0,4,8,5,7,6],by decide⟩
def SerializeWorkspace.markers (w : SerializeWorkspace extra) : External.CoverNormalization.EmitWorkspace (extra+3) :=
  markerHeaderPositions.trans w

def emitLeaderMarkers (extra : Nat) (w : SerializeWorkspace extra) : Routine (extra+7) :=
  sequence (External.CoverNormalization.emitReversedNatural (extra+3) w.markers)
    (sequence (prepend (w 4) [true])
      (sequence (ofProgram (ListPrograms.copyProgram (extra+6) (w 0) (w 5) (w 6)))
        (sequence (discardBit (w 5)) (repeatBit (w 5) (w 4) false))))

theorem emitLeaderMarkers_executes (extra : Nat) (w : SerializeWorkspace extra)
    (store : Fin (extra+9) → List Bool) (positive : 0<(store (w 0)).length)
    (empty : ∀ i∈([5,6,7,8] : List (Fin 9)),store (w i)=[]) :
    ∃ time ≤ 40*((store (w 0)).length+1)^2,
      Executes (emitLeaderMarkers extra w) store time
        (Function.update store (w 4)
          (((Encoding.list Encoding.boolean).encode (true::List.replicate ((store (w 0)).length-1) false)).reverse++store (w 4))) := by
  let N:=(store (w 0)).length
  obtain ⟨headerTime,headerBound,headerRun⟩:=External.CoverNormalization.emitReversedNatural_executes (extra+3) w.markers store
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl
        all_goals simp [SerializeWorkspace.markers,markerHeaderPositions,empty])
  let header:=Function.update store (w 4) ((Encoding.natural.encode N).reverse++store (w 4))
  have headerAs : Executes (External.CoverNormalization.emitReversedNatural (extra+3) w.markers) store headerTime header := headerRun
  have first:=prepend_executes (w 4) [true] header
  let firsted:=Function.update store (w 4) (true::((Encoding.natural.encode N).reverse++store (w 4)))
  have firstAs : Executes (prepend (w 4) [true]) header 2 firsted := by simpa [header,firsted] using first
  have copying:=copy_executes (extra+6) (w 0) (w 5) (w 6)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) firsted
    (by simp [firsted,w.injective.eq_iff,empty])
  have source : firsted (w 0)=store (w 0) := by simp [firsted,w.injective.eq_iff]
  have vacant : firsted (w 5)=[] := by simp [firsted,w.injective.eq_iff,empty]
  rw [source,vacant,List.append_nil] at copying
  let copied:=Function.update firsted (w 5) (store (w 0))
  have dropping:=discardBit_executes (w 5) copied
  let ready:=Function.update firsted (w 5) (store (w 0)).tail
  have dropAs : Executes (discardBit (w 5)) copied 1 ready := by simpa [copied,ready] using dropping
  have repeating:=repeatBit_executes (w 5) (w 4) false (by simp [w.injective.eq_iff]) ready
  have count : (ready (w 5)).length=N-1 := by simp [ready,N]
  rw [count] at repeating
  have final : Function.update (Function.update ready (w 5) []) (w 4)
      (List.replicate (N-1) false++ready (w 4))=
      Function.update store (w 4)
        (((Encoding.list Encoding.boolean).encode (true::List.replicate (N-1) false)).reverse++store (w 4)) := by
    have rowLength : (true::List.replicate (N-1) false).length=N := by simp;omega
    have sequence (bits : List Bool) : Encoding.sequence Encoding.boolean bits=bits := by
      induction bits with
      | nil=>rfl
      | cons bit bits ih=>simp only [Encoding.sequence,ih];rfl
    change _=Function.update store (w 4)
      ((Encoding.natural.encode (true::List.replicate (N-1) false).length++
        Encoding.sequence Encoding.boolean (true::List.replicate (N-1) false)).reverse++store (w 4))
    rw [rowLength,sequence]
    funext r
    by_cases e5 : r=w 5
    · subst r;simp [w.injective.eq_iff,empty]
    · by_cases e4 : r=w 4
      · subst r;simp [ready,firsted,w.injective.eq_iff,List.reverse_append,List.append_assoc]
      · simp [ready,firsted,e5,e4]
  rw [final] at repeating
  have combined:=headerAs.sequence (firstAs.sequence (copying.sequence (dropAs.sequence repeating)))
  refine ⟨_,?_,combined⟩
  change headerTime ≤ 30*(N+1)^2 at headerBound
  change headerTime+1+(2+1+(5*N+2+1+(1+1+(3*(N-1)+1)))) ≤ 40*(N+1)^2
  have small : N-1 ≤ N := by omega
  nlinarith only [headerBound,small,Nat.zero_le N]

end Counting.HardnessNetworkMachine
