import Counting.HardnessNetworkMachineMarkers
import Counting.HardnessNetworkMachineStar
import Counting.HardnessNetworkMachineEncodingSpec

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def roundHeaderPositions : Fin 6 ↪ Fin 9 := ⟨![1,4,8,5,7,6],by decide⟩
def SerializeWorkspace.rounds (w : SerializeWorkspace extra) : External.CoverNormalization.EmitWorkspace (extra+3) :=
  roundHeaderPositions.trans w

def emitNetworkSerialization (extra : Nat) (w : SerializeWorkspace extra) : Routine (extra+7) :=
  sequence (emitLeaderMarkers extra w)
    (sequence (External.CoverNormalization.emitReversedNatural (extra+3) w.rounds)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+6) (w 1) (w 5) (w 6)))
        (sequence (discardBit (w 5))
          (sequence (repeatedCopy (extra+6) (w 2) (w 5) (w 4) (w 6))
            (ofProgram (ListPrograms.copyProgram (extra+6) (w 3) (w 4) (w 6)))))))

def serializationCost (width base pathLength starLength : Nat) :=
  40*(width+1)^2+30*(base+1)^2+5*base+(5*pathLength+4)*(base-1)+5*starLength+20

theorem emitNetworkSerialization_executes (extra : Nat) (w : SerializeWorkspace extra)
    (store : Fin (extra+9) → List Bool) (path star : List (List Nat))
    (widthPositive : 0<(store (w 0)).length) (basePositive : 0<(store (w 1)).length)
    (pathCode : store (w 2)=((Encoding.list (Encoding.list Encoding.natural)).encode path).reverse)
    (starCode : store (w 3)=((Encoding.list (Encoding.list Encoding.natural)).encode star).reverse)
    (empty : ∀ i∈([5,6,7,8] : List (Fin 9)),store (w i)=[]) :
    ∃ time ≤ serializationCost (store (w 0)).length (store (w 1)).length
      (store (w 2)).length (store (w 3)).length,
      Executes (emitNetworkSerialization extra w) store time
        (Function.update store (w 4)
          (((Encoding.list Encoding.boolean).encode (true::List.replicate ((store (w 0)).length-1) false)++
            (Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode
              (List.replicate ((store (w 1)).length-1) path++[star])).reverse++store (w 4))) := by
  let N:=(store (w 0)).length
  let B:=(store (w 1)).length
  let leaders:=(Encoding.list Encoding.boolean).encode (true::List.replicate (N-1) false)
  obtain ⟨markTime,markBound,markRun⟩:=emitLeaderMarkers_executes extra w store widthPositive empty
  let marked:=Function.update store (w 4) (leaders.reverse++store (w 4))
  have markedEmpty (i : Fin 9) (member : i∈([5,6,7,8] : List (Fin 9))) : marked (w i)=[] := by
    have ne : i≠4 := by intro eq;subst i;simp at member
    simpa [marked,w.injective.eq_iff,ne] using empty i member
  obtain ⟨headerTime,headerBound,headerRun⟩:=External.CoverNormalization.emitReversedNatural_executes (extra+3) w.rounds marked
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl
        all_goals simp [SerializeWorkspace.rounds,roundHeaderPositions,markedEmpty])
  let headed:=Function.update marked (w 4) ((Encoding.natural.encode B).reverse++marked (w 4))
  have headerAs : Executes (External.CoverNormalization.emitReversedNatural (extra+3) w.rounds) marked headerTime headed := by
    simpa [SerializeWorkspace.rounds,roundHeaderPositions,headed,marked,w.injective.eq_iff,B] using headerRun
  have copying:=copy_executes (extra+6) (w 1) (w 5) (w 6)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) headed
    (by simp [headed,w.injective.eq_iff,markedEmpty])
  have baseAt : headed (w 1)=store (w 1) := by simp [headed,marked,w.injective.eq_iff]
  have counterEmpty : headed (w 5)=[] := by simp [headed,w.injective.eq_iff,markedEmpty]
  rw [baseAt,counterEmpty,List.append_nil] at copying
  let copied:=Function.update headed (w 5) (store (w 1))
  have dropping:=discardBit_executes (w 5) copied
  let ready:=Function.update headed (w 5) (store (w 1)).tail
  have dropAs : Executes (discardBit (w 5)) copied 1 ready := by simpa [copied,ready] using dropping
  have repeating:=repeatedCopy_executes (extra+6) (w 2) (w 5) (w 4) (w 6)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (store (w 1)).tail ready (by simp [ready]) (by simp [ready,headed,w.injective.eq_iff,markedEmpty])
  let repeated:=Function.update (Function.update ready (w 5) []) (w 4)
    ((Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) (List.replicate (B-1) path)).reverse++headed (w 4))
  have repeatAs : Executes (repeatedCopy (extra+6) (w 2) (w 5) (w 4) (w 6)) ready
      ((5*(store (w 2)).length+4)*(B-1)+1) repeated := by
    simpa [ready,headed,marked,w.injective.eq_iff,pathCode,repeated,B,copies_encoded_reverse] using repeating
  have starring:=copy_executes (extra+6) (w 3) (w 4) (w 6)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) repeated
    (by simp [repeated,ready,headed,w.injective.eq_iff,markedEmpty])
  have starAt : repeated (w 3)=store (w 3) := by simp [repeated,ready,headed,marked,w.injective.eq_iff]
  rw [starAt] at starring
  have final : Function.update repeated (w 4) (store (w 3)++repeated (w 4))=
      Function.update store (w 4)
        ((leaders++(Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode
          (List.replicate (B-1) path++[star])).reverse++store (w 4)) := by
    have length : (List.replicate (B-1) path++[star]).length=B := by simp;omega
    have encoding : (Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode
        (List.replicate (B-1) path++[star])=
        Encoding.natural.encode B++Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) (List.replicate (B-1) path)++
          (Encoding.list (Encoding.list Encoding.natural)).encode star := by
      change Encoding.natural.encode (List.replicate (B-1) path++[star]).length++_=_
      rw [length];simp only [sequence_append,Encoding.sequence,List.append_nil,List.append_assoc]
    rw [encoding]
    funext r
    by_cases e4 : r=w 4
    · subst r;simp [repeated,headed,marked,starCode,List.reverse_append,List.append_assoc]
    · by_cases e5 : r=w 5
      · subst r;simp [repeated,w.injective.eq_iff,empty]
      · simp [repeated,ready,headed,marked,e4,e5]
  rw [final] at starring
  have combined:=markRun.sequence (headerAs.sequence (copying.sequence (dropAs.sequence (repeatAs.sequence starring))))
  refine ⟨_,?_,combined⟩
  have headerLimit : headerTime ≤ 30*(B+1)^2 := by
    simpa [SerializeWorkspace.rounds,roundHeaderPositions,marked,w.injective.eq_iff,B] using headerBound
  change markTime ≤ 40*(N+1)^2 at markBound
  change _ ≤ 40*(N+1)^2+30*(B+1)^2+5*B+(5*(store (w 2)).length+4)*(B-1)+5*(store (w 3)).length+20
  omega

theorem emitNetworkSerialization_word (extra : Nat) (w : SerializeWorkspace extra)
    (store : Fin (extra+9) → List Bool) (base : Nat) (coefficients : List Nat)
    (positive : 0<base) (width : (store (w 0)).length=networkOrder base coefficients)
    (baseLength : (store (w 1)).length=base)
    (pathCode : store (w 2)=((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base coefficients)).reverse)
    (starCode : store (w 3)=((Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix base coefficients)).reverse)
    (empty : ∀ i∈([5,6,7,8] : List (Fin 9)),store (w i)=[]) :
    ∃ time ≤ serializationCost (store (w 0)).length base (store (w 2)).length (store (w 3)).length,
      Executes (emitNetworkSerialization extra w) store time
        (Function.update store (w 4) ((networkWord base coefficients).reverse++store (w 4))) := by
  obtain ⟨time,bound,ran⟩:=emitNetworkSerialization_executes extra w store (pathMatrix base coefficients) (starMatrix base coefficients)
    (by rw [width];simp [networkOrder]) (by simpa [baseLength] using positive) pathCode starCode empty
  exact ⟨time,by simpa only [baseLength] using bound,by simpa only [width,baseLength,networkWord,networkLeaders,networkRounds] using ran⟩

end Counting.HardnessNetworkMachine
