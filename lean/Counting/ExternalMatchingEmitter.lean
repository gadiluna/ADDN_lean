import Counting.StackEmitNatural
import Counting.StackEmitTripleSelected
import Counting.StackRoutineClearSelected

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev EdgeWorkspace (extra : Nat) := Fin 12 ↪ Fin (extra+12)
def edgeNaturalPositions (which : Fin 3) : Fin 5 ↪ Fin 12 :=
  ⟨![![0,3,7,8,9],![1,4,7,8,9],![2,5,7,8,9]] which,by fin_cases which <;> decide⟩
def edgeNaturalRoles (extra : Nat) (w : EdgeWorkspace extra) (which : Fin 3) : PowerWorkspace (extra+7) :=
  (edgeNaturalPositions which).trans w

def edgeTriplePositions : Fin 6 ↪ Fin 12 := ⟨![3,4,5,6,10,11],by decide⟩
def edgeTripleRoles (extra : Nat) (w : EdgeWorkspace extra) : TripleWorkspace (extra+6) := edgeTriplePositions.trans w

def emitEdge (extra : Nat) (w : EdgeWorkspace extra) : Routine (extra+10) :=
  sequence (emitNatural (extra+7) (edgeNaturalRoles extra w 0))
    (sequence (emitNatural (extra+7) (edgeNaturalRoles extra w 1))
      (sequence (emitNatural (extra+7) (edgeNaturalRoles extra w 2))
        (sequence (emitTripleSelected (extra+6) (edgeTripleRoles extra w) id)
          (clearRegisters [w 3,w 4,w 5]))))

theorem natural_length_le (n : Nat) : (Encoding.natural.encode n).length ≤ 2*n+1 := by
  have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [Encoding.natural_length];omega

theorem emitEdge_executes (extra : Nat) (w : EdgeWorkspace extra) (store : Fin (extra+12) → List Bool)
    (empty : ∀ i∈([3,4,5,7,8,9,10,11] : List (Fin 12)),store (w i)=[]) :
    ∃ time ≤ 300*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^2,
      Executes (emitEdge extra w) store time
        (Function.update store (w 6)
          (((Encoding.list Encoding.natural).encode [(store (w 0)).length,(store (w 1)).length,(store (w 2)).length]).reverse++store (w 6))) := by
  let a := (store (w 0)).length
  let b := (store (w 1)).length
  let c := (store (w 2)).length
  obtain ⟨t0,h0,r0⟩ := emitNatural_executes (extra+7) (edgeNaturalRoles extra w 0) store
    (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  let s1 := Function.update store (w 3) (Encoding.natural.encode a)
  have r0as : Executes (emitNatural (extra+7) (edgeNaturalRoles extra w 0)) store t0 s1 := by
    simpa [edgeNaturalRoles,edgeNaturalPositions,s1,a,empty 3 (by decide)] using r0
  obtain ⟨t1,h1,r1⟩ := emitNatural_executes (extra+7) (edgeNaturalRoles extra w 1) s1
    (by simp [edgeNaturalRoles,edgeNaturalPositions,s1,w.injective.eq_iff,empty 7 (by decide)])
    (by simp [edgeNaturalRoles,edgeNaturalPositions,s1,w.injective.eq_iff,empty 8 (by decide)])
    (by simp [edgeNaturalRoles,edgeNaturalPositions,s1,w.injective.eq_iff,empty 9 (by decide)])
  let s2 := Function.update s1 (w 4) (Encoding.natural.encode b)
  have r1as : Executes (emitNatural (extra+7) (edgeNaturalRoles extra w 1)) s1 t1 s2 := by
    simpa [edgeNaturalRoles,edgeNaturalPositions,s1,s2,b,w.injective.eq_iff,empty 4 (by decide)] using r1
  obtain ⟨t2,h2,r2⟩ := emitNatural_executes (extra+7) (edgeNaturalRoles extra w 2) s2
    (by simp [edgeNaturalRoles,edgeNaturalPositions,s2,s1,w.injective.eq_iff,empty 7 (by decide)])
    (by simp [edgeNaturalRoles,edgeNaturalPositions,s2,s1,w.injective.eq_iff,empty 8 (by decide)])
    (by simp [edgeNaturalRoles,edgeNaturalPositions,s2,s1,w.injective.eq_iff,empty 9 (by decide)])
  let s3 := Function.update s2 (w 5) (Encoding.natural.encode c)
  have r2as : Executes (emitNatural (extra+7) (edgeNaturalRoles extra w 2)) s2 t2 s3 := by
    simpa [edgeNaturalRoles,edgeNaturalPositions,s3,s2,s1,c,w.injective.eq_iff,empty 5 (by decide)] using r2
  let edge := (Encoding.list Encoding.natural).encode [a,b,c]
  have emit := emitTripleSelected_words (extra+6) (edgeTripleRoles extra w) id s3
    (by simp [edgeTripleRoles,edgeTriplePositions,s3,s2,s1,w.injective.eq_iff,empty 10 (by decide)])
    (by simp [edgeTripleRoles,edgeTriplePositions,s3,s2,s1,w.injective.eq_iff,empty 11 (by decide)])
  let s4 := Function.update s3 (w 6) (edge.reverse++store (w 6))
  have emitAs : Executes (emitTripleSelected (extra+6) (edgeTripleRoles extra w) id) s3
      (7*((Encoding.natural.encode a).length+(Encoding.natural.encode b).length+(Encoding.natural.encode c).length)+25) s4 := by
    simpa [edgeTripleRoles,edgeTriplePositions,s3,s2,s1,s4,edge,w.injective.eq_iff,Encoding.list,Encoding.sequence,List.append_assoc] using emit
  have lengthA := natural_length_le a
  have lengthB := natural_length_le b
  have lengthC := natural_length_le c
  have selectedBound (r : Fin (extra+12)) (member : r∈[w 3,w 4,w 5]) : (s4 r).length ≤ 2*(a+b+c)+1 := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|h
    · simp only [s4,s3,s2,s1,Function.update_of_ne (w.injective.ne (by decide : (3:Fin 12)≠6)),
        Function.update_of_ne (w.injective.ne (by decide : (3:Fin 12)≠5)),Function.update_of_ne (w.injective.ne (by decide : (3:Fin 12)≠4)),Function.update_self];omega
    · have eq : s4 (w 4)=Encoding.natural.encode b := by simp [s4,s3,s2,w.injective.eq_iff]
      rw [eq];omega
    · have eq : s4 (w 5)=Encoding.natural.encode c := by simp [s4,s3,w.injective.eq_iff]
      rw [eq];omega
    · contradiction
  obtain ⟨clearTime,clearBound,clearing⟩ := clearRegisters_selected_executes [w 3,w 4,w 5] s4 (2*(a+b+c)+1) selectedBound
  have cleared : clearedStore [w 3,w 4,w 5] s4=Function.update store (w 6) (edge.reverse++store (w 6)) := by
    funext r
    by_cases e3 : r=w 3
    · subst r;simp [clearedStore,w.injective.eq_iff,empty 3 (by decide)]
    · by_cases e4 : r=w 4
      · subst r;simp [clearedStore,w.injective.eq_iff,empty 4 (by decide)]
      · by_cases e5 : r=w 5
        · subst r;simp [clearedStore,w.injective.eq_iff,empty 5 (by decide)]
        · simp [clearedStore,s4,s3,s2,s1,e3,e4,e5,Function.update_apply]
  rw [cleared] at clearing
  have combined := r0as.sequence (r1as.sequence (r2as.sequence (emitAs.sequence clearing)))
  refine ⟨t0+1+(t1+1+(t2+1+(7*((Encoding.natural.encode a).length+(Encoding.natural.encode b).length+(Encoding.natural.encode c).length)+25+1+clearTime))),?_,combined⟩
  change t0 ≤ 20*(a+1)^2 at h0
  have boundB : t1 ≤ 20*(b+1)^2 := by simpa [edgeNaturalRoles,edgeNaturalPositions,s1,b,w.injective.eq_iff] using h1
  have boundC : t2 ≤ 20*(c+1)^2 := by simpa [edgeNaturalRoles,edgeNaturalPositions,s2,s1,c,w.injective.eq_iff] using h2
  simp only [List.length_cons,List.length_nil] at clearBound
  let S := a+b+c+1
  have p0 : (a+1)^2 ≤ S^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
  have p1 : (b+1)^2 ≤ S^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
  have p2 : (c+1)^2 ≤ S^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
  have linear : S ≤ S^2 := Nat.le_self_pow (by decide) S
  have positive : 1 ≤ S^2 := Nat.one_le_pow _ _ (by dsimp [S];omega)
  change _ ≤ 300*S^2
  have total0 : t0 ≤ 20*S^2 := h0.trans (Nat.mul_le_mul_left 20 p0)
  have total1 : t1 ≤ 20*S^2 := boundB.trans (Nat.mul_le_mul_left 20 p1)
  have total2 : t2 ≤ 20*S^2 := boundC.trans (Nat.mul_le_mul_left 20 p2)
  have codes : (Encoding.natural.encode a).length+(Encoding.natural.encode b).length+
      (Encoding.natural.encode c).length ≤ 2*S+1 := by dsimp [S];omega
  have clear : clearTime ≤ 6*S+3 := by dsimp [S];omega
  omega

end Counting.External.MatchingMachine
