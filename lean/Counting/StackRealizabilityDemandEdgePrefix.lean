import Counting.StackRealizabilityDemandEdgeLoop
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def demandEdgeHeaderRoles : FullListWorkspace 15:=
  ⟨![19,1,4,5,30,6,8,9,7,10,11,12,13,14,15,16,31],by decide⟩

def demandEdgePrefix : Routine 30:=sequence (readListHeader 15 demandEdgeHeaderRoles) (forEach 30 demandEdge)

def demandEdgePrefixStore (store : Store 30) (level target old value total : Nat)
    (edges : List (Nat×Nat)) (suffix : List Bool) : Store 30:=
  Function.update (Function.update store 19 suffix) 26 (total+demandEdges level target old value edges).bits

theorem demandEdgePrefix_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail) (level target old value total : Nat)
    (levelInput : store 0=level.bits) (targetInput : store 22=target.bits) (oldInput : store 25=old.bits)
    (weight : store 24=value.bits) (accumulator : store 26=total.bits)
    (work : ∀ r : Fin 32,4 ≤ r.val → r.val<17 → store r=[])
    (e2 : store 2=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e30 : store 30=[]) (e31 : store 31=[])
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 19=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix) :
    ∃ time ≤ 700000*((store 19).length+level.size+target.size+old.size+value.size+total.size+1)^7,
      Executes demandEdgePrefix store time
        (demandEdgePrefixStore store level target old value total edges suffix):=by
  have pairPositive (edge : Nat×Nat) : 0<((Encoding.product Encoding.natural Encoding.natural).encode edge).length:=by
    simp only [Encoding.product,List.length_append,Encoding.natural_length]
    omega
  have headerWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (demandEdgeHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [demandEdgeHeaderRoles,work,e30,e31]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 15 demandEdgeHeaderRoles store accepted tail
    status headerWork (Encoding.product Encoding.natural Encoding.natural) pairPositive edges suffix input
  let ready:=Function.update (Function.update store 19
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix))
      30 (List.replicate edges.length true)
  have readyWork (r : Fin 32) (lo : 4 ≤ r.val) (hi : r.val<17) : ready r=[]:=by
    have n19 : r≠19:=by intro same;subst r;norm_num at hi
    have n30 : r≠30:=by intro same;subst r;norm_num at hi
    simp [ready,n19,n30,work r lo hi]
  obtain ⟨loopTime,loopBound,loopRun⟩:=demandEdgeLoop_executes ready level target old value total
    (by simp [ready,levelInput]) (by simp [ready,targetInput]) (by simp [ready,oldInput])
    (by simp [ready,weight]) (by simp [ready,accumulator]) readyWork
    (by simp [ready,e2]) (by simp [ready,e27]) (by simp [ready,e28]) (by simp [ready,e29])
    edges suffix (by simp [ready]) (List.replicate edges.length true) (by simp [ready]) (by simp)
  have final : demandEdgeLoopStore ready level target old value total edges suffix=
      demandEdgePrefixStore store level target old value total edges suffix:=by
    funext r
    by_cases r19 : r=19 <;> by_cases r26 : r=26 <;> by_cases r30 : r=30 <;>
      simp [demandEdgeLoopStore,demandEdgePrefixStore,ready,r19,r26,r30,e30]
  rw [final] at loopRun
  have shorter : (ready 19).length ≤ (store 19).length:=by
    rw [input]
    change (Encoding.sequence _ edges++suffix).length ≤
      ((Encoding.natural.encode edges.length++Encoding.sequence _ edges)++suffix).length
    simp only [List.length_append];omega
  have countBound : edges.length ≤ (store 19).length:=by
    have count:=VerifiedParser.sequence_count_le pairPositive edges
    rw [input]
    change edges.length ≤ ((Encoding.natural.encode edges.length++Encoding.sequence _ edges)++suffix).length
    simp only [List.length_append];omega
  let S:=(store 19).length+level.size+target.size+old.size+value.size+total.size+1
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have countS : edges.length ≤ S:=by dsimp only [S];omega
  have valueS : value.size ≤ S:=by dsimp only [S];omega
  have inputS : (ready 19).length+level.size+target.size+old.size+value.size+total.size+1 ≤ S:=by dsimp only [S];omega
  have headerLimit : headerTime ≤ 1820*S^3:=by
    apply headerBound.trans
    change 1820*((store 19).length+1)^3 ≤ _
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
  have extra : edges.length*value.size ≤ S^2:=by simpa only [pow_two] using Nat.mul_le_mul countS valueS
  have linearSquare : S ≤ S^2:=Nat.le_self_pow (by decide) _
  have augmented : (ready 19).length+level.size+target.size+old.size+value.size+total.size+1+
      edges.length*value.size ≤ 2*S^2:=by omega
  have loopLimit : loopTime ≤ 680000*S^7+2*S+1:=by
    have bound : loopTime ≤ S*(85000*(2*S^2)^3+2)+1:=by
      apply loopBound.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul countS
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left augmented 3)) 2)) 1
    have expansion : S*(85000*(2*S^2)^3+2)+1=680000*S^7+2*S+1:=by ring
    exact expansion ▸ bound
  have cube : S^3 ≤ S^7:=Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^7:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^7:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _ ≤ 700000*S^7;omega,headerRun.sequence loopRun⟩

end Counting.StackMachine.RealizabilityCheck
