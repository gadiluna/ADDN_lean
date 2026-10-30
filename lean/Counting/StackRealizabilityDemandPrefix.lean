import Counting.StackRealizabilityDemandLoop
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

attribute [local irreducible] demandItem

def demandNodeHeaderRoles : FullListWorkspace 15:=⟨![17,1,0,2,23,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩
def demandWeightHeaderRoles : FullListWorkspace 15:=⟨![20,1,0,2,29,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩

def demandPrefix : Routine 30:=sequence (readListHeader 15 demandNodeHeaderRoles)
  (sequence (readListHeader 15 demandWeightHeaderRoles)
    (sequence (clear 29) (sequence (forEach 23 demandItem) (clear 18))))

def demandPrefixStore (store : Store 30) (nodes : List Executable.Node) (values : List Nat)
    (target old total : Nat) (nodeSuffix weightSuffix : List Bool) : Store 30:=
  Function.update (Function.update (Function.update store
    17 (Encoding.sequence Encoding.node nodes++nodeSuffix)) 20 weightSuffix)
    26 (total+demandRangeSum nodes target old 0 values).bits

/-- The two explicit list headers are read by the program. Equal lengths
are established by the separate length guard before this semantic pass. -/
theorem demandPrefix_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 32,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e23 : store 23=[]) (e24 : store 24=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[]) (e30 : store 30=[]) (e31 : store 31=[])
    (nodes : List Executable.Node) (sorted : ∀ node∈nodes, Executable.countsSorted node.incoming=true)
    (values : List Nat) (length : values.length=nodes.length)
    (nodeSuffix weightSuffix : List Bool)
    (nodeInput : store 17=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : store 20=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old total : Nat) (level : store 22=target.bits) (parent : store 25=old.bits) (accumulator : store 26=total.bits) :
    ∃ time ≤ 93000000*((store 17).length+(store 20).length+total.size+target.size+old.size+1)^15,
      Executes demandPrefix store time (demandPrefixStore store nodes values target old total nodeSuffix weightSuffix):=by
  have nodePositive (node : Executable.Node) : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have countPositive (value : Nat) : 0<(Encoding.natural.encode value).length:=by simp only [Encoding.natural_length];omega
  have nodeWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (demandNodeHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [demandNodeHeaderRoles,work,e23]
  obtain ⟨nodeTime,nodeBound,nodeRead⟩:=readListHeader_canonical 15 demandNodeHeaderRoles store accepted tail
    status nodeWork Encoding.node nodePositive nodes nodeSuffix nodeInput
  let nodeReady:=Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes++nodeSuffix))
    23 (List.replicate nodes.length true)
  have weightWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      nodeReady (demandWeightHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [nodeReady,demandWeightHeaderRoles,work,e29]
  obtain ⟨weightTime,weightBound,weightRead⟩:=readListHeader_canonical 15 demandWeightHeaderRoles nodeReady accepted tail
    (by simp [demandWeightHeaderRoles,nodeReady,status]) weightWork Encoding.natural countPositive values weightSuffix
    (by simp [demandWeightHeaderRoles,nodeReady,weightInput])
  let bothReady:=Function.update (Function.update nodeReady 20 (Encoding.sequence Encoding.natural values++weightSuffix))
    29 (List.replicate values.length true)
  have clearing:=clear_executes (29:Fin 32) bothReady
  have countAt : bothReady 29=List.replicate values.length true:=by simp [bothReady]
  rw [countAt,List.length_replicate] at clearing
  let ready:=Function.update bothReady 29 []
  have readyWork (r : Fin 32) (small : r.val<17) (different : r≠1) : ready r=[]:=by
    have n17 : r≠17:=by intro same;subst r;norm_num at small
    have n20 : r≠20:=by intro same;subst r;norm_num at small
    have n23 : r≠23:=by intro same;subst r;norm_num at small
    have n29 : r≠29:=by intro same;subst r;norm_num at small
    simp [ready,bothReady,nodeReady,n17,n20,n23,n29,work r small different]
  obtain ⟨loopTime,loopBound,loopRun⟩:=demandLoop_executes ready accepted tail
    (by simp [ready,bothReady,nodeReady,status]) readyWork
    (by simp [ready,bothReady,nodeReady,e19]) (by simp [ready,bothReady,nodeReady,e24])
    (by simp [ready,bothReady,nodeReady,e27]) (by simp [ready,bothReady,nodeReady,e28]) (by simp [ready])
    (by simp [ready,bothReady,nodeReady,e30]) (by simp [ready,bothReady,nodeReady,e31])
    nodes sorted 0 values (by omega) nodeSuffix (by simp [ready,bothReady,nodeReady])
    (by simp [ready,bothReady,nodeReady,e18]) target old total
    (by simp [ready,bothReady,nodeReady,level]) (by simp [ready,bothReady,nodeReady,parent])
    (by simp [ready,bothReady,nodeReady,accumulator])
    weightSuffix (by simp [ready,bothReady]) (List.replicate nodes.length true)
    (by simp [ready,bothReady,nodeReady]) (by simp [length])
  let scanned:=demandLoopStore ready nodes target old 0 total values weightSuffix
  have clearIndex:=clear_executes (18:Fin 32) scanned
  have indexAt : scanned 18=List.replicate values.length true:=by
    simp [scanned,demandLoopStore,ready,bothReady,nodeReady,e18]
  rw [indexAt,List.length_replicate] at clearIndex
  have final : Function.update scanned 18 []=demandPrefixStore store nodes values target old total nodeSuffix weightSuffix:=by
    funext r
    fin_cases r <;> simp [scanned,demandLoopStore,ready,bothReady,nodeReady,demandPrefixStore,e18,e23,e29]
  rw [final] at clearIndex
  have nodeShorter : (ready 17).length≤(store 17).length:=by
    rw [nodeInput]
    change (Encoding.sequence Encoding.node nodes++nodeSuffix).length≤
      ((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++nodeSuffix).length
    simp only [List.length_append];omega
  have weightShorter : (ready 20).length≤(store 20).length:=by
    rw [weightInput]
    change (Encoding.sequence Encoding.natural values++weightSuffix).length≤
      ((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++weightSuffix).length
    simp only [List.length_append];omega
  have countBound : values.length≤(store 17).length:=by
    have count:=DagValidation.node_sequence_count_le nodes
    rw [nodeInput]
    change values.length≤((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++nodeSuffix).length
    simp only [List.length_append];omega
  let S:=(store 17).length+(store 20).length+total.size+target.size+old.size+1
  have positive : 1≤S:=by dsimp only [S];omega
  have countS : values.length≤S:=by dsimp only [S];omega
  have readNode : nodeTime≤1820*S^3:=by apply nodeBound.trans;gcongr;change (store 17).length+1≤S;dsimp only [S];omega
  have readWeight : weightTime≤1820*S^3:=by apply weightBound.trans;gcongr;change (store 20).length+1≤S;dsimp only [S];omega
  have inputS : (ready 17).length+(ready 20).length+total.size+target.size+old.size+1≤S:=by dsimp only [S];omega
  have sourceS : (ready 17).length ≤ S:=by dsimp only [S];omega
  have extra : values.length*(ready 17).length ≤ S^2:=by
    simpa only [pow_two] using Nat.mul_le_mul countS sourceS
  have linearSquare : S ≤ S^2:=Nat.le_self_pow (by decide) _
  have augmented : (ready 17).length+(ready 20).length+total.size+target.size+old.size+1+
      values.length*(ready 17).length ≤ 2*S^2:=by omega
  have loopLimit : loopTime ≤ 92160000*S^15+2*S+1:=by
    have bound : loopTime ≤ S*(720000*(2*S^2)^7+2)+1:=by
      apply loopBound.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul countS
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left augmented 7)) 2)) 1
    have expansion (x : Nat) : x*(720000*(2*x^2)^7+2)+1=92160000*x^15+2*x+1:=by ring
    exact expansion S ▸ bound
  have cube : S^3 ≤ S^15:=Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^15:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^15:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _≤93000000*S^15;omega,
    nodeRead.sequence (weightRead.sequence (clearing.sequence (loopRun.sequence clearIndex)))⟩

end Counting.StackMachine.RealizabilityCheck
