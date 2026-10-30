import Counting.StackRealizabilityInitialLoop
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def initialNodeHeaderRoles : FullListWorkspace 9:=⟨![17,1,0,2,23,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩
def initialWeightHeaderRoles : FullListWorkspace 9:=⟨![20,1,0,2,25,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩

def initialPrefix : Routine 24:=sequence (readListHeader 9 initialNodeHeaderRoles)
  (sequence (readListHeader 9 initialWeightHeaderRoles)
    (sequence (clear 25) (sequence (forEach 23 initialItem) (clear 18))))

def initialPrefixStore (store : Store 24) (nodes : List Executable.Node) (values : List Nat)
    (leaders nonleaders : Nat) (nodeSuffix weightSuffix : List Bool) : Store 24:=
  Function.update (Function.update (Function.update (Function.update store
    17 (Encoding.sequence Encoding.node nodes++nodeSuffix)) 20 weightSuffix)
    21 (leaders+initialRangeSum nodes true 0 values).bits)
    22 (nonleaders+initialRangeSum nodes false 0 values).bits

/-- The two explicit list headers are read by the program. Equal lengths
are established by the separate length guard before this semantic pass. -/
theorem initialPrefix_executes (store : Store 24) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 26,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (nodes : List Executable.Node) (values : List Nat) (length : values.length=nodes.length)
    (nodeSuffix weightSuffix : List Bool)
    (nodeInput : store 17=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : store 20=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (leaders nonleaders : Nat) (first : store 21=leaders.bits) (second : store 22=nonleaders.bits) :
    ∃ time ≤ 13000*((store 17).length+(store 20).length+leaders.size+nonleaders.size+1)^5,
      Executes initialPrefix store time (initialPrefixStore store nodes values leaders nonleaders nodeSuffix weightSuffix):=by
  have nodePositive (node : Executable.Node) : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have countPositive (value : Nat) : 0<(Encoding.natural.encode value).length:=by simp only [Encoding.natural_length];omega
  have nodeWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (initialNodeHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [initialNodeHeaderRoles,work,e23]
  obtain ⟨nodeTime,nodeBound,nodeRead⟩:=readListHeader_canonical 9 initialNodeHeaderRoles store accepted tail
    status nodeWork Encoding.node nodePositive nodes nodeSuffix nodeInput
  let nodeReady:=Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes++nodeSuffix))
    23 (List.replicate nodes.length true)
  have weightWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      nodeReady (initialWeightHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [nodeReady,initialWeightHeaderRoles,work,e25]
  obtain ⟨weightTime,weightBound,weightRead⟩:=readListHeader_canonical 9 initialWeightHeaderRoles nodeReady accepted tail
    (by simp [initialWeightHeaderRoles,nodeReady,status]) weightWork Encoding.natural countPositive values weightSuffix
    (by simp [initialWeightHeaderRoles,nodeReady,weightInput])
  let bothReady:=Function.update (Function.update nodeReady 20 (Encoding.sequence Encoding.natural values++weightSuffix))
    25 (List.replicate values.length true)
  have clearing:=clear_executes (25:Fin 26) bothReady
  have countAt : bothReady 25=List.replicate values.length true:=by simp [bothReady]
  rw [countAt,List.length_replicate] at clearing
  let ready:=Function.update bothReady 25 []
  have readyWork (r : Fin 26) (small : r.val<17) (different : r≠1) : ready r=[]:=by
    have n17 : r≠17:=by intro same;subst r;norm_num at small
    have n20 : r≠20:=by intro same;subst r;norm_num at small
    have n23 : r≠23:=by intro same;subst r;norm_num at small
    have n25 : r≠25:=by intro same;subst r;norm_num at small
    simp [ready,bothReady,nodeReady,n17,n20,n23,n25,work r small different]
  obtain ⟨loopTime,loopBound,loopRun⟩:=initialLoop_executes ready accepted tail
    (by simp [ready,bothReady,nodeReady,status]) readyWork
    (by simp [ready,bothReady,nodeReady,e19]) (by simp [ready,bothReady,nodeReady,e24]) (by simp [ready])
    nodes 0 values (by omega) nodeSuffix (by simp [ready,bothReady,nodeReady])
    (by simp [ready,bothReady,nodeReady,e18]) leaders nonleaders
    (by simp [ready,bothReady,nodeReady,first]) (by simp [ready,bothReady,nodeReady,second])
    weightSuffix (by simp [ready,bothReady]) (List.replicate nodes.length true)
    (by simp [ready,bothReady,nodeReady]) (by simp [length])
  let scanned:=initialLoopStore ready nodes 0 leaders nonleaders values weightSuffix
  have clearIndex:=clear_executes (18:Fin 26) scanned
  have indexAt : scanned 18=List.replicate values.length true:=by
    simp [scanned,initialLoopStore,ready,bothReady,nodeReady,e18]
  rw [indexAt,List.length_replicate] at clearIndex
  have final : Function.update scanned 18 []=initialPrefixStore store nodes values leaders nonleaders nodeSuffix weightSuffix:=by
    funext r
    fin_cases r <;> simp [scanned,initialLoopStore,ready,bothReady,nodeReady,initialPrefixStore,e18,e23,e25]
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
  let S:=(store 17).length+(store 20).length+leaders.size+nonleaders.size+1
  have positive : 1≤S:=by dsimp only [S];omega
  have countS : values.length≤S:=by dsimp only [S];omega
  have readNode : nodeTime≤1820*S^3:=by apply nodeBound.trans;gcongr;change (store 17).length+1≤S;dsimp only [S];omega
  have readWeight : weightTime≤1820*S^3:=by apply weightBound.trans;gcongr;change (store 20).length+1≤S;dsimp only [S];omega
  have inputS : (ready 17).length+(ready 20).length+leaders.size+nonleaders.size+1≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤8000*S^5+2*S+1:=by
    have bound : loopTime≤S*(8000*S^4+2)+1:=loopBound.trans (by gcongr)
    nlinarith
  have cube : S^3≤S^5:=Nat.pow_le_pow_right positive (by decide)
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have one : 1≤S^5:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _≤13000*S^5;omega,
    nodeRead.sequence (weightRead.sequence (clearing.sequence (loopRun.sequence clearIndex)))⟩

end Counting.StackMachine.RealizabilityCheck
