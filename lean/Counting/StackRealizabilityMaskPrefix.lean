import Counting.StackRealizabilityMaskTable
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def maskNodeHeaderRoles : FullListWorkspace 13:=⟨![17,1,0,2,20,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩
def maskPrefix : Routine 28:=sequence (readListHeader 13 maskNodeHeaderRoles) maskTable

def maskPrefixStore (store : Store 28) (nodes : List Executable.Node) (suffix : List Bool)
    (old next : Nat) : Store 28:=maskTableStore
      (Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes++suffix))
        20 (List.replicate nodes.length true)) nodes old next

/-- The width is obtained by the real bounded list-header parser. No
population count or externally supplied node-count oracle controls the scan. -/
theorem maskPrefix_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e24 : store 24=[]) (e25 : store 25=[]) (e26 : store 26=[])
    (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (nodes : List Executable.Node) (suffix : List Bool)
    (input : store 17=(Encoding.list Encoding.node).encode nodes++suffix)
    (old next : Nat) (oldAt : store 22=old.bits) (nextAt : store 23=next.bits) :
    ∃ time ≤ 11000*((store 17).length+old.size+next.size+1)^5,
      Executes maskPrefix store time (maskPrefixStore store nodes suffix old next):=by
  have nodePositive (node : Executable.Node) : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega
  have nodeWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (maskNodeHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [maskNodeHeaderRoles,work,e20]
  obtain ⟨readTime,readBound,reading⟩:=readListHeader_canonical 13 maskNodeHeaderRoles store accepted tail
    status nodeWork Encoding.node nodePositive nodes suffix input
  let ready:=Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes++suffix))
    20 (List.replicate nodes.length true)
  have readyWork (r : Fin 30) (small : r.val<17) (different : r≠1) : ready r=[]:=by
    have n17 : r≠17:=by intro same;subst r;norm_num at small
    have n20 : r≠20:=by intro same;subst r;norm_num at small
    simp [ready,n17,n20,work r small different]
  obtain ⟨tableTime,tableBound,tableRun⟩:=maskTable_executes ready accepted tail
    (by simp [ready,status]) readyWork (by simp [ready,e18]) (by simp [ready,e19]) (by simp [ready,e21])
    (by simp [ready,e24]) (by simp [ready,e25]) (by simp [ready,e26])
    (by simp [ready,e27]) (by simp [ready,e28]) (by simp [ready,e29])
    nodes suffix (by simp [ready]) (by simp [ready]) old next (by simp [ready,oldAt]) (by simp [ready,nextAt])
  have shorter : (ready 17).length ≤ (store 17).length:=by
    rw [input]
    change (Encoding.sequence Encoding.node nodes++suffix).length ≤
      ((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++suffix).length
    simp only [List.length_append]
    omega
  let S:=(store 17).length+old.size+next.size+1
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have readLimit : readTime ≤ 1820*S^3:=by
    apply readBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by change (store 17).length+1 ≤ S;dsimp only [S];omega) 3)
  have tableLimit : tableTime ≤ 9000*S^5:=by
    apply tableBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 5)
  have cube : S^3 ≤ S^5:=Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _ ≤ 11000*S^5;omega,reading.sequence tableRun⟩

end Counting.StackMachine.RealizabilityCheck
