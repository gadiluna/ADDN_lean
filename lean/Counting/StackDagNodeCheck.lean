import Counting.StackDagNodeSemantics

/-! End-to-end semantic validation of a canonically serialized node. The
machine reads its level, optional parent and leader bit, chooses the actual
initial/noninitial branch, and cleans every metadata register it used. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def nodeCheckHeaderRoles : HeaderWorkspace 29:=⟨![28,21,22,23,1,4],by decide⟩
def nodeCheckRoutine : Routine 33:=
  sequence (headerRoutine 29 nodeCheckHeaderRoles)
    (sequence (ofProgram (combineFlagsProgram 33 1))
      (sequence nodeSemanticsRoutine (sequence (clear 21) (clear 23))))

def nodeCheckStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Store 33:=
  Function.update (Function.update store 28 []) 1 ((accepted && nodeCondition values current node)::tail)

theorem nodeCheck_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,21,22,23,25,26,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (currentBits : store 24=current.bits) (budget : (store 29).length=current)
    (input : store 28=Encoding.node.encode node) :
    ∃ time ≤ 901000*((store 17).length+(store 28).length+current.size+1)^5,
      Executes nodeCheckRoutine store time (nodeCheckStore store accepted tail values current node) := by
  obtain ⟨headerTime,headerBound,headerRun⟩:=header_executes 29 nodeCheckHeaderRoles store
    (work 4 (by decide) (by decide))
  have parsed : header (store 28)=⟨node.level.bits,(parentCode node).bits,[node.leader],nodeSuffix node,true⟩:=by
    rw [input]
    simpa only [List.append_nil,nodeSuffix] using header_node node []
  let readStore:=Function.update (Function.update (Function.update (Function.update (Function.update
    store 28 (nodeSuffix node)) 21 node.level.bits) 22 (parentCode node).bits) 23 [node.leader]) 1 (true::accepted::tail)
  have readEq : headerStore 29 nodeCheckHeaderRoles store=readStore:=by
    funext r
    fin_cases r <;> simp [headerStore,nodeCheckHeaderRoles,parsed,readStore,extraWork,status]
  rw [readEq] at headerRun
  have combined:=combineFlags_executes 33 1 readStore accepted true tail (by simp [readStore])
  let ready:=Function.update readStore 1 (accepted::tail)
  have combinedRun : Executes (ofProgram (combineFlagsProgram 33 1)) readStore 3 ready:=by
    simpa only [Bool.and_true] using combined
  have readyWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : ready r=[]:=by
    have n21 : r≠21:=by intro eq;subst r;norm_num at small
    have n22 : r≠22:=by intro eq;subst r;norm_num at small
    have n23 : r≠23:=by intro eq;subst r;norm_num at small
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    simp [ready,readStore,ne,n21,n22,n23,n28,work r small ne]
  have readyExtra (r : Fin 35) (member : r∈({18,19,20,25,26,30,31,32,33,34}:Finset (Fin 35))) : ready r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [ready,readStore,extraWork]
  obtain ⟨checkTime,checkBound,checkRun⟩:=nodeSemantics_executes ready accepted tail
    (by simp [ready]) readyWork readyExtra values current node inside sourceSuffix
    (by simp [ready,readStore,source])
    (by simp [ready,readStore]) (by simp [ready,readStore]) (by simp [ready,readStore])
    (by simp [ready,readStore,currentBits]) (by simp [ready,readStore,budget]) (by simp [ready,readStore])
  let checked:=nodeSemanticsStore ready accepted tail values current node
  have levelValue : checked 21=node.level.bits:=by simp [checked,nodeSemanticsStore,ready,readStore]
  have levelClear:=clear_executes (21:Fin 35) checked
  rw [levelValue,Encoding.bits_length] at levelClear
  let middle:=Function.update checked 21 []
  have leaderValue : middle 23=[node.leader]:=by simp [middle,checked,nodeSemanticsStore,ready,readStore]
  have leaderClear:=clear_executes (23:Fin 35) middle
  rw [leaderValue] at leaderClear
  have final : Function.update middle 23 []=nodeCheckStore store accepted tail values current node:=by
    funext r
    fin_cases r <;> simp [middle,checked,nodeSemanticsStore,ready,readStore,nodeCheckStore,extraWork]
  rw [final] at leaderClear
  have sameSource : ready 17=store 17:=by simp [ready,readStore]
  rw [sameSource] at checkBound
  change headerTime≤6*(store 28).length+17 at headerBound
  have fields:=node_metadata_size_le node
  let S:=(store 17).length+(store 28).length+current.size+1
  have limit : checkTime≤900010*S^5:=by simpa only [S,input] using checkBound
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have inputLimit : (store 28).length≤S:=by dsimp [S];omega
  have levelLimit : node.level.size≤S:=by rw [←input] at fields;omega
  refine ⟨_,?_,headerRun.sequence (combinedRun.sequence (checkRun.sequence (levelClear.sequence leaderClear)))⟩
  change headerTime+1+(3+1+(checkTime+1+(node.level.size+1+1+([node.leader].length+1))))≤901000*S^5
  simp only [List.length_cons,List.length_nil]
  have positiveS : 1≤S:=by dsimp [S];omega
  omega

end Counting.StackMachine.DagValidation
