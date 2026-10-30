import Counting.StackDagHeader
import Counting.StackEncodingDagReadPreserving

/-! Actual indexed access to a serialized node followed by extraction of
its metadata. Both scans are charged; the original DAG word and unary
index are preserved. The specification identifies the selected node,
rather than assuming its level or label is supplied by an oracle. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def selectedHeaderRoles : HeaderWorkspace 14 := ⟨![19,0,2,3,1,4],by decide⟩

def selectedHeader : Routine 18 :=
  sequence DagParser.preservingNodeRead
    (sequence (headerRoutine 14 selectedHeaderRoles) (ofProgram (combineFlagsProgram 18 1)))

def nodeSuffix (node : Executable.Node) : List Bool:=
  Encoding.natural.encode node.degree++
    (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming

def selectedHeaderStore (store : Store 18) (node : Executable.Node) : Store 18 :=
  fun r=>if r=19 then nodeSuffix node else if r=0 then node.level.bits
    else if r=2 then (parentCode node).bits else if r=3 then [node.leader] else store r

theorem selectedHeader_get (store : Store 18) (accepted : Bool) (tail : List Bool)
    (statusEq : store 1=accepted::tail)
    (workspaceEmpty : ∀ r : Fin 17,r≠1 → store (DagParser.nodeRoles r)=[])
    (outputEmpty : store 19=[]) (values : List Executable.Node) (index : Fin values.length)
    (suffix : List Bool) (sourceEq : store 17=Encoding.sequence Encoding.node values++suffix)
    (indexEq : (store 18).length=index.val) :
    ∃ time ≤ (2*(store 18).length+3)*2029*((store 17).length+1)^3+
        6*(store 17).length+7*(store 18).length+6*(Encoding.node.encode values[index]).length+36,
      Executes selectedHeader store time (selectedHeaderStore store values[index]) := by
  obtain ⟨readTime,readBound,readRun⟩:=DagParser.preservingNodeRead_get store accepted tail
    statusEq workspaceEmpty outputEmpty values index suffix sourceEq indexEq
  let node:=values[index]
  let readStore:=Function.update store 19 (Encoding.node.encode node)
  have empty0 : store 0=[]:=workspaceEmpty 0 (by decide)
  have empty2 : store 2=[]:=workspaceEmpty 2 (by decide)
  have empty3 : store 3=[]:=workspaceEmpty 3 (by decide)
  have empty4 : store 4=[]:=workspaceEmpty 4 (by decide)
  obtain ⟨headerTime,headerBound,headerRun⟩:=header_executes 14 selectedHeaderRoles readStore
    (by simp [readStore,selectedHeaderRoles,empty4])
  have readSource : readStore (selectedHeaderRoles 0)=Encoding.node.encode node:=by
    simp [readStore,selectedHeaderRoles]
  rw [readSource] at headerBound
  have decoded : header (Encoding.node.encode node)=
      ⟨node.level.bits,(parentCode node).bits,[node.leader],nodeSuffix node,true⟩ := by
    simpa only [List.append_nil,nodeSuffix] using header_node node []
  let parsed:=headerStore 14 selectedHeaderRoles readStore
  have parsedEq : parsed=Function.update (selectedHeaderStore store node) 1 (true::accepted::tail) := by
    funext r
    fin_cases r <;> simp [parsed,headerStore,selectedHeaderRoles,readStore,selectedHeaderStore,
      decoded,empty0,empty2,empty3,statusEq]
  have combined:=combineFlags_executes 18 1 parsed accepted true tail (by rw [parsedEq];simp)
  have restored : Function.update parsed 1 ((accepted && true)::tail)=selectedHeaderStore store node := by
    rw [parsedEq,Function.update_idem]
    have same : selectedHeaderStore store node 1=accepted::tail:=by simp [selectedHeaderStore,statusEq]
    simp only [Bool.and_true,←same,Function.update_eq_self]
  rw [restored] at combined
  dsimp only [node] at headerBound
  refine ⟨readTime+1+(headerTime+1+3),by omega,readRun.sequence (headerRun.sequence combined)⟩

end Counting.StackMachine.DagValidation
