import Counting.StackDagReferencePrefix
import Counting.StackDagNodeCheck

/-! Scan all parent/red citations in one canonical node. This predicate is
independent of the already-proved validity checks and does not assume them. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def referenceParentRoles : Fin 6 ↪ Fin 35:=⟨![22,24,1,2,3,4],by decide⟩
def referenceNode : Routine 33:=sequence (headerRoutine 29 nodeCheckHeaderRoles)
  (sequence (ofProgram (combineFlagsProgram 33 1))
    (sequence (distinctGuard 29 referenceParentRoles)
      (sequence (clear 21) (sequence (clear 22) (sequence (clear 23)
        (sequence (ofProgram (FieldAccess.skipProgram 33 28)) referenceIncoming))))))

def noNodeReference (target : Nat) (node : Executable.Node) : Bool:=
  decide (node.parent≠some target) && noIncomingReference target node.incoming

def referenceNodeStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (target : Nat) (node : Executable.Node) (suffix : List Bool) : Store 33:=
  Function.update (Function.update store 28 suffix) 1 ((accepted && noNodeReference target node)::tail)

theorem parentCode_ne_iff (node : Executable.Node) (target : Nat) :
    parentCode node≠target+1 ↔ node.parent≠some target:=by
  cases parent:node.parent <;> simp [parentCode,parent]

theorem referenceNode_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,30,31}:Finset (Fin 35)) → store r=[])
    (target : Nat) (targetCode : store 26=target.bits) (targetPlus : store 24=(target+1).bits)
    (node : Executable.Node) (suffix : List Bool) (input : store 28=Encoding.node.encode node++suffix) :
    ∃ time ≤ 2200*((store 28).length+target.size+1)^3,
      Executes referenceNode store time (referenceNodeStore store accepted tail target node suffix) := by
  obtain ⟨headerTime,headerBound,headerRun⟩:=header_executes 29 nodeCheckHeaderRoles store (work 4 (by decide) (by decide))
  have parsed:=header_node node suffix
  rw [←input] at parsed
  let rest:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix
  let readStore:=Function.update (Function.update (Function.update (Function.update (Function.update
    store 28 (Encoding.natural.encode node.degree++rest)) 21 node.level.bits) 22 (parentCode node).bits)
    23 [node.leader]) 1 (true::accepted::tail)
  have readEq : headerStore 29 nodeCheckHeaderRoles store=readStore:=by
    funext r
    fin_cases r <;> simp [headerStore,nodeCheckHeaderRoles,parsed,readStore,rest,extraWork,status,List.append_assoc]
  rw [readEq] at headerRun
  have combined:=combineFlags_executes 33 1 readStore accepted true tail (by simp [readStore])
  let ready:=Function.update readStore 1 (accepted::tail)
  have combinedRun : Executes (ofProgram (combineFlagsProgram 33 1)) readStore 3 ready:=by
    simpa only [Bool.and_true] using combined
  have compared:=distinctGuard_executes 29 referenceParentRoles ready accepted tail
    (by simp [referenceParentRoles,ready]) (by simp [referenceParentRoles,ready,readStore,work])
    (by simp [referenceParentRoles,ready,readStore,work]) (by simp [referenceParentRoles,ready,readStore,work])
  have predicate : (!decide (ready (referenceParentRoles 0)=ready (referenceParentRoles 1)))=decide (node.parent≠some target):=by
    change (!decide (ready 22=ready 24))=decide (node.parent≠some target)
    have first : ready 22=(parentCode node).bits:=by simp [ready,readStore]
    have second : ready 24=(target+1).bits:=by simp [ready,readStore,targetPlus]
    rw [first,second]
    simp only [Encoding.bits_injective.eq_iff,←decide_not,parentCode_ne_iff]
  rw [predicate] at compared
  let parentAccepted:=accepted && decide (node.parent≠some target)
  let checked:=Function.update ready 1 (parentAccepted::tail)
  have clearingLevel:=clear_executes (21:Fin 35) checked
  have levelValue : checked 21=node.level.bits:=by simp [checked,ready,readStore]
  rw [levelValue,Encoding.bits_length] at clearingLevel
  let noLevel:=Function.update checked 21 []
  have clearingParent:=clear_executes (22:Fin 35) noLevel
  have parentValue : noLevel 22=(parentCode node).bits:=by simp [noLevel,checked,ready,readStore]
  rw [parentValue,Encoding.bits_length] at clearingParent
  let noParent:=Function.update noLevel 22 []
  have clearingLeader:=clear_executes (23:Fin 35) noParent
  have leaderValue : noParent 23=[node.leader]:=by simp [noParent,noLevel,checked,ready,readStore]
  rw [leaderValue] at clearingLeader
  let clean:=Function.update noParent 23 []
  have skipping:=FieldAccess.skip_executes 33 28 clean
  have degreeWord : clean 28=Encoding.frame node.degree.bits++rest:=by simp [clean,noParent,noLevel,checked,ready,readStore,Encoding.natural]
  rw [degreeWord,FieldAccess.skipCost_frame,FieldAccess.skipRest_frame,Encoding.bits_length] at skipping
  let incomingStore:=Function.update clean 28 rest
  have incomingWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : incomingStore r=[]:=by
    have n21 : r≠21:=by intro eq;subst r;norm_num at small
    have n22 : r≠22:=by intro eq;subst r;norm_num at small
    have n23 : r≠23:=by intro eq;subst r;norm_num at small
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    simp [incomingStore,clean,noParent,noLevel,checked,ready,readStore,ne,n21,n22,n23,n28,work r small ne]
  obtain ⟨incomingTime,incomingBound,incomingRun⟩:=referenceIncoming_executes incomingStore parentAccepted tail
    (by simp [incomingStore,clean,noParent,noLevel,checked]) incomingWork
    (by simp [incomingStore,clean,noParent])
    (by simp [incomingStore,clean,noParent,noLevel,checked,ready,readStore,extraWork])
    (by simp [incomingStore,clean,noParent,noLevel,checked,ready,readStore,extraWork]) target
    (by simp [incomingStore,clean,noParent,noLevel,checked,ready,readStore,targetCode]) node.incoming suffix
    (by simp [incomingStore,rest])
  have final : referencePrefixStore incomingStore parentAccepted tail target node.incoming suffix=
      referenceNodeStore store accepted tail target node suffix:=by
    funext r
    fin_cases r <;> simp [referencePrefixStore,referenceNodeStore,noNodeReference,incomingStore,clean,noParent,
      noLevel,checked,ready,readStore,parentAccepted,extraWork,Bool.and_assoc]
  rw [final] at incomingRun
  have first : ready (referenceParentRoles 0)=(parentCode node).bits:=by simp [referenceParentRoles,ready,readStore]
  have second : ready (referenceParentRoles 1)=(target+1).bits:=by simp [referenceParentRoles,ready,readStore,targetPlus]
  have compareBound:=Compare.preservingCost_le (ready (referenceParentRoles 0)) (ready (referenceParentRoles 1))
  rw [first,second,Encoding.bits_length,Encoding.bits_length] at compareBound
  have successorSize : (target+1).size≤target.size+1:=by
    have bound:=increment_length_le target.bits
    simpa only [Machine.increment_bits,Encoding.bits_length] using bound
  have fields:=node_metadata_size_le node
  have restBound : rest.length≤(store 28).length:=by
    rw [input]
    have small:=nodeSuffix_length_le node
    have restSmall : rest.length≤(nodeSuffix node).length+suffix.length:=by
      simp only [rest,nodeSuffix,List.length_append]
      omega
    simp only [List.length_append]
    omega
  have degreeBound : node.degree.size≤(store 28).length:=by
    rw [input]
    have small:=nodeSuffix_length_le node
    have degree : node.degree.size≤(nodeSuffix node).length:=by simp only [nodeSuffix,List.length_append,Encoding.natural_length];omega
    simp only [List.length_append]
    omega
  have nodeBound : (Encoding.node.encode node).length≤(store 28).length:=by rw [input,List.length_append];omega
  have incomingSource : incomingStore 28=rest:=by simp [incomingStore]
  rw [incomingSource] at incomingBound
  have incomingLimit : incomingTime≤2000*((store 28).length+target.size+1)^3:=by apply incomingBound.trans;gcongr
  change headerTime≤6*(store 28).length+17 at headerBound
  have linear:=Nat.le_self_pow (by decide : 3≠0) ((store 28).length+target.size+1)
  refine ⟨_,?_,headerRun.sequence (combinedRun.sequence (compared.sequence (clearingLevel.sequence
    (clearingParent.sequence (clearingLeader.sequence (skipping.sequence incomingRun))))))⟩
  rw [first,second]
  simp only [List.length_cons,List.length_nil]
  omega

end Counting.StackMachine.DagValidation
