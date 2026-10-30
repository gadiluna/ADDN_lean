import Counting.StackDagIncomingFull
import Counting.StackDagParentClean
import Counting.StackFrameSkip

/-! The noninitial branch of the actual node validator. Parent and source
references are read from the same serialized node table. All copying,
degree-field skipping and workspace cleanup occur in the stack program. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def positiveParentRoles : Fin 28 ↪ Fin 35 where
  toFun r:=⟨r.val,by have:=r.isLt;omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 35=>r.val) equal

def positiveNodeRoutine : Routine 33:=
  sequence (ofProgram (ListPrograms.copyProgram 32 29 25 4))
    (sequence (mapRegisters positiveParentRoles parentReferenceClean)
      (sequence (ofProgram (FieldAccess.skipProgram 33 28)) fullIncomingPrefix))

def positiveNodeCondition (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Bool:=
  parentCheck values current node && incomingCondition values current node.level node.incoming

def positiveNodeStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Store 33:=
  Function.update (Function.update (Function.update store 22 []) 28 []) 1
    ((accepted && positiveNodeCondition values current node)::tail)

theorem positiveNode_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,25,26,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (level : store 21=node.level.bits) (reference : store 22=(parentCode node).bits)
    (leader : store 23=[node.leader]) (currentBits : store 24=current.bits) (budget : (store 29).length=current)
    (input : store 28=nodeSuffix node) :
    ∃ time ≤ 900000*((store 17).length+(Encoding.node.encode node).length+current.size+1)^5,
      Executes positiveNodeRoutine store time (positiveNodeStore store accepted tail values current node) := by
  have copied:=copy_executes 32 29 25 4 (by decide) (by decide) (by decide) store
    (work 4 (by decide) (by decide))
  rw [extraWork 25 (by decide),List.append_nil] at copied
  let ready:=Function.update store 25 (store 29)
  let localStore : Store 26:=ready ∘ positiveParentRoles
  have localWork (r : Fin 28) (small : r.val<17) (ne : r≠1) : localStore r=[]:=by
    have n1 : positiveParentRoles r≠1:=by intro eq;apply ne;apply Fin.ext;exact congrArg (fun r:Fin 35=>r.val) eq
    have n25 : positiveParentRoles r≠25:=by intro eq;have:=congrArg (fun r:Fin 35=>r.val) eq;dsimp [positiveParentRoles] at this;omega
    simp [localStore,ready,n25,work _ small n1]
  have localExtra (r : Fin 28) (member : r∈({18,19,20,26}:Finset (Fin 28))) : localStore r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl
    all_goals simp [localStore,ready,positiveParentRoles,extraWork]
  obtain ⟨parentTime,parentBound,parentRun⟩:=parentReferenceClean_executes localStore accepted tail
    (by simp [localStore,ready,positiveParentRoles,status]) localWork localExtra values current node inside sourceSuffix
    (by simp [localStore,ready,positiveParentRoles,source])
    (by simp [localStore,ready,positiveParentRoles,level])
    (by simp [localStore,ready,positiveParentRoles,reference])
    (by simp [localStore,ready,positiveParentRoles,leader])
    (by simp [localStore,ready,positiveParentRoles,currentBits])
    (by simp [localStore,ready,positiveParentRoles,budget])
  let parentFlag:=accepted && parentCheck values current node
  let checked:=Function.update (Function.update store 22 []) 1 (parentFlag::tail)
  have relocated : Executes (mapRegisters positiveParentRoles parentReferenceClean) ready parentTime checked:=by
    apply relocate_executes_frame parentReferenceClean positiveParentRoles ready checked localStore
      (parentCleanStore localStore accepted tail values current node) parentTime rfl _ _ parentRun
    · intro r
      fin_cases r <;> simp [checked,parentCleanStore,localStore,ready,positiveParentRoles,parentFlag,extraWork]
    · intro r outside
      have n1 : r≠1:=by intro eq;subst r;exact outside 1 rfl
      have n22 : r≠22:=by intro eq;subst r;exact outside 22 rfl
      have n25 : r≠25:=by intro eq;subst r;exact outside 25 rfl
      simp [checked,ready,n1,n22,n25]
  have checkedInput : checked 28=Encoding.frame node.degree.bits++
      (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming:=by
    simpa [checked,nodeSuffix,Encoding.natural] using input
  have skipped:=FieldAccess.skip_executes 33 28 checked
  rw [checkedInput,FieldAccess.skipCost_frame,FieldAccess.skipRest_frame,Encoding.bits_length] at skipped
  let incomingWord:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming
  let middle:=Function.update checked 28 incomingWord
  have middleWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : middle r=[]:=by
    have n22 : r≠22:=by intro eq;subst r;norm_num at small
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    simp [middle,checked,ne,n22,n28,work r small ne]
  have middleExtra (r : Fin 35) (member : r∈({18,19,20,22,25,26,30,31,32,33,34}:Finset (Fin 35))) : middle r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [middle,checked,extraWork]
  obtain ⟨incomingTime,incomingBound,incomingRun⟩:=fullIncomingPrefix_executes middle parentFlag tail
    (by simp [middle,checked]) middleWork middleExtra values current node.level inside sourceSuffix
    (by simp [middle,checked,source]) (by simp [middle,checked,level])
    (by simp [middle,checked,currentBits]) (by simp [middle,checked,budget]) node.incoming []
    (by simp [middle,incomingWord])
  have final : fullIncomingStore middle parentFlag tail values current node.level node.incoming []=
      positiveNodeStore store accepted tail values current node:=by
    funext r
    by_cases r1 : r=1
    · subst r;simp [fullIncomingStore,positiveNodeStore,parentFlag,positiveNodeCondition,Bool.and_assoc]
    · by_cases r28 : r=28
      · subst r;simp [fullIncomingStore,positiveNodeStore]
      · simp [fullIncomingStore,positiveNodeStore,middle,checked,r1,r28]
  rw [final] at incomingRun
  have parentSource : localStore 17=store 17:=by simp [localStore,ready,positiveParentRoles]
  rw [parentSource] at parentBound
  have middleSource : middle 17=store 17:=by simp [middle,checked]
  have middleInput : middle 28=incomingWord:=by simp [middle]
  rw [middleSource,middleInput] at incomingBound
  have currentBound : current≤(store 17).length:=by
    have count:=node_sequence_count_le values
    rw [source,List.length_append]
    omega
  have suffixSize:=nodeSuffix_length_le node
  have nodeFields:=node_metadata_size_le node
  have incomingSize : incomingWord.length≤(Encoding.node.encode node).length:=by
    have length : incomingWord.length≤(nodeSuffix node).length:=by
      simp [nodeSuffix,incomingWord]
    exact length.trans suffixSize
  have degreeSize : node.degree.size≤(Encoding.node.encode node).length:=by
    have length : node.degree.size≤(nodeSuffix node).length:=by
      simp [nodeSuffix,Encoding.natural_length]
      omega
    exact length.trans suffixSize
  let S:=(store 17).length+(Encoding.node.encode node).length+current.size+1
  have positiveS : 1≤S:=by dsimp [S];omega
  have parentLimit : parentTime≤10020*S^4:=by apply parentBound.trans;gcongr;dsimp [S];omega
  have incomingLimit : incomingTime≤832000*S^5:=by
    have base : (store 17).length+incomingWord.length+node.level.size+current.size+1≤2*S:=by dsimp [S];omega
    calc
      incomingTime≤26000*(2*S)^5:=incomingBound.trans (by gcongr)
      _=832000*S^5:=by ring
  have fourth : S^4≤S^5:=Nat.pow_le_pow_right positiveS (by decide)
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have indexS : current≤S:=by dsimp [S];omega
  have degreeS : node.degree.size≤S:=by dsimp [S];omega
  refine ⟨_,?_,copied.sequence (relocated.sequence (skipped.sequence incomingRun))⟩
  rw [budget]
  change (5*current+2)+1+(parentTime+1+(2*node.degree.size+1+1+incomingTime))≤900000*S^5
  omega

theorem positiveNodeCondition_vista (vista : Executable.Vista) (current : Nat)
    (noninitial : (vista.node current).level≠0) :
    positiveNodeCondition vista.nodes.toList current (vista.node current)=Executable.nodeValid vista current := by
  rw [positiveNodeCondition,parentCheck_vista,incomingCondition_vista]
  unfold Executable.nodeValid
  simp only [beq_iff_eq,noninitial,↓reduceIte]
  cases (vista.node current).parent <;> simp [Bool.and_assoc]

end Counting.StackMachine.DagValidation
