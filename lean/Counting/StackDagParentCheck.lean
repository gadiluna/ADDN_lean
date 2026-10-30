import Counting.StackDagPrepareParent
import Counting.StackDagParentLookup

/-! Binary-parent references are converted under the current-index budget,
then used for actual serialized access. Invalid references still terminate
within the same bound and yield a false accumulated status. Canonical node
encoding is a precondition supplied by the separate parser, not inferred. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def binaryParentCheck : Routine 26:=sequence prepareParent parentLookup

def parentCheck (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Bool:=
  match node.parent with
  | none=>false
  | some p=>p < current && (values[p]?.getD default).level+1==node.level &&
      (values[p]?.getD default).leader==node.leader

def selectedParent (values : List Executable.Node) (current : Nat) (node : Executable.Node)
    (inside : current<values.length) : Fin values.length:=
  ⟨min (parentCode node) current-1,by omega⟩

theorem selectedParent_condition (values : List Executable.Node) (current : Nat)
    (node : Executable.Node) (inside : current<values.length) :
    (decide (parentCode node≤current) &&
      parentCondition current node values[selectedParent values current node inside])=
      parentCheck values current node := by
  cases reference : node.parent with
  | none=>simp [parentCheck,parentCondition,parentCode,reference]
  | some p=>
    by_cases before : p<current
    · have fits : p+1≤current:=by omega
      have bounded : p<values.length:=by omega
      have selected : selectedParent values current node inside=⟨p,bounded⟩:=by
        apply Fin.ext
        simp [selectedParent,parentCode,reference,Nat.min_eq_left fits]
      simp [selected,parentCheck,parentCondition,parentCode,reference,fits,before,bounded]
    · have bad : ¬p+1≤current:=by omega
      simp [parentCheck,parentCondition,parentCode,reference,bad,before]

def binaryParentStore (store : Store 26) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current : Nat) (node : Executable.Node)
    (inside : current<values.length) : Store 26:=
  Function.update (lookupStore (prepareParentStore store accepted tail (parentCode node))
    values[selectedParent values current node inside]) 1 ((accepted && parentCheck values current node)::tail)

theorem binaryParentCheck_executes (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 28,r∈({18,19,20,26}:Finset (Fin 28)) → store r=[])
    (values : List Executable.Node) (current : Nat) (node : Executable.Node)
    (inside : current<values.length) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (level : store 21=node.level.bits) (reference : store 22=(parentCode node).bits)
    (leader : store 23=[node.leader]) (currentIndex : store 24=current.bits)
    (budget : (store 25).length=current) :
    ∃ time ≤ 100*(current+2*(parentCode node).size+2)^3+
      (2*current+3)*2029*((store 17).length+1)^3+6*(store 17).length+7*current+
      6*(Encoding.node.encode values[selectedParent values current node inside]).length+38+
      100*((parentCode node).size+current.size+
        values[selectedParent values current node inside].level.size+node.level.size+3),
      Executes binaryParentCheck store time (binaryParentStore store accepted tail values current node inside) := by
  have preparedWork (r : Fin 28) (member : r∈({0,2,3,4,5,6,7,18,20,26}:Finset (Fin 28))) : store r=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact work _ (by decide) (by decide) | exact extraWork _ (by decide)
  obtain ⟨prepareTime,prepareBound,preparedRun⟩:=prepareParent_executes store accepted tail status
    (parentCode node) reference preparedWork
  rw [budget] at prepareBound
  let prepared:=prepareParentStore store accepted tail (parentCode node)
  let selected:=selectedParent values current node inside
  let ok:=decide (parentCode node≤current)
  have preparedStatus : prepared 1=(accepted && ok)::tail:=by simp [prepared,prepareParentStore,budget,ok]
  have preparedEmpty (r : Fin 28) (small : r.val<17) (ne : r≠1) : prepared r=[] := by
    have ne18 : r≠18:=by intro eq;subst r;norm_num at small
    have ne25 : r≠25:=by intro eq;subst r;norm_num at small
    simp [prepared,prepareParentStore,ne,ne18,ne25,work r small ne]
  have preparedOutput : prepared 19=[]:=by simp [prepared,prepareParentStore,extraWork 19 (by decide)]
  have preparedSource : prepared 17=Encoding.sequence Encoding.node values++suffix:=by
    simp [prepared,prepareParentStore,source]
  have preparedIndex : (prepared 18).length=selected.val:=by
    simp [prepared,prepareParentStore,selected,selectedParent,budget]
  obtain ⟨lookupTime,lookupBound,lookupRun⟩:=parentLookup_get prepared (accepted && ok) tail preparedStatus
    preparedEmpty preparedOutput values selected suffix preparedSource preparedIndex current node
    (by simp [prepared,prepareParentStore,level]) (by simp [prepared,prepareParentStore,reference])
    (by simp [prepared,prepareParentStore,leader]) (by simp [prepared,prepareParentStore,currentIndex])
  have acceptance : ((accepted && ok) && parentCondition current node values[selected])=
      (accepted && parentCheck values current node) := by
    rw [Bool.and_assoc]
    exact congrArg (accepted && ·) (selectedParent_condition values current node inside)
  rw [acceptance] at lookupRun
  have lengthBound : (prepared 18).length≤current:=by rw [preparedIndex];dsimp [selected,selectedParent];omega
  have sourceSame : prepared 17=store 17:=by simp [prepared,prepareParentStore]
  rw [sourceSame] at lookupBound
  refine ⟨prepareTime+1+lookupTime,?_,preparedRun.sequence lookupRun⟩
  have mon : (2*(prepared 18).length+3)*2029*((store 17).length+1)^3≤
      (2*current+3)*2029*((store 17).length+1)^3 := by gcongr
  dsimp only [selected] at lookupBound
  omega

/-- The semantic result is precisely the parent factor of the executable
node validator, including the rejection of absent and forward references. -/
theorem parentCheck_vista (vista : Executable.Vista) (current : Nat) :
    parentCheck vista.nodes.toList current (vista.node current)=
      match (vista.node current).parent with
      | none=>false
      | some p=>p<current && (vista.node p).level+1==(vista.node current).level &&
          (vista.node p).leader==(vista.node current).leader := by
  simp [parentCheck,Executable.Vista.node]

end Counting.StackMachine.DagValidation
