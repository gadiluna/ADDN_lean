import Counting.StackDagParentBounds
import Counting.StackDagSourceLevel

/-! Actual red-reference validation: binary index, bounded access to the
serialized source node, and successor-level comparison. The bound rejects
forward references, including huge indices, without numeric expansion.
Multiplicity positivity and sortedness are separate incoming-list checks. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def redReferenceCheck : Routine 26:=
  sequence (incrementRoutine 25 20 22 26) (sequence prepareParent sourceLevelLookup)

def redCondition (values : List Executable.Node) (current targetLevel sourceIndex : Nat) : Bool:=
  sourceIndex<current && (values[sourceIndex]?.getD default).level+1==targetLevel

def selectedRed (values : List Executable.Node) (current sourceIndex : Nat)
    (inside : current<values.length) : Fin values.length:=
  ⟨min (sourceIndex+1) current-1,by omega⟩

theorem selectedRed_condition (values : List Executable.Node) (current targetLevel sourceIndex : Nat)
    (inside : current<values.length) :
    (decide (sourceIndex+1≤current) &&
      decide (values[selectedRed values current sourceIndex inside].level+1=targetLevel))=
      redCondition values current targetLevel sourceIndex := by
  by_cases before : sourceIndex<current
  · have fits : sourceIndex+1≤current:=by omega
    have bounded : sourceIndex<values.length:=by omega
    have selected : selectedRed values current sourceIndex inside=⟨sourceIndex,bounded⟩:=by
      apply Fin.ext
      simp [selectedRed,Nat.min_eq_left fits]
    apply Bool.eq_iff_iff.mpr
    simp [selected,redCondition,fits,before,bounded]
  · have bad : ¬sourceIndex+1≤current:=by omega
    simp [redCondition,bad,before]

def redReferenceStore (store : Store 26) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current targetLevel sourceIndex : Nat)
    (inside : current<values.length) : Store 26:=
  Function.update (lookupStore (prepareParentStore (Function.update store 22 (sourceIndex+1).bits)
    accepted tail (sourceIndex+1)) values[selectedRed values current sourceIndex inside]) 1
    ((accepted && redCondition values current targetLevel sourceIndex)::tail)

theorem redReferenceCheck_executes (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 28,r∈({18,19,20,26}:Finset (Fin 28)) → store r=[])
    (values : List Executable.Node) (current targetLevel sourceIndex : Nat)
    (inside : current<values.length) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (level : store 21=targetLevel.bits) (reference : store 22=sourceIndex.bits)
    (budget : (store 25).length=current) :
    ∃ time ≤ 4*sourceIndex.size+9+100*(current+2*(sourceIndex+1).size+2)^3+
      (2*current+3)*2029*((store 17).length+1)^3+6*(store 17).length+7*current+
      6*(Encoding.node.encode values[selectedRed values current sourceIndex inside]).length+72+
      16*values[selectedRed values current sourceIndex inside].level.size+6*targetLevel.size,
      Executes redReferenceCheck store time
        (redReferenceStore store accepted tail values current targetLevel sourceIndex inside) := by
  obtain ⟨incrementTime,incrementBound,incrementedRun⟩:=increment_natural 25 20 22 26
    (by decide) (by decide) (by decide) store
    (extraWork 20 (by decide)) (extraWork 26 (by decide)) sourceIndex reference
  let incremented:=Function.update store 22 (sourceIndex+1).bits
  have preparedWork (r : Fin 28) (member : r∈({0,2,3,4,5,6,7,18,20,26}:Finset (Fin 28))) : incremented r=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [incremented,work,extraWork]
  obtain ⟨prepareTime,prepareBound,preparedRun⟩:=prepareParent_executes incremented accepted tail
    (by simp [incremented,status]) (sourceIndex+1) (by simp [incremented]) preparedWork
  have incrementedBudget : (incremented 25).length=current:=by simp [incremented,budget]
  rw [incrementedBudget] at prepareBound
  let prepared:=prepareParentStore incremented accepted tail (sourceIndex+1)
  let selected:=selectedRed values current sourceIndex inside
  let ok:=decide (sourceIndex+1≤current)
  have preparedStatus : prepared 1=(accepted && ok)::tail:=by
    simp [prepared,prepareParentStore,incremented,budget,ok]
  have preparedEmpty (r : Fin 28) (small : r.val<17) (ne : r≠1) : prepared r=[] := by
    have ne18 : r≠18:=by intro eq;subst r;norm_num at small
    have ne22 : r≠22:=by intro eq;subst r;norm_num at small
    have ne25 : r≠25:=by intro eq;subst r;norm_num at small
    simp [prepared,prepareParentStore,incremented,ne,ne18,ne22,ne25,work r small ne]
  have preparedOutput : prepared 19=[]:=by
    simp [prepared,prepareParentStore,incremented,extraWork 19 (by decide)]
  have preparedSource : prepared 17=Encoding.sequence Encoding.node values++suffix:=by
    simp [prepared,prepareParentStore,incremented,source]
  have preparedIndex : (prepared 18).length=selected.val:=by
    simp [prepared,prepareParentStore,incremented,selected,selectedRed,budget]
  obtain ⟨lookupTime,lookupBound,lookupRun⟩:=sourceLevelLookup_get prepared (accepted && ok) tail
    preparedStatus preparedEmpty preparedOutput values selected suffix preparedSource preparedIndex targetLevel
    (by simp [prepared,prepareParentStore,incremented,level])
  have acceptance : ((accepted && ok) && decide (values[selected].level+1=targetLevel))=
      (accepted && redCondition values current targetLevel sourceIndex) := by
    rw [Bool.and_assoc]
    exact congrArg (accepted && ·) (selectedRed_condition values current targetLevel sourceIndex inside)
  rw [acceptance] at lookupRun
  have lengthBound : (prepared 18).length≤current:=by rw [preparedIndex];dsimp [selected,selectedRed];omega
  have sourceSame : prepared 17=store 17:=by simp [prepared,prepareParentStore,incremented]
  rw [sourceSame] at lookupBound
  refine ⟨incrementTime+1+(prepareTime+1+lookupTime),?_,incrementedRun.sequence (preparedRun.sequence lookupRun)⟩
  have mon : (2*(prepared 18).length+3)*2029*((store 17).length+1)^3≤
      (2*current+3)*2029*((store 17).length+1)^3 := by gcongr
  dsimp only [selected] at lookupBound
  omega

end Counting.StackMachine.DagValidation
