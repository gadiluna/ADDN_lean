import Counting.StackDagSelectedHeader
import Counting.StackDagParentFields
import Counting.StackEncodingRelabel

/-! A charged parent lookup and comparison. The input carries the current
node's extracted fields and a bounded unary parent index. The source is a
serialized node sequence; the parent fields are obtained by scanning it.
The separate bounded conversion theorem supplies the unary index from the
actual optional-parent field. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def lookupReadRoles : Fin 20 ↪ Fin 28 where
  toFun r:=⟨r.val,by have:=r.isLt;omega⟩
  inj':=by intro a b eq;apply Fin.ext;exact congrArg (fun r:Fin 28=>r.val) eq

def lookupFieldRoles : Fin 11 ↪ Fin 28:=⟨![22,24,0,21,3,23,1,4,5,6,7],by decide⟩

def parentLookup : Routine 26:=
  sequence (mapRegisters lookupReadRoles selectedHeader)
    (mapRegisters lookupFieldRoles parentFieldsRoutine)

def lookupStore (store : Store 26) (parent : Executable.Node) : Store 26:=
  fun r=>if r=19 then nodeSuffix parent else if r=0 then parent.level.bits
    else if r=2 then (parentCode parent).bits else if r=3 then [parent.leader] else store r

theorem lookupRead_get (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (output : store 19=[]) (values : List Executable.Node) (parent : Fin values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (index : (store 18).length=parent.val) :
    ∃ time ≤ (2*(store 18).length+3)*2029*((store 17).length+1)^3+
        6*(store 17).length+7*(store 18).length+6*(Encoding.node.encode values[parent]).length+36,
      Executes (mapRegisters lookupReadRoles selectedHeader) store time (lookupStore store values[parent]) := by
  let localStore : Store 18:=store ∘ lookupReadRoles
  have localWork (r : Fin 17) (ne : r≠1) : localStore (DagParser.nodeRoles r)=[] := by
    apply work
    · exact r.isLt
    · intro eq
      apply ne
      apply Fin.ext
      exact congrArg (fun x:Fin 28=>x.val) eq
  obtain ⟨time,bounded,executed⟩:=selectedHeader_get localStore accepted tail status localWork output
    values parent suffix source index
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame selectedHeader lookupReadRoles store (lookupStore store values[parent])
    localStore (selectedHeaderStore localStore values[parent]) time rfl _ _ executed
  · intro r
    fin_cases r <;> simp [lookupStore,selectedHeaderStore,lookupReadRoles,localStore,Function.comp_apply]
  · intro r outside
    have n0 : r≠0:=by intro eq;subst r;exact outside 0 rfl
    have n2 : r≠2:=by intro eq;subst r;exact outside 2 rfl
    have n3 : r≠3:=by intro eq;subst r;exact outside 3 rfl
    have n19 : r≠19:=by intro eq;subst r;exact outside 19 rfl
    simp [lookupStore,n0,n2,n3,n19]

theorem parentLookup_get (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (output : store 19=[]) (values : List Executable.Node) (parent : Fin values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (index : (store 18).length=parent.val) (current : Nat) (node : Executable.Node)
    (level : store 21=node.level.bits) (reference : store 22=(parentCode node).bits)
    (leader : store 23=[node.leader]) (currentIndex : store 24=current.bits) :
    ∃ time ≤ (2*(store 18).length+3)*2029*((store 17).length+1)^3+
        6*(store 17).length+7*(store 18).length+6*(Encoding.node.encode values[parent]).length+37+
        100*((parentCode node).size+current.size+values[parent].level.size+node.level.size+3),
      Executes parentLookup store time
        (Function.update (lookupStore store values[parent]) 1
          ((accepted && parentCondition current node values[parent])::tail)) := by
  obtain ⟨readTime,readBound,readRun⟩:=lookupRead_get store accepted tail status work output
    values parent suffix source index
  let parsed:=lookupStore store values[parent]
  let localStore : Store 9:=parsed ∘ lookupFieldRoles
  have localStatus : localStore 6=accepted::tail:=by simp [localStore,parsed,lookupStore,lookupFieldRoles,status]
  have localWork (r : Fin 11) (inside : 7≤r.val) : localStore r=[] := by
    fin_cases r <;> norm_num at inside
    all_goals simp [localStore,parsed,lookupStore,lookupFieldRoles,work]
  have check : parentFieldsCheck localStore=parentCondition current node values[parent] := by
    have h:=parentFieldsCheck_typed current node values[parent]
    simpa [parentFieldsCheck,parentInput,localStore,parsed,lookupStore,lookupFieldRoles,reference,
      currentIndex,level,leader] using h
  have fields:=parentFields_executes localStore accepted tail localStatus localWork
  rw [check] at fields
  let target:=Function.update parsed 1 ((accepted && parentCondition current node values[parent])::tail)
  have relocated : Executes (mapRegisters lookupFieldRoles parentFieldsRoutine) parsed
      (parentFieldsCost localStore) target := by
    apply relocate_executes_frame parentFieldsRoutine lookupFieldRoles parsed target localStore
      (Function.update localStore 6 ((accepted && parentCondition current node values[parent])::tail))
      (parentFieldsCost localStore) rfl _ _ fields
    · intro r
      fin_cases r <;> simp [target,localStore,lookupFieldRoles]
    · intro r outside
      have ne : r≠1:=by intro eq;subst r;exact outside 6 rfl
      simp [target,ne]
  have fieldBound : parentFieldsCost localStore ≤
      100*((parentCode node).size+current.size+values[parent].level.size+node.level.size+3) := by
    simpa [localStore,lookupFieldRoles,parsed,lookupStore,reference,currentIndex,level,leader,Encoding.bits_length]
      using parentFieldsCost_le localStore
  refine ⟨readTime+1+parentFieldsCost localStore,?_,readRun.sequence relocated⟩
  omega

end Counting.StackMachine.DagValidation
