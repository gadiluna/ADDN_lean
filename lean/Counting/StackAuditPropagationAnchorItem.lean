import Counting.StackAuditPropagationSelect
import Counting.StackAuditPropagationAvailable

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def anchorSelectRoles : Fin 32 ↪ Fin 37 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 37=>r.val) equal)⟩

abbrev anchorChoice : Routine 35 := sequence (relocate selectedLevel anchorSelectRoles)
  (branchRoutine 31 assignAvailable (skip 35))

abbrev anchorItem : Routine 35 := sequence anchorChoice (pushBit 18 true)

def chosenValues (node : Executable.Node) (anchor : Nat) (values : List Nat) : List Nat :=
  if node.level=anchor then availableValues values else values

def chosenWeights (node : Executable.Node) (anchor : Nat) (weights : Array Nat) (index : Nat)
    (values : List Nat) : Array Nat :=
  if node.level=anchor then availableWeights weights index values else weights

def choiceStore (store : Store 35) (node : Executable.Node) (anchor : Nat)
    (weights : Array Nat) (index : Nat) (values : List Nat) : Store 35 :=
  Function.update (Function.update store 36 (Encoding.sequence Encoding.natural (chosenValues node anchor values))) 35
    ((Encoding.array Encoding.natural).encode (chosenWeights node anchor weights index values))

/-- One actual physical-node iteration of anchor assignment. The indexed
header is read from the serialized DAG, its binary level is compared, and
only a selected node consumes an available coordinate. -/
theorem anchorChoice_executes (store : Store 35) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 37,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e21 : store 21=[]) (e31 : store 31=[])
    (nodes : List Executable.Node) (index : Fin nodes.length) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : store 18=List.replicate index.val true)
    (anchor : Nat) (query : store 30=anchor.bits)
    (weights : Array Nat) (inside : index.val<weights.size)
    (array : store 35=(Encoding.array Encoding.natural).encode weights)
    (values : List Nat) (source : store 36=Encoding.sequence Encoding.natural values) :
    ∃ time ≤ 8000*((store 17).length+anchor.size+1)^4+
      5*(store 35).length+8*index.val+22*(store 36).length+42,
      Executes anchorChoice store time (choiceStore store nodes[index] anchor weights index.val values) := by
  let localStore : Store 30 := store ∘ anchorSelectRoles
  have localWork (r : Fin 32) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    apply work (anchorSelectRoles r) small
    intro equal;apply different
    exact Fin.ext (congrArg (fun i:Fin 37=>i.val) equal)
  obtain ⟨readTime,readBound,read⟩ := selectedLevel_executes localStore accepted tail status localWork e19
    nodes index suffix input (by change (store 18).length=index.val;rw [counter,List.length_replicate]) anchor query
  let flagged := Function.update store 31 [decide (nodes[index].level=anchor)]
  have a : Executes (relocate selectedLevel anchorSelectRoles) store readTime flagged := by
    apply relocate_executes_frame selectedLevel anchorSelectRoles _ _ _ _ readTime rfl _ _ read
    · intro r;fin_cases r <;> simp [flagged,localStore,anchorSelectRoles,e31]
    · intro r outside
      have n31 : r≠31 := by intro equal;subst r;exact outside 31 rfl
      simp [flagged,n31]
  have restored : Function.update flagged 31 []=store := by
    simp only [flagged,Function.update_idem]
    rw [←e31,Function.update_eq_self]
  by_cases selected : nodes[index.val].level=anchor
  · obtain ⟨time,bounded,body⟩ := assignAvailable_executes store weights index.val inside values source array counter
      (work _ (by decide) (by decide)) (work _ (by decide) (by decide))
      (work _ (by decide) (by decide)) e21 e31
    have result : Function.update (Function.update store 36 (Encoding.sequence Encoding.natural (availableValues values))) 35
        ((Encoding.array Encoding.natural).encode (availableWeights weights index.val values))=
        choiceStore store nodes[index] anchor weights index.val values := by
      simp [choiceStore,chosenValues,chosenWeights,selected]
    rw [result] at body
    have ready : Executes assignAvailable (Function.update flagged 31 []) time
        (choiceStore store nodes[index] anchor weights index.val values) := by
      rw [restored];exact body
    have b := branch_executes_true (31:Fin 37) assignAvailable (skip 35) flagged _ [] time
      (by simp [flagged,selected]) ready
    refine ⟨_,?_,a.sequence b⟩
    change readTime ≤ 8000*((store 17).length+anchor.size+1)^4 at readBound
    omega
  · have body : Executes (skip 35) (Function.update flagged 31 []) 0 store := by
      rw [restored];exact skip_executes store
    have b := branch_executes_false (31:Fin 37) assignAvailable (skip 35) flagged store [] 0
      (by simp [flagged,selected]) body
    have result : choiceStore store nodes[index] anchor weights index.val values=store := by
      simp only [choiceStore,chosenValues,chosenWeights,Fin.getElem_fin,selected,if_false]
      rw [←source,Function.update_eq_self,←array,Function.update_eq_self]
    rw [result]
    refine ⟨_,?_,a.sequence b⟩
    change readTime ≤ 8000*((store 17).length+anchor.size+1)^4 at readBound
    omega

theorem anchorItem_executes (store : Store 35) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 37,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e21 : store 21=[]) (e31 : store 31=[])
    (nodes : List Executable.Node) (index : Fin nodes.length) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : store 18=List.replicate index.val true)
    (anchor : Nat) (query : store 30=anchor.bits)
    (weights : Array Nat) (inside : index.val<weights.size)
    (array : store 35=(Encoding.array Encoding.natural).encode weights)
    (values : List Nat) (source : store 36=Encoding.sequence Encoding.natural values) :
    ∃ time ≤ 9000*((store 17).length+(store 35).length+(store 36).length+anchor.size+index.val+1)^4,
      Executes anchorItem store time
        (Function.update (choiceStore store nodes[index] anchor weights index.val values) 18
          (List.replicate (index.val+1) true)) := by
  obtain ⟨time,bounded,a⟩ := anchorChoice_executes store accepted tail status work e19 e21 e31
    nodes index suffix input counter anchor query weights inside array values source
  have b := pushBit_executes (18:Fin 37) true (choiceStore store nodes[index] anchor weights index.val values)
  have countAt : choiceStore store nodes[index] anchor weights index.val values 18=List.replicate index.val true := by
    simp [choiceStore,counter]
  rw [countAt,←List.replicate_succ] at b
  refine ⟨_,?_,a.sequence b⟩
  let size := (store 17).length+(store 35).length+(store 36).length+anchor.size+index.val+1
  have raised : ((store 17).length+anchor.size+1)^4 ≤ size^4 := Nat.pow_le_pow_left (by dsimp only [size];omega) 4
  have linear : size ≤ size^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ size^4 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  have s1 : (store 35).length ≤ size := by dsimp only [size];omega
  have s2 : (store 36).length ≤ size := by dsimp only [size];omega
  have s3 : index.val ≤ size := by dsimp only [size];omega
  change _ ≤ 9000*size^4
  omega

end Counting.StackMachine.AuditPropagation
