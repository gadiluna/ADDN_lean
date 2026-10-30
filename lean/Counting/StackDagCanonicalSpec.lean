import Counting.DagCanonicalRecordsSpec
import Counting.DagSemanticsCanonical
import Counting.DagCanonicalBounds

namespace Counting.StackMachine.DagUpdate.Canonical
open Executable

/-- Canonicalization interns an already remapped signature, then writes
its result into the original node's mapping slot. -/
def commitRecord (state : CanonicalState) (record : Sort.Record) : CanonicalState :=
  let next:=intern state.1 record.2
  (next.1,state.2.set! record.1 next.2)

/-- Freezing remapped signatures before sorting is exact when none of the
nodes in this batch refers to another node in the batch. -/
theorem canonicalInsert_frozen (source : Vista) (mapping : Array Nat) (indices : List Nat)
    (state : CanonicalState)
    (same : ∀ index∈indices,referenceMap state.2 (source.node index)=referenceMap mapping (source.node index))
    (independent : ∀ index∈indices,∀ other∈indices,
      (∀ parent,(source.node other).parent=some parent → index≠parent) ∧
      ∀ edge∈(source.node other).incoming,index≠edge.1) :
    indices.foldl (canonicalInsert source) state=
      (Sort.indexedSignatures source mapping indices).foldl commitRecord state := by
  induction indices generalizing state with
  | nil=>rfl
  | cons index rest ih=>
    have step:canonicalInsert source state index=
        commitRecord state (index,referenceMap mapping (source.node index)):=by
      unfold canonicalInsert commitRecord
      rw [same index (by simp)]
    simp only [List.foldl_cons,Sort.indexedSignatures,List.map_cons]
    rw [←step]
    apply ih
    · intro other member
      have unrelated:=independent index (by simp) other (by simp [member])
      change referenceMap (state.2.set! index
        (intern state.1 (referenceMap state.2 (source.node index))).2) (source.node other)=_
      rw [referenceMap_set_ne _ _ _ _ unrelated.1 unrelated.2]
      exact same other (by simp [member])
    · intro first memFirst other memOther
      exact independent first (by simp [memFirst]) other (by simp [memOther])

theorem nodesValid_references_lower (source : Vista) (valid : NodesValid source) (index : Nat)
    (inside : index<source.nodes.size) :
    ReferencesIn (source.node index) (lowerNodes source (source.node index).level) := by
  obtain zero | positive:=nodeReady_of_check source index inside (valid index inside)
  · constructor
    · intro parent parentAt
      rw [zero.2.1] at parentAt
      contradiction
    · intro edge member
      rw [zero.2.2.2] at member
      contradiction
  · obtain ⟨_,parent,parentAt,parentInside,parentLevel,_,_,incoming⟩:=positive
    constructor
    · intro p same
      have equal:parent=p:=Option.some.inj (parentAt.symm.trans same)
      subst p
      exact (mem_lowerNodes _ _ _).mpr ⟨parentInside,by omega⟩
    · intro edge member
      obtain ⟨edgeInside,edgeLevel⟩:=incoming edge member
      exact (mem_lowerNodes _ _ _).mpr ⟨edgeInside,by omega⟩

/-- The complete level operation used by the executable can read and
remap all signatures once, stable-sort the indexed records, then intern
the records while updating only their own mapping slots. -/
theorem canonicalLevel_records (source : Vista) (valid : NodesValid source)
    (state : CanonicalState) (level : Nat) :
    canonicalLevel source state level=
      ((Sort.indexedSignatures source state.2 (levelNodes source level)).insertionSort
        (fun a b=>Sort.recordLE a b=true)).foldl commitRecord state := by
  rw [Sort.indexedSignatures_sorted]
  apply canonicalInsert_frozen
  · intro index member
    rfl
  · intro index member other otherMember
    have indexLevel:index<source.nodes.size ∧ (source.node index).level=level:=by
      simpa only [List.mem_mergeSort,levelNodes,List.mem_filter,List.mem_range,beq_iff_eq] using member
    have otherLevel:other<source.nodes.size ∧ (source.node other).level=level:=by
      simpa only [List.mem_mergeSort,levelNodes,List.mem_filter,List.mem_range,beq_iff_eq] using otherMember
    have references:=nodesValid_references_lower source valid other otherLevel.1
    constructor
    · intro parent parentAt equal
      have lower:=(mem_lowerNodes _ _ _).mp (references.1 parent parentAt)
      rw [←equal,indexLevel.2,otherLevel.2] at lower
      omega
    · intro edge edgeAt equal
      have lower:=(mem_lowerNodes _ _ _).mp (references.2 edge edgeAt)
      rw [←equal,indexLevel.2,otherLevel.2] at lower
      omega

end Counting.StackMachine.DagUpdate.Canonical
