import Counting.DagSemantics
import Mathlib.Data.List.Induction

namespace Counting.Executable

instance : LawfulBEq Node where
  eq_of_beq := by
    intro a b h
    cases a
    cases b
    change instBEqNode.beq _ _ = true at h
    simpa only [instBEqNode.beq, Bool.and_eq_true, beq_iff_eq, Node.mk.injEq] using h
  rfl := by
    intro a
    cases a
    change instBEqNode.beq _ _ = true
    simp only [instBEqNode.beq, beq_self_eq_true, Bool.and_self]

def ReferencesBefore (node : Node) (bound : Nat) : Prop :=
  (∀ parent, node.parent = some parent → parent < bound) ∧
    ∀ edge ∈ node.incoming, edge.1 < bound

def Topological (vista : Vista) : Prop :=
  ∀ index, index < vista.nodes.size → ReferencesBefore (vista.node index) index

theorem topological_of_valid (vista : Vista) (valid : vista.valid = true) :
    Topological vista := by
  intro index hi
  have hn : nodeValid vista index = true := by
    simp only [Vista.valid, Bool.and_eq_true] at valid
    exact List.all_eq_true.mp valid.1.1.2 index (List.mem_range.mpr hi)
  unfold nodeValid at hn
  dsimp only at hn
  by_cases hz : (vista.node index).level = 0
  · simp only [beq_iff_eq, hz, if_true, Bool.and_eq_true,
      Option.isNone_iff_eq_none, List.isEmpty_iff] at hn
    constructor
    · intro parent hp
      rw [hn.1.1] at hp
      contradiction
    · intro edge he
      rw [hn.2] at he
      contradiction
  · simp only [beq_iff_eq, hz, if_false] at hn
    cases hp : (vista.node index).parent with
    | none => simp [hp] at hn
    | some parent =>
        simp only [hp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hn
        constructor
        · intro p hpp
          have heq : parent = p := Option.some.inj (hp.symm.trans hpp)
          simpa only [heq] using hn.1.1.1.1
        · intro edge he
          have he' := List.all_eq_true.mp hn.2 edge he
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he'
          exact he'.1

theorem referenceMap_congr (left right : Array Nat) (node : Node)
    (parentEqual : ∀ p, node.parent = some p → left[p]?.getD 0 = right[p]?.getD 0)
    (incomingEqual : ∀ edge ∈ node.incoming,
      left[edge.1]?.getD 0 = right[edge.1]?.getD 0) :
    referenceMap left node = referenceMap right node := by
  have hp : node.parent.map (fun i => left[i]?.getD 0) =
      node.parent.map (fun i => right[i]?.getD 0) := by
    cases h : node.parent with
    | none => rfl
    | some p => simp only [Option.map_some, parentEqual p h]
  have foldEqual : ∀ (bundles : List (Nat × Nat)) (acc : List (Nat × Nat)),
      (∀ edge ∈ bundles, left[edge.1]?.getD 0 = right[edge.1]?.getD 0) →
      bundles.foldl (fun acc edge => addCount (left[edge.1]?.getD 0) edge.2 acc) acc =
        bundles.foldl (fun acc edge => addCount (right[edge.1]?.getD 0) edge.2 acc) acc := by
    intro bundles
    induction bundles with
    | nil => intros; rfl
    | cons edge rest ih =>
        intro acc equal
        simp only [List.foldl_cons, equal edge (List.mem_cons_self)]
        exact ih _ (fun edge he => equal edge (List.mem_cons_of_mem _ he))
  unfold referenceMap
  rw [hp, foldEqual node.incoming [] incomingEqual]

theorem referenceMap_push (mapping : Array Nat) (newIndex : Nat) (node : Node)
    (references : ReferencesBefore node mapping.size) :
    referenceMap (mapping.push newIndex) node = referenceMap mapping node := by
  apply referenceMap_congr
  · intro parent hp
    simp only [Array.getElem?_push_lt (references.1 parent hp),
      Array.getElem?_eq_getElem (references.1 parent hp)]
  · intro edge he
    simp only [Array.getElem?_push_lt (references.2 edge he),
      Array.getElem?_eq_getElem (references.2 edge he)]

theorem intern_size_le (nodes : Array Node) (node : Node) :
    nodes.size ≤ (intern nodes node).1.size := by
  unfold intern
  split <;> simp

theorem intern_index_lt (nodes : Array Node) (node : Node) :
    (intern nodes node).2 < (intern nodes node).1.size := by
  unfold intern
  split
  · rename_i index found
    exact List.mem_range.mp (List.mem_of_find?_eq_some found)
  · simp

theorem intern_node (nodes : Array Node) (node : Node) :
    (Vista.mk (intern nodes node).1 0).node (intern nodes node).2 = node := by
  unfold intern
  split
  · rename_i index found
    simpa only [Vista.node, beq_iff_eq] using List.find?_some found
  · simp [Vista.node]

theorem intern_extends (nodes : Array Node) (node : Node) :
    Extends ⟨nodes, 0⟩ ⟨(intern nodes node).1, 0⟩ := by
  intro index hi
  unfold intern
  split
  · rfl
  · simp only [Vista.node, Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]

/-- Each input node produces exactly one index in the import map. -/
theorem importVista_mapping_size (pool : Array Node) (source : Vista) :
    (importVista pool source).2.size = source.nodes.size := by
  rcases source with ⟨⟨nodes⟩, bottom⟩
  induction nodes using List.reverseRecOn with
  | nil => rfl
  | append_singleton nodes node ih =>
      simp only [importVista, ← Array.foldl_toList] at *
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        Array.size_push, List.length_append, List.length_singleton, List.size_toArray] using
          congrArg (· + 1) ih

@[simp] theorem node_push_old (nodes : Array Node) (node : Node) (bottom index : Nat)
    (inside : index < nodes.size) :
    (Vista.mk (nodes.push node) bottom).node index = (Vista.mk nodes bottom).node index := by
  simp only [Vista.node, Array.getElem?_push_lt inside, Array.getElem?_eq_getElem inside]

@[simp] theorem node_push_last (nodes : Array Node) (node : Node) (bottom : Nat) :
    (Vista.mk (nodes.push node) bottom).node nodes.size = node := by simp [Vista.node]

theorem importVista_push (pool nodes : Array Node) (node : Node) (bottom : Nat) :
    importVista pool ⟨nodes.push node, bottom⟩ =
      let before := importVista pool ⟨nodes, bottom⟩
      let next := intern before.1 (referenceMap before.2 node)
      (next.1, before.2.push next.2) := by
  simp only [importVista, Array.foldl_push]

/-- Structural correctness of the actual match-and-merge pass. All imported
references are in bounds and every source node is reindexed exactly; preexisting
pool nodes retain their contents. This theorem permits arbitrary initial pools. -/
theorem importVista_correct (pool : Array Node) (source : Vista)
    (topological : Topological source) :
    pool.size ≤ (importVista pool source).1.size ∧
    Extends ⟨pool, 0⟩ ⟨(importVista pool source).1, 0⟩ ∧
    (∀ index, index < source.nodes.size →
      ((importVista pool source).2[index]?.getD 0) < (importVista pool source).1.size) ∧
    Relabels source ⟨(importVista pool source).1, 0⟩ (importVista pool source).2 := by
  rcases source with ⟨⟨nodes⟩, bottom⟩
  induction nodes using List.reverseRecOn with
  | nil =>
      simp only [importVista, Array.foldl_empty]
      exact ⟨le_rfl, fun _ _ => rfl, by simp, by intro i hi; simp at hi⟩
  | append_singleton nodes node ih =>
      let previous : Vista := ⟨⟨nodes⟩, bottom⟩
      have pushed : (⟨nodes ++ [node]⟩ : Array Node) = previous.nodes.push node := by
        apply Array.ext'
        simp [previous]
      rw [pushed] at topological ⊢
      have oldTopo : Topological previous := by
        intro i hi
        have h := topological i (by simpa only [Array.size_push] using Nat.lt_succ_of_lt hi)
        simpa only [node_push_old _ _ _ _ hi] using h
      have ih := ih oldTopo
      let before := importVista pool previous
      let next := intern before.1 (referenceMap before.2 node)
      have mapSize : before.2.size = previous.nodes.size := importVista_mapping_size pool previous
      have newRefs : ReferencesBefore node before.2.size := by
        rw [mapSize]
        simpa only [node_push_last] using topological previous.nodes.size (by simp)
      rw [importVista_push]
      change pool.size ≤ next.1.size ∧ Extends ⟨pool, 0⟩ ⟨next.1, 0⟩ ∧
        (∀ index, index < (previous.nodes.push node).size →
          ((before.2.push next.2)[index]?.getD 0) < next.1.size) ∧
        Relabels ⟨previous.nodes.push node, bottom⟩ ⟨next.1, 0⟩ (before.2.push next.2)
      refine ⟨ih.1.trans (intern_size_le _ _), ?_, ?_, ?_⟩
      · intro i hi
        exact (intern_extends _ _ i (hi.trans_le ih.1)).trans (ih.2.1 i hi)
      · intro i hi
        have hib : i ≤ previous.nodes.size := Nat.le_of_lt_succ (by simpa using hi)
        rcases lt_or_eq_of_le hib with hlt | rfl
        · have him : i < before.2.size := by omega
          have oldInside : before.2[i]?.getD 0 < before.1.size := ih.2.2.1 i hlt
          simpa only [Array.getElem?_push_lt him, Array.getElem?_eq_getElem him] using
            oldInside.trans_le (intern_size_le before.1 (referenceMap before.2 node))
        · rw [← mapSize, Array.getElem?_push_size, Option.getD_some]
          exact intern_index_lt _ _
      · intro i hi
        have hib : i ≤ previous.nodes.size := Nat.le_of_lt_succ (by simpa using hi)
        rcases lt_or_eq_of_le hib with hlt | rfl
        · have him : i < before.2.size := by omega
          have oldRefs : ReferencesBefore (previous.node i) before.2.size := by
            obtain ⟨hp, he⟩ := oldTopo i hlt
            exact ⟨fun p h => (hp p h).trans him, fun edge h => (he edge h).trans him⟩
          rw [Array.getElem?_push_lt him, Option.getD_some, node_push_old _ _ _ _ hlt]
          rw [referenceMap_push _ _ _ oldRefs]
          have old := ih.2.2.2 i hlt
          have ext := intern_extends before.1 (referenceMap before.2 node)
            (before.2[i]?.getD 0) (ih.2.2.1 i hlt)
          simpa only [Array.getElem?_eq_getElem him, Option.getD_some] using ext.trans old
        · rw [node_push_last, referenceMap_push _ _ _ newRefs, ← mapSize,
            Array.getElem?_push_size, Option.getD_some]
          exact intern_node _ _

/-- Importing a valid vista preserves the full-information history at every
source node, even when equal signatures are shared with the existing pool. -/
theorem importVista_decode (pool : Array Node) (source : Vista)
    (valid : source.valid = true) (index : Nat) (inside : index < source.nodes.size) :
    decodeNode ⟨(importVista pool source).1, 0⟩ (source.node index).level
      ((importVista pool source).2[index]?.getD 0) = decodeNode source (source.node index).level index :=
  decodeNode_eq_of_relabels source _ _ (wellFormed_of_valid source valid)
    (importVista_correct pool source (topological_of_valid source valid)).2.2.2 index inside

end Counting.Executable
