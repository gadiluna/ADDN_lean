import Counting.DagSemanticsWellFormed
import Counting.DagSemanticsCanonical

namespace Counting.Executable

def AllNodes (property : Node → Prop) (nodes : Array Node) : Prop :=
  ∀ node ∈ nodes.toList, property node

theorem allNodes_iff (property : Node → Prop) (vista : Vista) :
    AllNodes property vista.nodes ↔ ∀ i, i < vista.nodes.size → property (vista.node i) := by
  constructor
  · intro h i hi
    apply h
    simp only [Vista.node, Array.getElem?_eq_getElem hi, Option.getD_some]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  · intro h node hn
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hn)
    simpa only [Vista.node, Array.getElem?_eq_getElem hi, Option.getD_some] using h i hi

theorem allNodes_push (property : Node → Prop) (nodes : Array Node) (node : Node)
    (old : AllNodes property nodes) (current : property node) :
    AllNodes property (nodes.push node) := by
  intro x hx
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact old x hx
  · exact current

theorem intern_allNodes (property : Node → Prop) (nodes : Array Node) (node : Node)
    (old : AllNodes property nodes) (current : property node) :
    AllNodes property (intern nodes node).1 := by
  unfold intern
  split
  · exact old
  · exact allNodes_push property nodes node old current

theorem importVista_allNodes (property : Node → Prop)
    (referenceStable : ∀ mapping node, property node → property (referenceMap mapping node))
    (pool : Array Node) (source : Vista) (old : AllNodes property pool)
    (current : AllNodes property source.nodes) :
    AllNodes property (importVista pool source).1 := by
  have aux (nodes : List Node) : ∀ state : Array Node × Array Nat,
      AllNodes property state.1 → (∀ node ∈ nodes, property node) →
      AllNodes property (nodes.foldl (fun state node =>
        let next := intern state.1 (referenceMap state.2 node)
        (next.1, state.2.push next.2)) state).1 := by
    induction nodes with
    | nil => intro state h _; exact h
    | cons node rest ih =>
        intro state h hnodes
        exact ih _ (intern_allNodes property _ _ h (referenceStable _ _ (hnodes node (by simp))))
          (fun n hn => hnodes n (by simp [hn]))
  unfold importVista
  rw [← Array.foldl_toList]
  exact aux source.nodes.toList (pool, #[]) old current

/-- Initial histories carry no references. This is separate from bounds so
that intermediate shared pools need not yet be reachable from one bottom. -/
def BaseCleanNode (node : Node) : Prop :=
  node.level = 0 → node.parent = none ∧ node.incoming = []

def BaseClean (vista : Vista) : Prop := AllNodes BaseCleanNode vista.nodes

theorem baseClean_of_valid (vista : Vista) (valid : vista.valid = true) : BaseClean vista := by
  apply (allNodes_iff BaseCleanNode vista).mpr
  intro i hi hz
  have hn : nodeValid vista i = true := by
    simp only [Vista.valid, Bool.and_eq_true] at valid
    exact List.all_eq_true.mp valid.1.1.2 i (List.mem_range.mpr hi)
  simp only [nodeValid, hz, beq_self_eq_true, if_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none, List.isEmpty_iff] at hn
  exact ⟨hn.1.1, hn.2⟩

theorem referenceMap_baseClean (mapping : Array Nat) (node : Node)
    (clean : BaseCleanNode node) : BaseCleanNode (referenceMap mapping node) := by
  intro hz
  obtain ⟨parent, incoming⟩ := clean hz
  simp only [referenceMap, parent, incoming, Option.map_none, List.foldl_nil, and_self]

theorem importVista_baseClean (pool : Array Node) (source : Vista)
    (old : BaseClean ⟨pool, 0⟩) (current : BaseClean source) :
    BaseClean ⟨(importVista pool source).1, 0⟩ :=
  importVista_allNodes BaseCleanNode referenceMap_baseClean pool source old current

theorem references_lower_of_structure (vista : Vista) (wellFormed : WellFormed vista)
    (clean : BaseClean vista) (i : Nat) (hi : i < vista.nodes.size) :
    ReferencesIn (vista.node i) (lowerNodes vista (vista.node i).level) := by
  rcases wellFormed i hi with hz | ⟨p, hp, hpi, hpl, incoming⟩
  · obtain ⟨parent, incoming⟩ := (allNodes_iff _ _).mp clean i hi hz
    constructor
    · intro p hp
      rw [parent] at hp
      contradiction
    · intro edge he
      rw [incoming] at he
      contradiction
  · constructor
    · intro q hq
      have heq : p = q := Option.some.inj (hp.symm.trans hq)
      subst q
      exact (mem_lowerNodes _ _ _).mpr ⟨hpi.trans hi, by omega⟩
    · intro edge he
      obtain ⟨hei, hel⟩ := incoming edge he
      exact (mem_lowerNodes _ _ _).mpr ⟨hei.trans hi, by omega⟩

theorem canonicalize_decode_of_structure (vista : Vista)
    (wellFormed : WellFormed vista) (clean : BaseClean vista)
    (i : Nat) (hi : i < vista.nodes.size) :
    decodeNode (canonicalize vista) (vista.node i).level
      ((canonicalState vista).2[i]?.getD 0) = decodeNode vista (vista.node i).level i :=
  canonicalize_decode_of_references vista wellFormed
    (references_lower_of_structure vista wellFormed clean) i hi

end Counting.Executable
