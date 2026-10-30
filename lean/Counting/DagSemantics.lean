import Counting.Executable
import Counting.HistoryBridge

/-! Mathematical interpretation of compressed vistas. Expansion into multisets
occurs only in this proof layer; executable multiplicities remain binary counts.
-/
namespace Counting.Executable

open scoped BigOperators

/-- Interpret sparse bundles as the multiset that they denote. -/
def bundleMessages {α : Type} (value : Nat → α) (bundles : List (Nat × Nat)) : Multiset α :=
  (bundles.map (fun edge => Multiset.replicate edge.2 (value edge.1))).sum

@[simp] theorem bundleMessages_nil {α : Type} (value : Nat → α) :
    bundleMessages value [] = 0 := rfl

@[simp] theorem bundleMessages_cons {α : Type} (value : Nat → α)
    (edge : Nat × Nat) (rest : List (Nat × Nat)) :
    bundleMessages value (edge :: rest) =
      Multiset.replicate edge.2 (value edge.1) + bundleMessages value rest := rfl

/-- Aggregating a bundle preserves every message, without expanding it at run time. -/
theorem bundleMessages_addCount {α : Type} (value : Nat → α)
    (index count : Nat) (bundles : List (Nat × Nat)) :
    bundleMessages value (addCount index count bundles) =
      Multiset.replicate count (value index) + bundleMessages value bundles := by
  induction bundles with
  | nil =>
      by_cases hc : count = 0 <;> simp [addCount, hc]
  | cons edge rest ih =>
      rcases edge with ⟨i, c⟩
      by_cases hc : count = 0
      · simp [addCount, hc]
      by_cases hi : index = i
      · subst i
        simp [addCount, hc, Multiset.replicate_add, add_assoc, add_comm]
      by_cases hlt : index < i
      · simp [addCount, hc, hi, hlt]
      · simp [addCount, hc, hi, hlt, ih, add_left_comm]

theorem bundleMessages_congr {α : Type} (left right : Nat → α)
    (bundles : List (Nat × Nat))
    (equal : ∀ edge ∈ bundles, left edge.1 = right edge.1) :
    bundleMessages left bundles = bundleMessages right bundles := by
  unfold bundleMessages
  congr 1
  apply List.map_congr_left
  intro edge he
  rw [equal edge he]

/-- Reindexing and merging coincident bundle destinations preserves their sum. -/
theorem bundleMessages_reindex {α : Type} (value : Nat → α)
    (mapping : Array Nat) (bundles accumulated : List (Nat × Nat)) :
    bundleMessages value
      (bundles.foldl (fun acc edge => addCount (mapping[edge.1]?.getD 0) edge.2 acc) accumulated) =
      bundleMessages (fun i => value (mapping[i]?.getD 0)) bundles +
        bundleMessages value accumulated := by
  induction bundles generalizing accumulated with
  | nil => simp
  | cons edge rest ih =>
      simp only [List.foldl_cons, ih, bundleMessages_addCount, bundleMessages_cons]
      ac_rfl

theorem bundleMessages_referenceMap {α : Type} (value : Nat → α)
    (mapping : Array Nat) (node : Node) :
    bundleMessages value (referenceMap mapping node).incoming =
      bundleMessages (fun i => value (mapping[i]?.getD 0)) node.incoming := by
  simpa only [referenceMap, bundleMessages_nil, add_zero] using
    bundleMessages_reindex value mapping node.incoming []

/-- Height-indexed semantic expansion. The extra height parameter makes this a
total function even on malformed arrays. Only a node's recorded height is used
when interpreting a well-formed DAG. -/
def decodeNode (vista : Vista) : (depth : Nat) → Nat → Counting.FullHistory depth
  | 0, index => (vista.node index).leader
  | depth + 1, index =>
      (decodeNode vista depth ((vista.node index).parent.getD 0),
        (vista.node index).degree,
        bundleMessages (decodeNode vista depth) (vista.node index).incoming)

def Vista.denotes (vista : Vista) : Counting.FullHistory (vista.node vista.bottom).level :=
  decodeNode vista (vista.node vista.bottom).level vista.bottom

@[simp] theorem initialVista_denotes (leader : Bool) :
    (initialVista leader).denotes = leader := rfl

/-- The structural part of validity, without reachability or uniqueness. It
suffices for well-founded interpretation and preservation under pool extension. -/
def WellFormed (vista : Vista) : Prop :=
  ∀ index, index < vista.nodes.size →
    (vista.node index).level = 0 ∨
      ∃ parent, (vista.node index).parent = some parent ∧ parent < index ∧
        (vista.node parent).level + 1 = (vista.node index).level ∧
        ∀ edge ∈ (vista.node index).incoming,
          edge.1 < index ∧ (vista.node edge.1).level + 1 = (vista.node index).level

theorem wellFormed_of_valid (vista : Vista) (valid : vista.valid = true) :
    WellFormed vista := by
  intro index hi
  have hn : nodeValid vista index = true := by
    simp only [Vista.valid, Bool.and_eq_true] at valid
    exact List.all_eq_true.mp valid.1.1.2 index (List.mem_range.mpr hi)
  unfold nodeValid at hn
  dsimp only at hn
  by_cases hz : (vista.node index).level = 0
  · exact Or.inl hz
  · right
    simp only [beq_iff_eq, hz, if_false] at hn
    cases hp : (vista.node index).parent with
    | none => simp [hp] at hn
    | some parent =>
        simp only [hp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hn
        exact ⟨parent, rfl, hn.1.1.1.1, hn.1.1.1.2,
          fun edge he => by simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
            using List.all_eq_true.mp hn.2 edge he⟩

/-- Extending a storage pool preserves every existing entry. -/
def Extends (old new : Vista) : Prop :=
  ∀ index, index < old.nodes.size → new.node index = old.node index

theorem decodeNode_eq_of_extends (old new : Vista) (wellFormed : WellFormed old)
    (extension : Extends old new) (index : Nat) (inside : index < old.nodes.size) :
    decodeNode new (old.node index).level index = decodeNode old (old.node index).level index := by
  generalize hd : (old.node index).level = depth
  induction depth using Nat.strong_induction_on generalizing index with
  | h depth ih =>
      cases depth with
      | zero => simp only [decodeNode, extension index inside]
      | succ depth =>
          obtain hz | ⟨parent, hp, hpi, hpl, incoming⟩ := wellFormed index inside
          · omega
          have hpdepth : (old.node parent).level = depth := by omega
          have parentEqual := ih depth (by omega) parent (by omega) hpdepth
          simp only [decodeNode, extension index inside, hp, Option.getD_some]
          have messagesEqual := bundleMessages_congr (decodeNode new depth)
            (decodeNode old depth) (old.node index).incoming (by
              intro edge he
              obtain ⟨hei, hel⟩ := incoming edge he
              exact ih depth (by omega) edge.1 (by omega) (by omega))
          exact Prod.ext parentEqual (Prod.ext rfl messagesEqual)

/-- A complete structural reindexing may identify equal signatures. It need
not be injective: shared nodes and repeated messages are interpreted correctly. -/
def Relabels (source target : Vista) (mapping : Array Nat) : Prop :=
  ∀ index, index < source.nodes.size →
    target.node (mapping[index]?.getD 0) = referenceMap mapping (source.node index)

theorem decodeNode_eq_of_relabels (source target : Vista) (mapping : Array Nat)
    (wellFormed : WellFormed source) (relabels : Relabels source target mapping)
    (index : Nat) (inside : index < source.nodes.size) :
    decodeNode target (source.node index).level (mapping[index]?.getD 0) =
      decodeNode source (source.node index).level index := by
  generalize hd : (source.node index).level = depth
  induction depth using Nat.strong_induction_on generalizing index with
  | h depth ih =>
      cases depth with
      | zero => simp only [decodeNode, relabels index inside, referenceMap]
      | succ depth =>
          obtain hz | ⟨parent, hp, hpi, hpl, incoming⟩ := wellFormed index inside
          · omega
          have hpdepth : (source.node parent).level = depth := by omega
          have parentEqual := ih depth (by omega) parent (by omega) hpdepth
          simp only [decodeNode, relabels index inside]
          rw [bundleMessages_referenceMap]
          simp only [referenceMap, hp, Option.map_some, Option.getD_some]
          have messagesEqual := bundleMessages_congr
            (fun i => decodeNode target depth (mapping[i]?.getD 0))
            (decodeNode source depth) (source.node index).incoming (by
              intro edge he
              obtain ⟨hei, hel⟩ := incoming edge he
              exact ih depth (by omega) edge.1 (by omega) (by omega))
          exact Prod.ext parentEqual (Prod.ext rfl messagesEqual)

end Counting.Executable
