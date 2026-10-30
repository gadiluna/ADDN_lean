import Counting.SmallPrefixBounds

/-! Dense full-prefix tables. Each level is a list of rows. A row contains
anonymity, input bit, degree, parent index, and all previous-level receipts.
The initial level has degree and parent zero and no receipt fields. List
lengths provide framing, so no expanded histories occur in the binary data. -/
namespace Counting.SmallPrefix
open TimingProtocolLocal
variable {A : Type} [Fintype A]

noncomputable def nodeRow (G : Nat → A → A → Nat) (leader : A → Bool) :
    (r : Nat) → FullHistory r → List Nat
  | 0, h => [anonymity G leader 0 h, if h = true then 1 else 0, 0, 0]
  | r + 1, h => [anonymity G leader (r + 1) h, if input (r + 1) h then 1 else 0,
      degree r h, (fullLevel G leader r).toList.idxOf (parent r h)] ++
      (fullLevel G leader r).toList.map (fun u => red r u h)

noncomputable def table (G : Nat → A → A → Nat) (leader : A → Bool) (t : Nat) :
    List (List (List Nat)) :=
  (List.range (t + 1)).map (fun r => (fullLevel G leader r).toList.map (nodeRow G leader r))

def tableCodec : Encoding.Codec (List (List (List Nat))) :=
  Encoding.list (Encoding.list (Encoding.list Encoding.natural))

noncomputable def tableBits (G : Nat → A → A → Nat) (leader : A → Bool) (t : Nat) : List Bool :=
  tableCodec.encode (table G leader t)

theorem table_roundtrip (G : Nat → A → A → Nat) (leader : A → Bool) (t : Nat) (suffix : List Bool) :
    tableCodec.decode (tableBits G leader t ++ suffix) = some (table G leader t, suffix) :=
  tableCodec.roundtrip _ _

theorem fullLevel_list_nodup (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat) :
    (fullLevel G leader r).toList.Nodup := Finset.nodup_toList _

theorem parent_in_fullLevel (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat)
    (v : FullHistory (r + 1)) (member : v ∈ fullLevel G leader (r + 1)) :
    parent r v ∈ fullLevel G leader r := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp member
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

/-- No positive receipt is omitted by the dense previous-level enumeration. -/
theorem red_outside_fullLevel (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat)
    (u : FullHistory r) (absent : u ∉ fullLevel G leader r)
    (v : FullHistory (r + 1)) (member : v ∈ fullLevel G leader (r + 1)) : red r u v = 0 := by
  classical
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp member
  unfold red
  change (incoming _ _ b).count u = 0
  rw [count_incoming]
  apply Finset.sum_eq_zero
  intro a _
  have different : history G leader r a ≠ u := fun eq =>
    absent (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, eq⟩)
  simp [different]

/-- Parent indices in the actual table point to precisely the parent history. -/
theorem parent_index_correct (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat)
    (v : FullHistory (r + 1)) (member : v ∈ fullLevel G leader (r + 1)) :
    (fullLevel G leader r).toList[(fullLevel G leader r).toList.idxOf (parent r v)]? =
      some (parent r v) := by
  classical
  exact List.getElem?_idxOf (Finset.mem_toList.mpr (parent_in_fullLevel G leader r v member))

/-- The serialized level enumerates every full history exactly once, and
its row contains all anonymities, parent indices, labels and red counts. -/
theorem table_level (G : Nat → A → A → Nat) (leader : A → Bool) (t r : Nat)
    (within : r ≤ t) :
    (table G leader t)[r]? = some ((fullLevel G leader r).toList.map (nodeRow G leader r)) := by
  rw [table, List.getElem?_map, List.getElem?_range (by omega), Option.map_some]

theorem list_encoded_bound {B : Type} (codec : Encoding.Codec B) (values : List B)
    (count payload : Nat) (length : values.length ≤ count)
    (elements : ∀ x ∈ values, (codec.encode x).length ≤ payload) :
    ((Encoding.list codec).encode values).length ≤ (count + 1) * (payload + 3) := by
  rw [Encoding.list_length]
  have size : values.length.size ≤ count :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans length
  have sum : (values.map (fun x => (codec.encode x).length)).sum ≤ values.length * payload := by
    clear length size
    induction values with
    | nil => simp
    | cons x xs ih =>
      have h := elements x List.mem_cons_self
      have tail := ih (fun a ha => elements a (List.mem_cons_of_mem x ha))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  nlinarith

def tableBudget (t B K : Nat) := (t + 2) * ((B + 1) * ((B + 5) * (2 * K + 4) + 3) + 3)

/-- A bound for the actual, fully framed, binary table (including indices). -/
theorem table_bits_bound (G : Nat → A → A → Nat) (leader : A → Bool) (t B K : Nat)
    (nodes : ∀ r, r ≤ t → (fullLevel G leader r).card ≤ B)
    (anons : ∀ r, r ≤ t → ∀ h ∈ fullLevel G leader r, (anonymity G leader r h).size ≤ K)
    (degrees : ∀ r, r < t → ∀ h ∈ fullLevel G leader (r + 1), (degree r h).size ≤ K)
    (reds : ∀ r, r < t → ∀ u (v : FullHistory (r + 1)),
      v ∈ fullLevel G leader (r + 1) → (red r u v).size ≤ K)
    (indices : B ≤ K) (positive : 1 ≤ K) :
    (tableBits G leader t).length ≤ tableBudget t B K := by
  classical
  have rowLength (r : Nat) (within : r ≤ t) (h : FullHistory r) :
      (nodeRow G leader r h).length ≤ B + 4 := by
    cases r with
    | zero => simp [nodeRow]
    | succ r =>
      simp only [nodeRow, List.length_append, List.length_cons, List.length_nil,
        List.length_map, Finset.length_toList]
      have := nodes r (by omega)
      omega
  have rowEntries (r : Nat) (within : r ≤ t) (h : FullHistory r)
      (member : h ∈ fullLevel G leader r) :
      ∀ x ∈ nodeRow G leader r h, x.size ≤ K := by
    cases r with
    | zero =>
      intro x hx
      simp only [nodeRow, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact anons 0 within h member
      · split_ifs <;> simp_all
      · simp
      · simp
    | succ r =>
      intro x hx
      simp only [nodeRow, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl) | hx
      · exact anons (r + 1) within h member
      · split_ifs <;> simp_all
      · exact degrees r (by omega) h member
      · have bound : (fullLevel G leader r).toList.idxOf (parent r h) ≤
            (fullLevel G leader r).toList.length := List.idxOf_le_length
        have bitBound : ((fullLevel G leader r).toList.idxOf (parent r h)).size ≤
            (fullLevel G leader r).card :=
          (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simpa using bound)
        exact bitBound.trans ((nodes r (by omega)).trans indices)
      · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
        exact reds r (by omega) u h member
  have rowBound (r : Nat) (within : r ≤ t) (h : FullHistory r)
      (member : h ∈ fullLevel G leader r) :
      ((Encoding.list Encoding.natural).encode (nodeRow G leader r h)).length ≤
        (B + 5) * (2 * K + 4) := by
    apply list_encoded_bound Encoding.natural _ (B + 4) (2 * K + 1) (rowLength r within h)
    intro x hx
    rw [Encoding.natural_length]
    have := rowEntries r within h member x hx
    omega
  unfold tableBits tableCodec table tableBudget
  apply list_encoded_bound _ _ (t + 1) ((B + 1) * ((B + 5) * (2 * K + 4) + 3))
  · simp
  · intro rows member
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp member
    have within : r ≤ t := by have := List.mem_range.mp hr; omega
    apply list_encoded_bound _ _ B ((B + 5) * (2 * K + 4))
    · simpa using nodes r within
    · intro row member
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp member
      exact rowBound r within h (Finset.mem_toList.mp hh)

end Counting.SmallPrefix
