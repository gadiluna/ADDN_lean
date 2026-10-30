import Counting.DagSemanticsCounts

namespace Counting.Executable

theorem eraseDups_sublist_nodup {α : Type} [BEq α] [LawfulBEq α] (list : List α) :
    list.eraseDups.Sublist list ∧ list.eraseDups.Nodup := by
  generalize hn : list.length = length
  induction length using Nat.strong_induction_on generalizing list with
  | h length ih =>
      cases list with
      | nil => simp
      | cons a rest =>
          let filtered := rest.filter (fun b => !b == a)
          have less : filtered.length < length := by
            change (rest.filter (fun b => !b == a)).length < length
            have le := List.length_filter_le (fun b => !b == a) rest
            simp only [List.length_cons] at hn
            omega
          have tail := ih filtered.length less filtered rfl
          rw [List.eraseDups_cons]
          refine ⟨(tail.1.trans (List.filter_sublist)).cons_cons a, List.nodup_cons.mpr ⟨?_, tail.2⟩⟩
          intro ha
          have hf := List.mem_eraseDups.mp ha
          simp only [List.mem_filter, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
            and_false] at hf

theorem nodes_nodup_of_valid (vista : Vista) (valid : vista.valid = true) : vista.nodes.toList.Nodup := by
  have properties := eraseDups_sublist_nodup vista.nodes.toList
  have equal : vista.nodes.toList.eraseDups = vista.nodes.toList := by
    apply properties.1.eq_of_length
    simp only [Vista.valid, Bool.and_eq_true, beq_iff_eq] at valid
    simpa only [Array.length_toList] using valid.1.2
  rw [← equal]
  exact properties.2

theorem node_index_injective (vista : Vista) (valid : vista.valid = true)
    (i j : Nat) (hi : i < vista.nodes.size) (hj : j < vista.nodes.size)
    (equal : vista.node i = vista.node j) : i = j := by
  apply (nodes_nodup_of_valid vista valid).getElem_inj_iff.mp
  change vista.nodes[i] = vista.nodes[j]
  simpa only [Vista.node, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hj, Option.getD_some] using equal

theorem nodeValid_of_valid (vista : Vista) (valid : vista.valid = true)
    (i : Nat) (hi : i < vista.nodes.size) : nodeValid vista i = true := by
  simp only [Vista.valid, Bool.and_eq_true] at valid
  exact List.all_eq_true.mp valid.1.1.2 i (List.mem_range.mpr hi)

theorem nodeValid_zero (vista : Vista) (i : Nat) (valid : nodeValid vista i = true)
    (zero : (vista.node i).level = 0) :
    (vista.node i).parent = none ∧ (vista.node i).degree = 0 ∧ (vista.node i).incoming = [] := by
  simpa only [nodeValid, zero, beq_self_eq_true, if_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none, beq_iff_eq, List.isEmpty_iff, and_assoc] using valid

theorem nodeValid_positive (vista : Vista) (i : Nat) (valid : nodeValid vista i = true)
    (positive : (vista.node i).level ≠ 0) :
    ∃ p, (vista.node i).parent = some p ∧ p < i ∧
      (vista.node p).level + 1 = (vista.node i).level ∧
      (vista.node p).leader = (vista.node i).leader ∧
      countsSorted (vista.node i).incoming = true ∧
      ∀ edge ∈ (vista.node i).incoming,
        edge.1 < i ∧ (vista.node edge.1).level + 1 = (vista.node i).level := by
  unfold nodeValid at valid
  dsimp only at valid
  simp only [beq_iff_eq, positive, if_false] at valid
  cases hp : (vista.node i).parent with
  | none => simp [hp] at valid
  | some p =>
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
      exact ⟨p, rfl, valid.1.1.1.1, valid.1.1.1.2, valid.1.1.2, valid.1.2,
        fun edge he => by simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          using List.all_eq_true.mp valid.2 edge he⟩

theorem node_eq_of_fields (a b : Node)
    (level : a.level = b.level) (parent : a.parent = b.parent)
    (leader : a.leader = b.leader) (degree : a.degree = b.degree)
    (incoming : a.incoming = b.incoming) : a = b := by
  cases a
  cases b
  simp_all

/-- The validator's exact-signature deduplication, positive sorted bundles
and inherited labels ensure that each full history has one stored node. -/
theorem decodeNode_injective (vista : Vista) (valid : vista.valid = true)
    (depth i j : Nat) (hi : i < vista.nodes.size) (hj : j < vista.nodes.size)
    (li : (vista.node i).level = depth) (lj : (vista.node j).level = depth)
    (equal : decodeNode vista depth i = decodeNode vista depth j) : i = j := by
  induction depth generalizing i j with
  | zero =>
      obtain ⟨pi, di, mi⟩ := nodeValid_zero vista i (nodeValid_of_valid vista valid i hi) li
      obtain ⟨pj, dj, mj⟩ := nodeValid_zero vista j (nodeValid_of_valid vista valid j hj) lj
      apply node_index_injective vista valid i j hi hj
      exact node_eq_of_fields _ _ (li.trans lj.symm) (pi.trans pj.symm) equal
        (di.trans dj.symm) (mi.trans mj.symm)
  | succ depth ih =>
      obtain ⟨pi, hpi, hip, lip, leaderi, sortedi, incomingi⟩ :=
        nodeValid_positive vista i (nodeValid_of_valid vista valid i hi) (by omega)
      obtain ⟨pj, hpj, hjp, ljp, leaderj, sortedj, incomingj⟩ :=
        nodeValid_positive vista j (nodeValid_of_valid vista valid j hj) (by omega)
      have parentEqual : pi = pj := by
        apply ih pi pj (hip.trans hi) (hjp.trans hj) (by omega) (by omega)
        simpa only [decodeNode, hpi, hpj, Option.getD_some] using congrArg Prod.fst equal
      have degreeEqual : (vista.node i).degree = (vista.node j).degree :=
        congrArg (fun h : Counting.FullHistory (depth + 1) => h.2.1) equal
      have messagesEqual : bundleMessages (decodeNode vista depth) (vista.node i).incoming =
          bundleMessages (decodeNode vista depth) (vista.node j).incoming :=
        congrArg (fun h : Counting.FullHistory (depth + 1) => h.2.2) equal
      have bundlesEqual : (vista.node i).incoming = (vista.node j).incoming := by
        apply bundleMessages_eq_implies_bundles_eq (decodeNode vista depth) _ _
          (sparse_of_countsSorted _ sortedi) (sparse_of_countsSorted _ sortedj) _ messagesEqual
        have bounds : ∀ e ∈ (vista.node i).incoming ++ (vista.node j).incoming,
            e.1 < vista.nodes.size ∧ (vista.node e.1).level = depth := by
          intro e he
          rcases List.mem_append.mp he with he | he
          · obtain ⟨hei, hel⟩ := incomingi e he
            exact ⟨hei.trans hi, by omega⟩
          · obtain ⟨hei, hel⟩ := incomingj e he
            exact ⟨hei.trans hj, by omega⟩
        intro e he f hf historiesEqual
        exact ih e.1 f.1 (bounds e he).1 (bounds f hf).1 (bounds e he).2 (bounds f hf).2 historiesEqual
      apply node_index_injective vista valid i j hi hj
      exact node_eq_of_fields _ _ (li.trans lj.symm) (by rw [hpi, hpj, parentEqual])
        (leaderi.symm.trans ((congrArg (fun p => (vista.node p).leader) parentEqual).trans leaderj))
        degreeEqual bundlesEqual

end Counting.Executable
