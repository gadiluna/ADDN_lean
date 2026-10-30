import Counting.DagSemanticsLabels
import Counting.LinearSolver

namespace Counting.Executable

/-- Exact evidence from every branch of the executable audit. Subsequent
lemmas interpret these guards and the propagation loop mathematically. -/
structure AuditExtracted (vista : Vista) (leaders candidate last : Nat)
    (witness : AuditWitness) (values : Array ℚ) (natural : Array Nat) : Prop where
  opening : (!vista.valid || leaders == 0 || candidate < leaders || last == 0 ||
    (vista.node vista.bottom).level < last) = false
  leaderSeen : (levelNodes vista 0).any (fun i => (vista.node i).leader) = true
  bounded : (List.range (last + 1)).all (fun r => (levelNodes vista r).length ≤ candidate) = true
  childrenPresent : (List.range last).all (fun r =>
    (levelNodes vista r).all (fun i => !(children vista i (r + 1)).isEmpty)) = true
  anchorFound : ((List.range (last + 1)).reverse).find? (flat vista) = some witness.anchor
  solved : solveLinear? (levelNodes vista witness.anchor).length
    (anchorRows vista witness.anchor leaders) = some values
  naturalExact : positiveNaturals? values = some natural
  total : natural.toList.sum = candidate
  weights : witness.weights = propagateWeights vista witness.anchor natural
  flowCheck : (List.range witness.anchor).all (fun r => r == 0 ||
    (levelNodes vista (r - 1)).all (fun parent =>
      ((levelNodes vista r).map (fun v =>
        countFrom (vista.node v) parent * (witness.weights[v]?.getD 0))).sum ==
      ((children vista parent r).map (fun v =>
        (vista.node v).degree * (witness.weights[v]?.getD 0))).sum)) = true
  suffixCheck : (levelNodes vista witness.anchor).all (fun v =>
    ((levelNodes vista last).filter (fun descendant =>
      ascend vista (last - witness.anchor) descendant == some v)).length ≤
        (witness.weights[v]?.getD 0)) = true

theorem audit_extract (vista : Vista) (leaders candidate last : Nat) (witness : AuditWitness)
    (accepted : audit? vista leaders candidate last = some witness) :
    ∃ values natural, AuditExtracted vista leaders candidate last witness values natural := by
  rw [audit_unfold] at accepted
  split at accepted
  next => contradiction
  next hopen =>
    split at accepted
    next => contradiction
    next hleader =>
      split at accepted
      next => contradiction
      next hbound =>
        split at accepted
        next => contradiction
        next hchildren =>
          cases hanchor : ((List.range (last + 1)).reverse).find? (flat vista) with
          | none => simp [hanchor] at accepted
          | some anchor =>
              simp only [hanchor] at accepted
              dsimp only [bind, pure] at accepted
              rw [Option.bind_some] at accepted
              cases hvalues : solveLinear? (levelNodes vista anchor).length (anchorRows vista anchor leaders) with
              | none => simp [hvalues] at accepted
              | some values =>
                  simp only [hvalues, Option.bind_some] at accepted
                  cases hnatural : positiveNaturals? values with
                  | none => simp [hnatural] at accepted
                  | some natural =>
                      simp only [hnatural, Option.bind_some] at accepted
                      split at accepted
                      next => contradiction
                      next htotal =>
                        split at accepted
                        next => contradiction
                        next hflow =>
                          split at accepted
                          next => contradiction
                          next hsuffix =>
                            have identify := Option.some.inj accepted
                            subst witness
                            exact ⟨values, natural, ⟨by simpa using hopen, by simpa using hleader,
                              by simpa using hbound, by simpa using hchildren, hanchor,
                              hvalues, hnatural, by simpa using htotal, rfl,
                              by simpa only [Bool.not_eq_true, Bool.not_eq_false'] using hflow,
                              by simpa using hsuffix⟩⟩

theorem find_reverse_range_maximum (predicate : Nat → Bool) (bound anchor : Nat)
    (found : (List.range bound).reverse.find? predicate = some anchor) :
    anchor < bound ∧ predicate anchor = true ∧
      ∀ k, anchor < k → k < bound → predicate k = false := by
  induction bound with
  | zero => simp at found
  | succ bound ih =>
      rw [List.range_succ, List.reverse_append] at found
      simp only [List.reverse_singleton, List.singleton_append] at found
      cases hb : predicate bound with
      | true =>
          simp only [List.find?_cons, hb] at found
          have equal := Option.some.inj found
          subst anchor
          exact ⟨Nat.lt_succ_self bound, hb, by intro k hk hkb; omega⟩
      | false =>
          simp only [List.find?_cons, hb] at found
          obtain ⟨inside, passes, maximal⟩ := ih found
          refine ⟨Nat.lt_succ_of_lt inside, passes, ?_⟩
          intro k hk hkb
          rcases lt_or_eq_of_le (Nat.le_of_lt_succ hkb) with less | rfl
          · exact maximal k hk less
          · exact hb

theorem AuditExtracted.basic {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural) :
    vista.valid = true ∧ 0 < leaders ∧ leaders ≤ candidate ∧ 0 < last ∧
    last ≤ (vista.node vista.bottom).level ∧ 0 < witness.anchor ∧ witness.anchor ≤ last ∧
    flat vista witness.anchor = true ∧
    (∀ r, witness.anchor < r → r ≤ last → flat vista r = false) ∧
    natural.size = (levelNodes vista witness.anchor).length := by
  have opening := evidence.opening
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne, decide_eq_false_iff_not,
    not_lt] at opening
  have maximum := find_reverse_range_maximum (flat vista) (last + 1) witness.anchor evidence.anchorFound
  have positive : 0 < witness.anchor := by
    have hf := maximum.2.1
    simp only [flat, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact hf.1.1
  have sizeValues := (solveLinear_sound _ _ _ evidence.solved).2.1
  have sizeNatural := (positiveNaturals_sound _ _ evidence.naturalExact).1
  exact ⟨opening.1.1.1.1, Nat.pos_of_ne_zero opening.1.1.1.2, opening.1.1.2,
    Nat.pos_of_ne_zero opening.1.2, opening.2, positive, Nat.le_of_lt_succ maximum.1,
    maximum.2.1, fun r hr hl => maximum.2.2 r hr (Nat.lt_succ_of_le hl),
    sizeNatural.trans sizeValues⟩


theorem AuditExtracted.accepted {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural) :
    audit? vista leaders candidate last = some witness := by
  rcases witness with ⟨anchor, weights⟩
  have flow := evidence.flowCheck
  have suffix := evidence.suffixCheck
  simp only [audit_unfold, evidence.opening, Bool.false_eq_true, if_false, evidence.leaderSeen,
    evidence.bounded, evidence.childrenPresent, Bool.not_true, evidence.anchorFound]
  dsimp only [bind, pure]
  simp only [Option.bind_some, evidence.solved, evidence.naturalExact, evidence.total, bne_self_eq_false,
    ← evidence.weights, flow, suffix, Bool.not_true, Bool.false_eq_true, if_false]

end Counting.Executable
