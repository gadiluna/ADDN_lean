import Counting.StackEncodingBoundedCount

/-! Canonical-natural interface to the existing bounded binary-to-unary
machine. The witness/budget is consumed, the framed header is preserved,
and an oversized value yields exactly the budget length and a false flag. -/
namespace Counting.StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def boundedNaturalResult (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11)→List Bool) (value : Nat) : Fin (extra+11)→List Bool :=
  Function.update
    (Function.update (Function.update store (w 1)
      (List.replicate (min value (store (w 10)).length) true)) (w 10) []) (w 6)
    (decide (value≤(store (w 10)).length)::store (w 6))

theorem countRun_natural_zero (value budget : Nat) :
    countRun value.bits 0 budget=min value budget := by
  rw [countRun_natural value 0 budget (Nat.zero_le _),Nat.zero_add,Nat.min_comm]

theorem boundedCount_natural_result (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11)→List Bool) (value : Nat)
    (header : store (w 0)=Encoding.natural.encode value) :
    boundedCountResult extra w store value.bits (store (w 10))=
      boundedNaturalResult extra w store value := by
  have status:=boundedCount_status extra w store value.bits (store (w 10))
  have canonical : (∃ n≤(store (w 10)).length,value.bits=n.bits) ↔ value≤(store (w 10)).length := by
    constructor
    · rintro ⟨n,bounded,equal⟩
      have same:=Encoding.bits_injective equal
      exact same ▸ bounded
    · intro bounded;exact ⟨value,bounded,rfl⟩
  rw [show decide (∃ n≤(store (w 10)).length,value.bits=n.bits)=
    decide (value≤(store (w 10)).length) by simp only [canonical]] at status
  funext r
  by_cases flag : r=w 6
  · subst r
    simpa only [boundedNaturalResult,Function.update_self] using status
  · by_cases source : r=w 0
    · subst r
      simp [boundedCountResult,boundedNaturalResult,countState,w.injective.eq_iff,header,Encoding.natural]
    · by_cases unary : r=w 1
      · subst r
        simp [boundedCountResult,boundedNaturalResult,countState,w.injective.eq_iff,countRun_natural_zero]
      · by_cases budget : r=w 10
        · subst r
          simp [boundedCountResult,boundedNaturalResult,countState,w.injective.eq_iff]
        · simp [boundedCountResult,boundedNaturalResult,countState,flag,source,unary,budget]

theorem boundedNatural_executes (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11)→List Bool) (value : Nat)
    (header : store (w 0)=Encoding.natural.encode value) (unaryEmpty : store (w 1)=[])
    (workEmpty : ∀ i : Fin 11,i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → store (w i)=[]) :
    ∃ time ≤ 64*((store (w 10)).length+(Encoding.natural.encode value).length+1)^3,
      Routine.Executes (boundedCount extra w) store time (boundedNaturalResult extra w store value) := by
  obtain ⟨time,bounded,executed⟩:=boundedCount_executes extra w store value.bits (store (w 10)) workEmpty
  have start : countState extra w store value.bits 0 (store (w 10))=store := by
    funext r
    by_cases source : r=w 0
    · subst r;simp [countState,header,Encoding.natural]
    · by_cases unary : r=w 1
      · subst r;simp [countState,w.injective.eq_iff,unaryEmpty]
      · by_cases budget : r=w 10
        · subst r;simp [countState,w.injective.eq_iff]
        · simp [countState,source,unary,budget]
  rw [start,boundedCount_natural_result extra w store value header] at executed
  exact ⟨time,bounded,executed⟩

theorem boundedNatural_unary (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11)→List Bool) (value : Nat) :
    boundedNaturalResult extra w store value (w 1)=
      List.replicate (min value (store (w 10)).length) true := by
  simp [boundedNaturalResult,w.injective.eq_iff]

theorem boundedNatural_flag (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11)→List Bool) (value : Nat) :
    boundedNaturalResult extra w store value (w 6)=
      decide (value≤(store (w 10)).length)::store (w 6) := by
  simp [boundedNaturalResult]

theorem boundedNatural_unary_of_fits (extra : Nat) (w : CountWorkspace extra)
    (store : Fin (extra+11)→List Bool) (value : Nat) (fits : value≤(store (w 10)).length) :
    boundedNaturalResult extra w store value (w 1)=List.replicate value true := by
  rw [boundedNatural_unary,Nat.min_eq_left fits]

end Counting.StackMachine.EncodingPrograms
