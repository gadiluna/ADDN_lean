import Counting.EncodingTabulate

/-! Binary length bounds for concrete, densely tabulated network inputs.
Every length prefix and every zero matrix entry is included. -/
namespace Counting.Encoding

theorem array_length_le {A : Type} (codec : Codec A) (values : Array A) (B : Nat)
    (bounded : ∀ value ∈ values.toList, (codec.encode value).length ≤ B) :
    ((array codec).encode values).length ≤ 2*values.size.size+1+values.size*B := by
  have sum := List.sum_le_sum (l := values.toList)
    (f := fun value => (codec.encode value).length) (g := fun _ => B) bounded
  simp only [List.map_const', List.sum_replicate, Array.length_toList, smul_eq_mul] at sum
  rw [array_length]
  omega

theorem array_ofFn_length_le {A : Type} (codec : Codec A) {n : Nat} (f : Fin n → A)
    (B : Nat) (bounded : ∀ i, (codec.encode (f i)).length ≤ B) :
    ((array codec).encode (Array.ofFn f)).length ≤ 2*n.size+1+n*B := by
  have bound := array_length_le codec (Array.ofFn f) B (by
    intro value present
    have member : value ∈ Array.ofFn f := by simpa only [Array.mem_def] using present
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp member
    exact bounded i)
  simpa only [Array.size_ofFn] using bound

def tabulateLengthBound (n t B : Nat) : Nat :=
  (2*n.size+1+n) + (2*t.size+1+t*(2*n.size+1+n*(2*n.size+1+n*(2*B+1))))

theorem tabulate_encoding_length (n t : Nat) (leader : Fin n → Bool)
    (G : Nat → Fin n → Fin n → Nat) (B : Nat)
    (labels : ∀ r, 0 < r → r ≤ t → ∀ a b, (G r a b).size ≤ B) :
    (networkInput.encode (tabulate n t leader G)).length ≤ tabulateLengthBound n t B := by
  have leaders := array_ofFn_length_le boolean leader 1 (by intro a; simp [boolean])
  have rounds := array_ofFn_length_le (array (array natural))
    (fun r : Fin t => Array.ofFn (fun a : Fin n => Array.ofFn (G (r.val+1) a)))
    (2*n.size+1+n*(2*n.size+1+n*(2*B+1))) (by
      intro r
      apply array_ofFn_length_le
      intro a
      apply array_ofFn_length_le
      intro b
      rw [natural_length]
      have bounded := labels (r.val+1) (by omega) (by have := r.isLt; omega) a b
      omega)
  rw [networkInput_length]
  simpa only [tabulate, tabulateLengthBound, Nat.mul_one] using Nat.add_le_add leaders rounds

/-- A uniform polynomial in the three explicit size parameters. -/
theorem tabulateLengthBound_polynomial (n t B L : Nat)
    (agents : n ≤ L) (rounds : t ≤ L) (labels : B ≤ L) :
    tabulateLengthBound n t B ≤ 12*(L+1)^4 := by
  have nb : n.size ≤ L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans agents
  have tb : t.size ≤ L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans rounds
  have row : 2*n.size+1+n*(2*B+1) ≤ 2*L+1+L*(2*L+1) := by
    have := Nat.mul_le_mul agents (show 2*B+1 ≤ 2*L+1 by omega)
    omega
  have matrix : 2*n.size+1+n*(2*n.size+1+n*(2*B+1)) ≤
      2*L+1+L*(2*L+1+L*(2*L+1)) := by
    have := Nat.mul_le_mul agents row
    omega
  have total := Nat.mul_le_mul rounds matrix
  unfold tabulateLengthBound
  nlinarith [Nat.zero_le (L^2), Nat.zero_le (L^3)]

end Counting.Encoding
