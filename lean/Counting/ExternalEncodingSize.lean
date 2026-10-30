import Counting.ExternalEncoding

namespace Counting.External.CNFEncoding

theorem nat_size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self

theorem literal_length_upper {n : ℕ} (literal : Literal n) :
    ((Encoding.product Encoding.natural Encoding.boolean).encode (literalRaw literal)).length ≤ 2*n+2 := by
  rw [literal_length]
  have bound := (nat_size_le_self literal.var.val).trans literal.var.isLt.le
  omega

theorem clause_length_upper {n : ℕ} (clause : List (Literal n)) :
    ((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode
      (clause.map literalRaw)).length ≤ clause.length*(2*n+4)+1 := by
  rw [Encoding.list_length, List.length_map]
  have payload : ((clause.map literalRaw).map (fun literal =>
      ((Encoding.product Encoding.natural Encoding.boolean).encode literal).length)).sum ≤
        clause.length*(2*n+2) := by
    induction clause with
    | nil => simp
    | cons literal rest ih =>
        have first := literal_length_upper literal
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  have header := nat_size_le_self clause.length
  nlinarith

theorem formula_length_upper {n : ℕ} (formula : CNF n) :
    ((Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode
      (formula.map (List.map literalRaw))).length ≤
        3*formula.length+1+formula.width*(2*n+4) := by
  rw [Encoding.list_length, List.length_map]
  have payload : ((formula.map (List.map literalRaw)).map (fun clause =>
      ((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode clause).length)).sum ≤
        formula.width*(2*n+4)+formula.length := by
    induction formula with
    | nil => simp [CNF.width]
    | cons clause rest ih =>
        have first := clause_length_upper clause
        simp only [List.map_cons, List.sum_cons, List.length_cons, CNF.width]
        nlinarith
  have header := nat_size_le_self formula.length
  omega

theorem input_length_upper (input : CNFInput) :
    (codec.encode input).length ≤ 3*input.1+3*input.2.length+2+input.2.width*(2*input.1+4) := by
  rcases input with ⟨n, formula⟩
  have formulaBound := formula_length_upper formula
  have header := nat_size_le_self n
  have table : ((Encoding.list Encoding.boolean).encode (List.replicate n true)).length ≤ 3*n+1 := by
    rw [Encoding.list_length]
    simp only [List.length_replicate, Encoding.boolean, List.length_singleton,
      List.map_const', List.length_replicate, List.sum_replicate, smul_eq_mul, Nat.mul_one]
    omega
  change (rawCodec.encode (toRaw ⟨n, formula⟩)).length ≤
    3*n+3*formula.length+2+formula.width*(2*n+4)
  have length : (rawCodec.encode (toRaw ⟨n, formula⟩)).length =
      ((Encoding.list Encoding.boolean).encode (List.replicate n true)).length +
      ((Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode
        (formula.map (List.map literalRaw))).length := List.length_append
  rw [length]
  omega

theorem input_length_polynomial (input : CNFInput) (bound : ℕ)
    (varBound : input.1 ≤ bound) (clauseBound : input.2.length ≤ bound)
    (occurrenceBound : input.2.width ≤ bound) :
    (codec.encode input).length ≤ bound*(2*bound+10)+2 := by
  have estimate := input_length_upper input
  have payload := Nat.mul_le_mul occurrenceBound (show 2*input.1+4 ≤ 2*bound+4 by omega)
  nlinarith

end Counting.External.CNFEncoding
