import Counting.ExternalCNFClause

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine

@[simp] theorem literal_length_negate (literal : Nat×Bool) :
    (literalCodec.encode (literal.1,!literal.2)).length=(literalCodec.encode literal).length := by
  simp [literalCodec,Encoding.product,Encoding.boolean]

theorem literal_member_sequence_length (literals : List (Nat×Bool)) (literal : Nat×Bool)
    (member : literal∈literals) :
    (literalCodec.encode literal).length≤(Encoding.sequence literalCodec literals).length := by
  induction literals with
  | nil => contradiction
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | inRest
    · simp [Encoding.sequence]
    · exact (ih inRest).trans (by simp [Encoding.sequence])

theorem headD_drop_length_le (literals : List (Nat×Bool)) (j terminal limit : Nat)
    (items : ∀ literal∈literals,(literalCodec.encode literal).length≤limit)
    (terminalBound : terminal≤limit) :
    (literalCodec.encode ((literals.drop j).headD (terminal,true))).length≤2*limit+2 := by
  cases dropped : literals.drop j with
  | nil => simpa using (literal_length_le terminal true).trans (by omega)
  | cons literal rest =>
    have member : literal∈literals := List.mem_of_mem_drop (by rw [dropped];exact List.mem_cons_self)
    have bound := items literal member
    simpa using (bound.trans (by omega : limit≤2*limit+2))

theorem gateCode_bound (literals : List (Nat×Bool)) (current width limit : Nat)
    (items : ∀ literal∈literals,(literalCodec.encode literal).length≤limit)
    (fresh : current+width≤limit) (j : Nat) (less : j<width) (i : Fin 6) :
    (literalCodec.encode (gateSource (current+j) ((literals.drop j).headD (current+width,true)) i)).length≤2*limit+2 := by
  have cur : current+j≤limit := by omega
  have nxt : current+j+1≤limit := by omega
  have a := (literal_length_le (current+j) true).trans (show 2*(current+j)+2≤2*limit+2 by omega)
  have b := (literal_length_le (current+j) false).trans (show 2*(current+j)+2≤2*limit+2 by omega)
  have c := (literal_length_le (current+j+1) true).trans (show 2*(current+j+1)+2≤2*limit+2 by omega)
  have d := (literal_length_le (current+j+1) false).trans (show 2*(current+j+1)+2≤2*limit+2 by omega)
  have e := headD_drop_length_le literals j (current+width) limit items fresh
  fin_cases i
  · exact a
  · exact b
  · exact c
  · exact d
  · exact e
  · change (literalCodec.encode (((literals.drop j).headD (current+width,true)).1,!((literals.drop j).headD (current+width,true)).2)).length≤2*limit+2
    rw [literal_length_negate]
    exact e

/-- The numerical gate-size hypothesis of the compositional loop follows
from actual serialized input length and the explicit fresh-variable range. -/
theorem gateCode_source_bound (literals : List (Nat×Bool)) (suffix : List Bool) (current width limit : Nat)
    (source : ((Encoding.list literalCodec).encode literals++suffix).length≤limit)
    (fresh : current+width≤limit) (j : Nat) (less : j<width) (i : Fin 6) :
    (literalCodec.encode (gateSource (current+j) ((literals.drop j).headD (current+width,true)) i)).length≤2*limit+2 := by
  apply gateCode_bound literals current width limit ?_ fresh j less i
  intro literal member
  apply (literal_member_sequence_length literals literal member).trans
  simp only [Encoding.list,List.length_append] at source
  omega

end Counting.External.CNFMachine
