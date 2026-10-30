import Counting.EncodingRationalRows
import Counting.LinearSolver
import Counting.StackRationalPositiveIntegral

namespace Counting.Encoding

def optional {α : Type} (codec : Codec α) : Codec (Option α) where
  encode value := match value with
    | none => [false]
    | some value => true::codec.encode value
  decode input := match input with
    | [] => none
    | false::rest => some (none,rest)
    | true::rest => (codec.decode rest).map (fun (value,suffix) => (some value,suffix))
  roundtrip value suffix := by
    cases value with
    | none => rfl
    | some value => simp only [List.cons_append,codec.roundtrip,Option.map_some]

end Counting.Encoding

namespace Counting.PositiveNaturals

def guard (value : Rat) : Bool := decide (value.den=1 ∧ 0<value.num)
def result (row : List Rat) : Option (List Nat) :=
  if row.all guard then some (row.map (fun value => value.num.toNat)) else none
def output (row : List Rat) : List Bool :=
  (Encoding.optional (Encoding.list Encoding.natural)).encode (result row)

theorem guard_scalar (value : Rat) :
    StackMachine.RationalArithmetic.Predicates.positiveIntegralPredicate (Encoding.rational.encode value)=guard value :=
  StackMachine.RationalArithmetic.Predicates.positiveIntegral_correct value

theorem guard_eq (value : Rat) : guard value=(value.den==1 && decide (0<value.num)) := by
  apply Bool.eq_iff_iff.mpr
  simp [guard]

theorem result_executable (row : List Rat) :
    Executable.positiveNaturals? row.toArray = (result row).map List.toArray := by
  have guards : (fun value : Rat => value.den==1 && decide (0<value.num))=guard :=
    funext fun value => (guard_eq value).symm
  simp only [Executable.positiveNaturals?,List.all_toArray,guards,result]
  split <;> simp_all [List.map_toArray]

theorem output_eq (row : List Rat) : output row =
    if row.all guard then true::(Encoding.list Encoding.natural).encode (row.map (fun value => value.num.toNat))
    else [false] := by
  unfold output result
  split <;> rfl

theorem numerator_length (value : Rat) :
    (Encoding.natural.encode value.num.toNat).length ≤ (Encoding.rational.encode value).length := by
  rw [Encoding.natural_length,Encoding.rational_length]
  have magnitude : value.num.toNat ≤ value.num.natAbs := by
    generalize value.num=z
    cases z <;> simp
  have bound := Nat.size_le_size magnitude
  omega

theorem output_sequence_length (row : List Rat) :
    (Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat))).length ≤
      (Encoding.sequence (Encoding.framed Encoding.rational) row).length := by
  induction row with
  | nil => rfl
  | cons value rest ih =>
      simp only [Encoding.sequence,List.map_cons,List.length_append,Encoding.framed_length]
      have bounded := numerator_length value
      omega

end Counting.PositiveNaturals
