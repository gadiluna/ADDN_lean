import Counting.EncodingSigned

namespace Counting.Encoding

/-- A scalar field in the internal matrix tape has one outer frame. Its
payload is the unchanged canonical scalar codec. The outer delimiter lets
finite machines extract fields without interpreting rational arithmetic. -/
def framed {α : Type} (codec : Codec α) : Codec α where
  encode value := frame (codec.encode value)
  decode input := do
    let (payload,suffix) ← unframe input
    let value ← codec.decodeExact payload
    pure (value,suffix)
  roundtrip value suffix := by
    simp only [unframe_frame,bind,Option.bind_some,
      (codec.decodeExact_iff _ _).mpr rfl,pure]

@[simp] theorem framed_length {α : Type} (codec : Codec α) (value : α) :
    ((framed codec).encode value).length = 2*(codec.encode value).length+1 :=
  frame_length _

def rationalRow : Codec (List Rat) := list (framed rational)
/-- Outer row frames permit indexed access without expanding or interpreting
the coefficients in the skipped rows. -/
def rationalMatrix : Codec (List (List Rat)) := list (framed rationalRow)

theorem rational_field_length_pos (value : Rat) : 0<(rational.encode value).length := by
  rw [rational_length]
  omega

theorem framed_sequence_length_le {α : Type} (codec : Codec α)
    (positive : ∀ value,0<(codec.encode value).length) (values : List α) :
    (sequence (framed codec) values).length ≤ 3*(sequence codec values).length := by
  induction values with
  | nil => simp [sequence]
  | cons value rest ih =>
    simp only [sequence,List.length_append,framed_length]
    have nonempty := positive value
    omega

theorem rationalRow_length_le (row : List Rat) :
    (rationalRow.encode row).length ≤ 3*((list rational).encode row).length := by
  change (natural.encode row.length++sequence (framed rational) row).length ≤
    3*(natural.encode row.length++sequence rational row).length
  simp only [List.length_append]
  have bounded := framed_sequence_length_le rational rational_field_length_pos row
  omega

theorem rationalRow_roundtrip (row : List Rat) (suffix : List Bool) :
    rationalRow.decode (rationalRow.encode row++suffix) = some (row,suffix) := rationalRow.roundtrip row suffix

theorem rationalRow_injective : Function.Injective rationalRow.encode := rationalRow.injective

end Counting.Encoding
