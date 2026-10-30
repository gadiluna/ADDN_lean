import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Explicit binary encodings. Natural numbers use little-endian bits, with
zero encoded by the empty bit string. A self-delimiting frame prefixes every
payload bit by `true` and terminates with `false`; parsers retain the unused
suffix. No multiplicity is expanded into repeated messages. -/
namespace Counting.Encoding

def value : List Bool → Nat
  | [] => 0
  | bit :: bits => Nat.bit bit (value bits)

@[simp] theorem value_bits (n : Nat) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit bit n admissible ih => rw [Nat.bits_append_bit n bit admissible, value, ih]

theorem bits_injective : Function.Injective Nat.bits := fun _ _ same => by
  simpa only [value_bits] using congrArg value same

theorem bits_length (n : Nat) : n.bits.length = n.size := Nat.size_eq_bits_len n

theorem bits_length_le_iff (n bound : Nat) : n.bits.length ≤ bound ↔ n < 2 ^ bound := by
  rw [bits_length, Nat.size_le]

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def unframe : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: bit :: rest => (unframe rest).map (fun (bits, suffix) => (bit :: bits, suffix))
  | _ => none

@[simp] theorem unframe_frame (bits suffix : List Bool) :
    unframe (frame bits ++ suffix) = some (bits, suffix) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [frame, List.cons_append, unframe, ih, Option.map_some]

@[simp] theorem frame_length (bits : List Bool) : (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

/-- A compositional, executable prefix codec, including an exact inverse on
every appended suffix. Invalid encodings may return `none`. -/
structure Codec (α : Type) where
  encode : α → List Bool
  decode : List Bool → Option (α × List Bool)
  roundtrip : ∀ value suffix, decode (encode value ++ suffix) = some (value, suffix)

theorem Codec.injective {α : Type} (codec : Codec α) : Function.Injective codec.encode := by
  intro a b same
  have := congrArg (fun bits => codec.decode (bits ++ [])) same
  simpa only [codec.roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using this

/-- Reject suffixes and noncanonical codes, including redundant high zero
bits in natural fields. This is a total executable parser. -/
def Codec.decodeExact {α : Type} (codec : Codec α) (input : List Bool) : Option α :=
  match codec.decode input with
  | none => none
  | some (value, suffix) =>
      if suffix = [] ∧ codec.encode value = input then some value else none

theorem Codec.decodeExact_iff {α : Type} (codec : Codec α) (input : List Bool) (value : α) :
    codec.decodeExact input = some value ↔ codec.encode value = input := by
  constructor
  · unfold Codec.decodeExact
    cases decoded : codec.decode input with
    | none => simp
    | some pair =>
        rcases pair with ⟨other, suffix⟩
        dsimp only
        split_ifs with checked
        · intro equal
          exact Option.some.inj equal ▸ checked.2
        · simp
  · intro equal
    subst input
    have decoded : codec.decode (codec.encode value) = some (value, []) := by
      simpa only [List.append_nil] using codec.roundtrip value []
    simp only [Codec.decodeExact, decoded, and_self, ite_true]

def transport {α β : Type} (codec : Codec α) (encode : β → α) (decode : α → β)
    (inverse : ∀ value, decode (encode value) = value) : Codec β where
  encode value := codec.encode (encode value)
  decode input := (codec.decode input).map (fun (value, rest) => (decode value, rest))
  roundtrip value suffix := by simp only [codec.roundtrip, Option.map_some, inverse]

def natural : Codec Nat where
  encode n := frame n.bits
  decode input := (unframe input).map (fun (bits, suffix) => (value bits, suffix))
  roundtrip n suffix := by simp only [unframe_frame, Option.map_some, value_bits]

@[simp] theorem natural_length (n : Nat) : (natural.encode n).length = 2 * n.size + 1 := by
  exact (frame_length n.bits).trans (by rw [bits_length])

def boolean : Codec Bool where
  encode bit := [bit]
  decode input := match input with | [] => none | bit :: rest => some (bit, rest)
  roundtrip _ _ := rfl

def product {α β : Type} (first : Codec α) (second : Codec β) : Codec (α × β) where
  encode pair := first.encode pair.1 ++ second.encode pair.2
  decode input := do
    let (a, rest) ← first.decode input
    let (b, suffix) ← second.decode rest
    pure ((a, b), suffix)
  roundtrip pair suffix := by
    simp only [List.append_assoc, first.roundtrip, second.roundtrip, bind, pure, Option.bind_some]

def sequence {α : Type} (codec : Codec α) : List α → List Bool
  | [] => []
  | head :: tail => codec.encode head ++ sequence codec tail

def parseCount {α : Type} (codec : Codec α) : Nat → List Bool → Option (List α × List Bool)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (head, rest) ← codec.decode input
      let (tail, suffix) ← parseCount codec count rest
      pure (head :: tail, suffix)

@[simp] theorem parseCount_sequence {α : Type} (codec : Codec α) (values : List α) (suffix : List Bool) :
    parseCount codec values.length (sequence codec values ++ suffix) = some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.length_cons, sequence, List.append_assoc, parseCount, codec.roundtrip,
        bind, pure, Option.bind_some, ih]

def list {α : Type} (codec : Codec α) : Codec (List α) where
  encode values := natural.encode values.length ++ sequence codec values
  decode input := do
    let (count, rest) ← natural.decode input
    parseCount codec count rest
  roundtrip values suffix := by
    simp only [List.append_assoc, natural.roundtrip, bind, Option.bind_some, parseCount_sequence]

theorem sequence_length {α : Type} (codec : Codec α) (values : List α) :
    (sequence codec values).length = (values.map (fun a => (codec.encode a).length)).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [sequence, List.length_append, ih, List.map_cons, List.sum_cons]

theorem list_length {α : Type} (codec : Codec α) (values : List α) :
    ((list codec).encode values).length = 2 * values.length.size + 1 +
      (values.map (fun a => (codec.encode a).length)).sum := by
  simp only [list, List.length_append, natural_length, sequence_length]

theorem natural_list_length_le (values : List Nat) (bound : Nat)
    (bounded : ∀ value ∈ values, value ≤ bound) :
    ((list natural).encode values).length ≤
      2 * values.length.size + 1 + values.length * (2 * bound.size + 1) := by
  rw [list_length]
  apply Nat.add_le_add_left
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons head tail ih =>
      have hhead := Nat.size_le_size (bounded head List.mem_cons_self)
      have htail := ih (fun value member => bounded value (List.mem_cons_of_mem head member))
      simp only [List.map_cons, List.sum_cons, natural_length, List.length_cons]
      simp only [natural_length] at htail
      nlinarith

def pairWords (first second : List Bool) : List Bool := frame first ++ second

theorem pairWords_injective : Function.Injective (fun pair : List Bool × List Bool =>
    pairWords pair.1 pair.2) := by
  intro a b equal
  have := congrArg unframe equal
  simpa only [pairWords, unframe_frame, Option.some.injEq, Prod.eta] using this

theorem pairWords_length (first second : List Bool) :
    (pairWords first second).length = 2 * first.length + 1 + second.length := by
  simp only [pairWords, List.length_append, frame_length]

end Counting.Encoding
