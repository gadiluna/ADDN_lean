import Counting.ExternalCellular

namespace Counting.External.WitnessWord
open Machine

def permitted (symbol : Symbol) : Prop := symbol = .blank ∨ symbol = .zero ∨ symbol = .one

instance (symbol : Symbol) : Decidable (permitted symbol) := inferInstanceAs
  (Decidable (symbol = .blank ∨ symbol = .zero ∨ symbol = .one))

def read (witness : List Bool) (position : ℕ) : Symbol :=
  ((witness.map bitSymbol)[position]?).getD .blank

@[simp] theorem read_nil (position : ℕ) : read [] position = .blank := by simp [read]

@[simp] theorem read_cons_zero (bit : Bool) (rest : List Bool) :
    read (bit::rest) 0 = bitSymbol bit := rfl

@[simp] theorem read_cons_succ (bit : Bool) (rest : List Bool) (position : ℕ) :
    read (bit::rest) (position+1) = read rest position := by simp [read]

theorem read_permitted (witness : List Bool) (position : ℕ) : permitted (read witness position) := by
  induction witness generalizing position with
  | nil => simp [permitted]
  | cons bit rest ih =>
      cases position with
      | zero => cases bit <;> simp [bitSymbol, permitted]
      | succ position => exact ih position

theorem read_blank_iff (witness : List Bool) (position : ℕ) :
    read witness position = .blank ↔ witness.length ≤ position := by
  induction witness generalizing position with
  | nil => simp
  | cons bit rest ih =>
      cases position with
      | zero => simp [bitSymbol_ne_blank]
      | succ position => simpa using ih position

theorem read_blank_forward (witness : List Bool) (first second : ℕ) (ordered : first ≤ second)
    (blank : read witness first = .blank) : read witness second = .blank :=
  (read_blank_iff witness second).mpr (((read_blank_iff witness first).mp blank).trans ordered)

theorem read_append (first second : List Bool) (position : ℕ) :
    read (first++second) position =
      if position < first.length then read first position else read second (position-first.length) := by
  simp only [read, List.map_append, List.getElem?_append, List.length_map]
  split <;> rfl

/-- Adjacent blank propagation forces one cutoff. It neither fixes nor
silently pads the certificate length supplied to the verifier. -/
theorem exists_word (width : ℕ) (symbols : Fin width → Symbol)
    (valid : ∀ position, permitted (symbols position))
    (closed : ∀ first second : Fin width, first.val+1 = second.val →
      symbols first = .blank → symbols second = .blank) :
    ∃ witness : List Bool, witness.length ≤ width ∧
      ∀ position, symbols position = read witness position.val := by
  induction width with
  | zero => exact ⟨[], by simp, fun position => Fin.elim0 position⟩
  | succ width ih =>
      obtain headBlank | headZero | headOne := valid 0
      · refine ⟨[], by simp, ?_⟩
        intro position
        simp only [read_nil]
        induction position using Fin.induction with
        | zero => exact headBlank
        | succ position prev => exact closed position.castSucc position.succ rfl prev
      · obtain ⟨tail, tailBound, tailEq⟩ := ih (fun position => symbols position.succ)
          (fun position => valid position.succ)
          (fun first second adjacent => closed first.succ second.succ (by simpa using adjacent))
        refine ⟨false::tail, by simpa using Nat.succ_le_succ tailBound, ?_⟩
        intro position
        refine Fin.cases ?_ (fun position => ?_) position
        · exact headZero
        · exact tailEq position
      · obtain ⟨tail, tailBound, tailEq⟩ := ih (fun position => symbols position.succ)
          (fun position => valid position.succ)
          (fun first second adjacent => closed first.succ second.succ (by simpa using adjacent))
        refine ⟨true::tail, by simpa using Nat.succ_le_succ tailBound, ?_⟩
        intro position
        refine Fin.cases ?_ (fun position => ?_) position
        · exact headOne
        · exact tailEq position

theorem exists_word_iff (width : ℕ) (symbols : Fin width → Symbol) :
    (∃ witness : List Bool, witness.length ≤ width ∧
      ∀ position, symbols position = read witness position.val) ↔
      (∀ position, permitted (symbols position)) ∧
      (∀ first second : Fin width, first.val+1 = second.val →
        symbols first = .blank → symbols second = .blank) := by
  constructor
  · rintro ⟨witness, _, equal⟩
    constructor
    · intro position
      rw [equal]
      exact read_permitted witness position.val
    · intro first second adjacent blank
      rw [equal] at blank ⊢
      exact read_blank_forward witness first.val second.val (by omega) blank
  · exact fun ⟨valid, closed⟩ => exists_word width symbols valid closed

end Counting.External.WitnessWord
