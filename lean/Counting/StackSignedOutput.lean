import Counting.StackSignedParseAddition
import Counting.StackNormalize
import Counting.StackRoutineMove
import Counting.StackBinaryMultiplyOutput

namespace Counting.StackMachine.Signed
open Routine

set_option backward.isDefEq.respectTransparency false

def canonicalSign (sign : Bool) (magnitude : Nat) : Bool := if magnitude=0 then false else sign

theorem signed_natAbs (sign : Bool) (magnitude : Nat) :
    (Encoding.signedValue sign magnitude).natAbs = magnitude := by
  cases sign <;> simp [Encoding.signedValue]

theorem signed_negative (sign : Bool) (magnitude : Nat) :
    Encoding.negative (Encoding.signedValue sign magnitude) = canonicalSign sign magnitude := by
  cases sign <;> cases magnitude <;> simp [Encoding.negative,Encoding.signedValue,canonicalSign]
  all_goals omega

theorem signed_integer_encode (sign : Bool) (magnitude : Nat) :
    Encoding.integer.encode (Encoding.signedValue sign magnitude) =
      canonicalSign sign magnitude::Encoding.natural.encode magnitude := by
  rw [Encoding.integer_encode,signed_negative,signed_natAbs]

/-- A canonical natural frame is empty exactly when its first marker is
false. Inspect and restore that marker; reset the sign only in this case. -/
def fixSign : Routine 10 where
  states := 5
  code state := match state.val with
    | 0 => .pop 2 1 1 4
    | 1 => .push 2 false 2
    | 2 => .pop 10 3 3 3
    | 3 => .push 10 false 5
    | 4 => .push 2 true 5
    | _ => .halt

theorem fixSign_frame (input payload : List Bool) (sign : Bool) :
    Executes fixSign (file input (Encoding.frame payload) [] [] [] [] [sign] [] [])
      (if payload=[] then 4 else 2)
      (file input (Encoding.frame payload) [] [] [] [] [if payload=[] then false else sign] [] []) := by
  cases payload with
  | nil =>
      refine ⟨⟨5,file input (Encoding.frame []) [] [] [] [] [false] [] []⟩,?_,rfl,rfl⟩
      cases sign <;> apply congrArg some <;> apply congrArg (Config.mk _)
      all_goals funext r; fin_cases r <;> rfl
  | cons bit rest =>
      refine ⟨⟨5,file input (Encoding.frame (bit::rest)) [] [] [] [] [sign] [] []⟩,?_,rfl,rfl⟩
      apply congrArg some
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl

theorem fixSign_executes (input : List Bool) (magnitude : Nat) (sign : Bool) :
    ∃ time ≤ 4,
      Executes fixSign (file input (Encoding.natural.encode magnitude) [] [] [] [] [sign] [] []) time
        (file input (Encoding.natural.encode magnitude) [] [] [] [] [canonicalSign sign magnitude] [] []) := by
  have zero : magnitude.bits=[] ↔ magnitude=0 := by
    constructor
    · intro equal
      have := congrArg Encoding.value equal
      simpa [Encoding.value] using this
    · rintro rfl; rfl
  refine ⟨if magnitude.bits=[] then 4 else 2,by split_ifs <;> omega,?_⟩
  simpa only [canonicalSign,zero,Encoding.natural] using fixSign_frame input magnitude.bits sign

abbrev formatMagnitude : Routine 10 := Normalize.formatRoutine 9 1 2 7
abbrev signFrame : Routine 10 := readSign 10 2
abbrev moveOutput : Routine 10 := Routine.move 9 2 1 7
abbrev formatOutput : Routine 10 := sequence formatMagnitude
  (sequence fixSign (sequence signFrame moveOutput))

theorem formatOutput_executes (input payload : List Bool) (sign : Bool) :
    ∃ time ≤ 17*payload.length+29,
      Executes formatOutput (file input [] [] [] [] payload [sign] [] []) time
        (file input [] [] [] [] (Encoding.integer.encode (value sign payload)) [] [] []) := by
  let magnitude := Encoding.value payload
  let framed := Encoding.natural.encode magnitude
  let signed := Encoding.integer.encode (value sign payload)
  have formatted := Normalize.format_executes 9 1 2 7 (by decide) (by decide) (by decide)
    (file input [] [] [] [] payload [sign] [] []) rfl
  change Executes formatMagnitude (file input [] [] [] [] payload [sign] [] [])
    (Normalize.formatCost payload)
    (Function.update (Function.update (file input [] [] [] [] payload [sign] [] []) 1 []) 2 (framed++[])) at formatted
  have formattedStore : Function.update (Function.update (file input [] [] [] [] payload [sign] [] []) 1 []) 2 (framed++[]) =
      file input framed [] [] [] [] [sign] [] [] := by
    funext r; fin_cases r <;> simp [file]
  rw [formattedStore] at formatted
  obtain ⟨fixTime,fixBound,fixed⟩ := fixSign_executes input magnitude sign
  have framedSign := readSign_executes (registers := 10) 10 2 (by decide)
    (file input framed [] [] [] [] [canonicalSign sign magnitude] [] [])
  change Executes signFrame (file input framed [] [] [] [] [canonicalSign sign magnitude] [] []) 2
    (Function.update (Function.update (file input framed [] [] [] [] [canonicalSign sign magnitude] [] []) 10 []) 2
      (canonicalSign sign magnitude::framed)) at framedSign
  have signStore : Function.update (Function.update
      (file input framed [] [] [] [] [canonicalSign sign magnitude] [] []) 10 []) 2
      (canonicalSign sign magnitude::framed) = file input signed [] [] [] [] [] [] [] := by
    have representation : signed = canonicalSign sign magnitude::framed := signed_integer_encode sign magnitude
    rw [representation]
    funext r; fin_cases r <;> rfl
  rw [signStore] at framedSign
  have moved := move_executes 9 2 1 7 (by decide) (by decide) (by decide)
    (file input signed [] [] [] [] [] [] []) rfl
  change Executes moveOutput (file input signed [] [] [] [] [] [] []) (6*signed.length+4)
    (Function.update (Function.update (file input signed [] [] [] [] [] [] []) 1 (signed++[])) 2 []) at moved
  have movedStore : Function.update (Function.update (file input signed [] [] [] [] [] [] []) 1 (signed++[])) 2 [] =
      file input [] [] [] [] signed [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  rw [movedStore] at moved
  refine ⟨_,?_,formatted.sequence (fixed.sequence (framedSign.sequence moved))⟩
  have formatBound := Normalize.formatCost_le payload
  have naturalBound := Binary.natural_value_length payload
  have signedLength : signed.length ≤ 2*payload.length+2 := by
    change (Encoding.integer.encode (Encoding.signedValue sign (Encoding.value payload))).length ≤ _
    rw [signed_integer_encode,List.length_cons]
    omega
  omega

end Counting.StackMachine.Signed
