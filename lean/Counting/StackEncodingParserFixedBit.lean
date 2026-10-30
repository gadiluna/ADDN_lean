import Counting.StackEncodingParserBoolean

namespace Counting.Encoding

/-- A singleton grammar: a single prescribed bit, with no payload value. -/
def fixedBit (expected : Bool) : Codec Unit where
  encode _ := [expected]
  decode input := match input with
    | [] => none
    | bit::rest => if bit=expected then some ((),rest) else none
  roundtrip value suffix := by cases value;simp

end Counting.Encoding

namespace Counting.StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def fixedBitEffect (expected : Bool) : List Bool → ParseEffect
  | [] => ⟨[],[],false⟩
  | bit::rest => ⟨rest,[bit],bit==expected⟩

def fixedBitItem (expected : Bool) (registers : Nat) (source status output : Fin (registers+2)) : Routine registers where
  states := 7
  code control := match control.val with
    | 0 => .pop source 5 1 2
    | 1 => .push output false (if expected then 5 else 7)
    | 2 => .push output true (if expected then 7 else 5)
    | 5 => .pop status 6 6 6
    | 6 => .push status false 7
    | _ => .halt

theorem fixedBitItem_executes (expected : Bool) (registers : Nat) (source status output : Fin (registers+2))
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    (store : Routine.Store registers) (accepted : Bool) (tail : List Bool)
    (statusEq : store status=accepted::tail) :
    ∃ time ≤ 4,
      Routine.Executes (fixedBitItem expected registers source status output) store time
        (parseStore source status output store accepted tail (fixedBitEffect expected (store source))) := by
  cases input : store source with
  | nil =>
    let finish : Config (fixedBitItem expected registers source status output).program :=
      ⟨7,Function.update store status (false::tail)⟩
    refine ⟨3,by decide,finish,?_,rfl,?_⟩
    · cases accepted <;> simp [Machine.run,step,fixedBitItem,input,statusEq,finish]
    · funext r
      by_cases a : r=source
      · subst r;simp [finish,parseStore,fixedBitEffect,ss,input]
      · by_cases b : r=status
        · subst r;simp [finish,parseStore,fixedBitEffect,Ne.symm ss]
        · by_cases c : r=output
          · subst r;simp [finish,parseStore,fixedBitEffect,Ne.symm so,Ne.symm statusOutput]
          · simp [finish,parseStore,a,b,c]
  | cons bit rest =>
    let finish : Config (fixedBitItem expected registers source status output).program :=
      ⟨7,Function.update (Function.update (Function.update store source rest) output (bit::store output))
        status ((accepted && (bit==expected))::tail)⟩
    refine ⟨if bit=expected then 2 else 4,by split_ifs <;> decide,finish,?_,rfl,?_⟩
    · cases bit <;> cases expected <;> cases accepted <;>
        simp [Machine.run,step,fixedBitItem,input,finish,statusEq,Ne.symm so,Ne.symm ss,statusOutput]
    · funext r
      by_cases a : r=source
      · subst r;simp [finish,parseStore,fixedBitEffect,ss,so]
      · by_cases b : r=status
        · subst r;simp [finish,parseStore,fixedBitEffect,Ne.symm ss]
        · by_cases c : r=output
          · subst r;simp [finish,parseStore,fixedBitEffect,Ne.symm so,Ne.symm statusOutput]
          · simp [finish,parseStore,a,b,c]

def fixedBitParser (expected : Bool) (registers : Nat) (source status output : Fin (registers+2))
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output) :
    VerifiedParser registers source status output Unit (Encoding.fixedBit expected) where
  work := ∅
  separate := by simp
  routine := fixedBitItem expected registers source status output
  effect := fixedBitEffect expected
  coefficient := 4
  exponent := 1
  suffix_le input := by cases input <;> simp [fixedBitEffect]
  code_le input := by
    cases input <;> simp [fixedBitEffect,Complexity.polynomial]
    omega
  sound input accepted := by
    cases input with
    | nil => simp [fixedBitEffect] at accepted
    | cons bit rest =>
      have same : bit=expected := by simpa only [fixedBitEffect,beq_iff_eq] using accepted
      subst bit
      exact ⟨(),rfl,rfl⟩
  roundtrip value suffix := by cases value;simp [Encoding.fixedBit,fixedBitEffect]
  executes store accepted tail statusEq _ := by
    obtain ⟨time,bounded,ran⟩ := fixedBitItem_executes expected registers source status output ss so statusOutput store accepted tail statusEq
    exact ⟨time,by simp only [Complexity.polynomial,pow_one];omega,ran⟩

end Counting.StackMachine.EncodingPrograms
