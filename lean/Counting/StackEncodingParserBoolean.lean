import Counting.StackEncodingParserProduct

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def booleanEffect : List Bool → ParseEffect
  | [] => ⟨[],[],false⟩
  | bit::rest => ⟨rest,[bit],true⟩

def booleanItem (registers : Nat) (source status output : Fin (registers+2)) : Routine registers where
  states := 5
  code control := match control.val with
    | 0 => .pop source 3 1 2
    | 1 => .push output false 5
    | 2 => .push output true 5
    | 3 => .pop status 4 4 4
    | 4 => .push status false 5
    | _ => .halt

theorem booleanItem_executes (registers : Nat) (source status output : Fin (registers+2))
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    (store : Routine.Store registers) (accepted : Bool) (tail : List Bool)
    (statusEq : store status=accepted::tail) :
    Routine.Executes (booleanItem registers source status output) store
      (if (store source).isEmpty then 3 else 2)
      (parseStore source status output store accepted tail (booleanEffect (store source))) := by
  cases input : store source with
  | nil =>
    let finish : Config (booleanItem registers source status output).program :=
      ⟨5,Function.update store status (false::tail)⟩
    refine ⟨finish,?_,rfl,?_⟩
    · cases accepted <;> simp [Machine.run,step,booleanItem,input,statusEq,finish]
    · funext r
      by_cases a : r=source
      · subst r; simp [finish,parseStore,booleanEffect,ss,input]
      · by_cases b : r=status
        · subst r; simp [finish,parseStore,booleanEffect,Ne.symm ss]
        · by_cases c : r=output
          · subst r; simp [finish,parseStore,booleanEffect,Ne.symm so,Ne.symm statusOutput]
          · simp [finish,parseStore,a,b,c]
  | cons bit rest =>
    let finish : Config (booleanItem registers source status output).program :=
      ⟨5,Function.update (Function.update store source rest) output (bit::store output)⟩
    refine ⟨finish,?_,rfl,?_⟩
    · cases bit <;> simp [Machine.run,step,booleanItem,input,finish,Ne.symm so]
    · funext r
      by_cases a : r=source
      · subst r; simp [finish,parseStore,booleanEffect,so]
      · by_cases b : r=status
        · subst r; simp [finish,parseStore,booleanEffect,Ne.symm ss,statusOutput,statusEq]
        · by_cases c : r=output
          · subst r; simp [finish,parseStore,booleanEffect,Ne.symm so,Ne.symm statusOutput]
          · simp [finish,parseStore,a,b,c]

def booleanParser (registers : Nat) (source status output : Fin (registers+2))
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output) :
    VerifiedParser registers source status output Bool Encoding.boolean where
  work := ∅
  separate := by simp
  routine := booleanItem registers source status output
  effect := booleanEffect
  coefficient := 4
  exponent := 1
  suffix_le input := by cases input <;> simp [booleanEffect]
  code_le input := by
    cases input <;> simp [booleanEffect,Complexity.polynomial]
    omega
  sound input accepted := by
    cases input with
    | nil => simp [booleanEffect] at accepted
    | cons bit rest => exact ⟨bit,rfl,rfl⟩
  roundtrip _ _ := rfl
  executes store accepted tail statusEq _ := by
    refine ⟨_,?_,booleanItem_executes registers source status output ss so statusOutput store accepted tail statusEq⟩
    simp only [Complexity.polynomial,pow_one]
    split_ifs <;> omega

end Counting.StackMachine.EncodingPrograms
