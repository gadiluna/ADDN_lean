import Counting.StackEncodingFlaggedCorrectness
import Counting.StackRoutineLists

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def unframeSuffix (input : List Bool) : List Bool :=
  ((Encoding.unframe input).map Prod.snd).getD []

theorem unframe_payload_length (input : List Bool) : (unframePayload input).length≤ input.length := by
  cases parsed : Encoding.unframe input with
  | none => simp [unframePayload,parsed]
  | some pair =>
    obtain ⟨payload,suffix⟩:=pair
    have split:=Machine.unframe_sound input payload suffix parsed
    simp only [unframePayload,parsed,Option.map_some,Option.getD_some]
    rw [split,List.length_append,Encoding.frame_length]
    omega

theorem flagged_result_updates (extra : Nat) (source target temporary flag : Fin (extra+4))
    (st : source≠target) (sw : source≠temporary) (tw : target≠temporary)
    (fs : flag≠source) (ft : flag≠target) (fw : flag≠temporary)
    (store : Fin (extra+4) → List Bool) (empty : store temporary=[]) :
    flaggedResult extra source target temporary flag store =
      Function.update
        (Function.update (Function.update store source (unframeSuffix (store source))) target
          (unframePayload (store source)++store target)) flag
        ((Encoding.unframe (store source)).isSome::store flag) := by
  funext r
  by_cases a : r=source
  · subst r
    unfold flaggedResult
    cases parsed : Encoding.unframe (store source) with
    | none => simp [parserStore,unframeSuffix,unframePayload,parsed,st,Ne.symm fs]
    | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore,unframeSuffix,unframePayload,parsed,st,Ne.symm fs]
  · by_cases b : r=target
    · subst r
      unfold flaggedResult
      cases parsed : Encoding.unframe (store source) with
      | none => simp [parserStore,unframeSuffix,unframePayload,parsed,Ne.symm st,Ne.symm ft]
      | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore,unframeSuffix,unframePayload,parsed,Ne.symm st,Ne.symm ft]
    · by_cases c : r=flag
      · subst r
        unfold flaggedResult
        cases parsed : Encoding.unframe (store source) with
        | none => simp
        | some pair => obtain ⟨payload,suffix⟩:=pair; simp
      · by_cases d : r=temporary
        · subst r
          unfold flaggedResult
          cases parsed : Encoding.unframe (store source) with
          | none => simp [parserStore,Ne.symm sw,Ne.symm tw,Ne.symm fw,empty]
          | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore,Ne.symm sw,Ne.symm tw,Ne.symm fw,empty]
        · unfold flaggedResult
          cases parsed : Encoding.unframe (store source) with
          | none => simp [parserStore,a,b,c,d]
          | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore,a,b,c,d]

theorem canonical_executes (extra : Nat) (source target : Fin (extra+2))
    (distinct : source≠target) (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (canonicalProgram extra source target)) store
      ((store source).length+2)
      (Function.update (Function.update store source []) target (canonicalPayload (store source)::store target)) := by
  have start : canonicalConfig extra source target (canonicalControl extra source target true) store (store source) (store target) =
      (⟨0,store⟩ : Config (canonicalProgram extra source target)) := by
    apply congrArg (Config.mk _)
    funext r
    by_cases a : r=source
    · subst r; simp
    · by_cases b : r=target
      · subst r; simp [a]
      · simp [a,b]
  refine ⟨canonicalConfig extra source target 4 store [] (canonicalPayload (store source)::store target),
    ?_,canonical_halted _ _ _ _ _ _,?_⟩
  · rw [←start]
    exact canonical_run extra source target distinct store (store source) (store target) true
  · funext r
    by_cases a : r=source
    · subst r; simp [canonicalConfig,distinct]
    · by_cases b : r=target
      · subst r; simp [canonicalConfig,Ne.symm distinct]
      · simp [canonicalConfig,a,b]

end Counting.StackMachine.EncodingPrograms
