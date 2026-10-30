import Counting.StackEncodingPair

namespace Counting.StackMachine.EncodingPrograms

structure PairParseResult where
  first : List Bool
  second : List Bool
  suffix : List Bool
  accepted : Bool
  deriving DecidableEq, Repr

/-- On failure, completed first-field data is retained; unfinished payloads
are discarded. This specifies failure stores rather than leaving them free. -/
def parsePair (input : List Bool) : PairParseResult :=
  match Encoding.unframe input with
  | none => ⟨[],[],[],false⟩
  | some (first,rest) => match Encoding.unframe rest with
    | none => ⟨first,[],[],false⟩
    | some (second,suffix) => ⟨first,second,suffix,true⟩

def pairExpected (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : Fin (extra+5) → List Bool :=
  let result := parsePair (store (regs 0))
  fun r => if r=regs 0 then result.suffix
    else if r=regs 1 then result.first++store r
    else if r=regs 2 then result.second++store r
    else if r=regs 3 then []
    else if r=regs 4 then result.accepted::store r
    else store r

set_option maxHeartbeats 1000000 in
theorem pair_result_spec (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (distinct : Function.Injective regs) (store : Fin (extra+5) → List Bool) :
    pairResult extra regs store = pairExpected extra regs store := by
  cases first : Encoding.unframe (store (regs 0)) with
  | none =>
    funext r
    by_cases a : r=regs 0
    · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,distinct.eq_iff,Encoding.unframe]
    · by_cases b : r=regs 1
      · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,distinct.eq_iff,Encoding.unframe]
      · by_cases c : r=regs 2
        · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,distinct.eq_iff,Encoding.unframe]
        · by_cases d : r=regs 3
          · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,distinct.eq_iff,Encoding.unframe]
          · by_cases e : r=regs 4
            · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,distinct.eq_iff,Encoding.unframe]
            · simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,distinct.eq_iff,Encoding.unframe,a,b,c,d,e]
  | some pair =>
    obtain ⟨payload,rest⟩:=pair
    cases second : Encoding.unframe rest with
    | none =>
      funext r
      by_cases a : r=regs 0
      · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
      · by_cases b : r=regs 1
        · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
        · by_cases c : r=regs 2
          · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
          · by_cases d : r=regs 3
            · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
            · by_cases e : r=regs 4
              · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
              · simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff,a,b,c,d,e]
    | some pair =>
      obtain ⟨payload2,suffix⟩:=pair
      funext r
      by_cases a : r=regs 0
      · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
      · by_cases b : r=regs 1
        · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
        · by_cases c : r=regs 2
          · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
          · by_cases d : r=regs 3
            · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
            · by_cases e : r=regs 4
              · subst r; simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff]
              · simp [pairResult,pairFirst,pairSecond,flaggedResult,parserStore,pairExpected,parsePair,first,second,distinct.eq_iff,a,b,c,d,e]

def frameCodec : Encoding.Codec (List Bool) where
  encode := Encoding.frame
  decode := Encoding.unframe
  roundtrip := Encoding.unframe_frame

theorem parsePair_codec (input : List Bool) :
    (Encoding.product frameCodec frameCodec).decode input =
      if (parsePair input).accepted then
        some (((parsePair input).first,(parsePair input).second),(parsePair input).suffix)
      else none := by
  unfold Encoding.product
  dsimp only [frameCodec]
  cases first : Encoding.unframe input with
  | none => simp [first,parsePair]
  | some pair =>
    obtain ⟨payload,rest⟩:=pair
    cases second : Encoding.unframe rest <;> simp [first,second,parsePair]

theorem parsePair_frames (first second suffix : List Bool) :
    parsePair (Encoding.frame first++Encoding.frame second++suffix) = ⟨first,second,suffix,true⟩ := by
  simp only [parsePair,List.append_assoc,Encoding.unframe_frame]

/-- Completed payloads and the retained suffix never exceed the original
input size, including both forms of truncation. -/
theorem parsePair_length_bound (input : List Bool) :
    (parsePair input).first.length+(parsePair input).second.length+
      (parsePair input).suffix.length ≤ input.length := by
  cases first : Encoding.unframe input with
  | none => simp [parsePair,first]
  | some pair =>
    obtain ⟨payload,rest⟩:=pair
    have split := Machine.unframe_sound input payload rest first
    have length : input.length=2*payload.length+1+rest.length := by
      rw [split,List.length_append,Encoding.frame_length]
    cases second : Encoding.unframe rest with
    | none => simp only [parsePair,first,second,List.length_nil,Nat.add_zero]; omega
    | some pair =>
      obtain ⟨payload2,suffix⟩:=pair
      have split2 := Machine.unframe_sound rest payload2 suffix second
      have length2 : rest.length=2*payload2.length+1+suffix.length := by
        rw [split2,List.length_append,Encoding.frame_length]
      simp only [parsePair,first,second]
      omega

theorem pair_executes_spec (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (distinct : Function.Injective regs) (store : Fin (extra+5) → List Bool)
    (scratch : store (regs 3)=[]) :
    ∃ time ≤ 6*(store (regs 0)).length+13,
      Routine.Executes (pairRoutine extra regs) store time (pairExpected extra regs store) := by
  simpa only [pair_result_spec extra regs distinct store] using pair_executes extra regs distinct store scratch

end Counting.StackMachine.EncodingPrograms
