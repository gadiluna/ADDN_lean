import Counting.MachineFrame
import Counting.MachineStride

namespace Counting.Machine

/-- Validate one complete frame with no suffix, then position the head on
its first payload cell. Invalid frames or nonempty witnesses halt rejecting. -/
def frameBoot : Program where
  states := 6
  code state symbol := match state.val, symbol with
    | 0, .one => some (1, .move .right)
    | 0, .zero => some (2, .write .zero)
    | 1, .one | 1, .zero => some (0, .move .right)
    | 2, _ => some (3, .move .right)
    | 3, .blank => some (4, .move .left)
    | 4, .blank => some (5, .move .right)
    | 4, _ => some (4, .move .left)
    | 5, _ => some (6, .move .right)
    | _, _ => none
  accept state := state == 6

def frameEmbedding (config : Config frameProgram) : Config frameBoot :=
  ⟨⟨config.control.val, by have := config.control.isLt; change config.control.val < 3 at this; change config.control.val < 7; omega⟩, config.tape⟩

theorem frameEmbedding_step (config next : Config frameProgram)
    (success : step frameProgram config = some next) :
    step frameBoot (frameEmbedding config) = some (frameEmbedding next) := by
  rcases config with ⟨control, ⟨left, head, right⟩⟩
  fin_cases control <;> cases head <;>
    simp_all [step, frameProgram, frameBoot, frameEmbedding] <;> subst next <;> exact ⟨rfl, rfl⟩

theorem frameEmbedding_run (steps : Nat) (config next : Config frameProgram)
    (success : run (step frameProgram) steps config = some next) :
    run (step frameBoot) steps (frameEmbedding config) = some (frameEmbedding next) := by
  induction steps generalizing config with
  | zero => exact congrArg some (congrArg frameEmbedding (Option.some.inj success))
  | succ steps ih =>
      cases first : step frameProgram config with
      | none => simp only [run, first, Option.bind_none] at success; contradiction
      | some middle =>
          have rest : run (step frameProgram) steps middle = some next := by
            simpa only [run, first, Option.bind_some] using success
          rw [run, frameEmbedding_step config middle first, Option.bind_some]
          exact ih middle rest

theorem frameEmbedding_reject (config : Config frameProgram)
    (halted : step frameProgram config = none) (rejected : frameProgram.accept config.control = false) :
    step frameBoot (frameEmbedding config) = none ∧ frameBoot.accept (frameEmbedding config).control = false := by
  rcases config with ⟨control, ⟨left, head, right⟩⟩
  fin_cases control <;> cases head <;>
    simp_all [step, frameProgram, frameBoot, frameEmbedding]

theorem frameBoot_malformed (input : List Bool) (malformed : Encoding.unframe input = none) :
    ∃ steps output, steps ≤ input.length ∧ HaltsAt frameBoot input steps output ∧
      frameBoot.accept output.control = false := by
  have rejected : frameProgram.accept (frameScan [] input).2.control = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have parsed := (frameScan_accepts [] input).mp accepted
    simp only [malformed, Option.isSome_none, Bool.false_eq_true] at parsed
  obtain ⟨halted, reject⟩ := frameEmbedding_reject _ (frameScan_halted [] input) rejected
  exact ⟨_, _, frameScan_steps [] input,
    ⟨frameEmbedding_run _ _ _ (frameScan_run [] input), halted⟩, reject⟩

def packed : List Bool → List Symbol
  | [] => []
  | bit :: rest => .one :: bitSymbol bit :: packed rest

theorem packed_length (input : List Bool) : (packed input).length = 2 * input.length := by
  induction input with
  | nil => rfl
  | cons bit rest ih => simp only [packed, List.length_cons, ih]; omega

theorem frame_symbols (input : List Bool) :
    (Encoding.frame input).map bitSymbol = packed input ++ [.zero] := by
  induction input with
  | nil => rfl
  | cons bit rest ih => simp only [Encoding.frame, List.map_cons, packed, List.cons_append, ih]; rfl

theorem packed_nonblank (input : List Bool) : ∀ symbol ∈ packed input, symbol ≠ .blank := by
  induction input with
  | nil => simp only [packed, List.not_mem_nil, false_implies, forall_const]
  | cons bit rest ih =>
      intro symbol present
      simp only [packed, List.mem_cons] at present
      rcases present with rfl | rfl | present
      · decide
      · exact bitSymbol_ne_blank bit
      · exact ih symbol present

theorem unframe_sound (input payload suffix : List Bool)
    (parsed : Encoding.unframe input = some (payload, suffix)) : input = Encoding.frame payload ++ suffix := by
  induction input using List.twoStepInduction generalizing payload with
  | nil => contradiction
  | singleton bit =>
      cases bit with
      | false => cases Option.some.inj parsed; rfl
      | true => contradiction
  | cons_cons flag bit rest ih _ =>
      cases flag with
      | false => cases Option.some.inj parsed; rfl
      | true =>
          obtain ⟨pair, decoded, equal⟩ := Option.map_eq_some_iff.mp parsed
          rcases pair with ⟨bits, remaining⟩
          obtain ⟨parts, suffixEqual⟩ := Prod.mk.inj equal
          subst payload remaining
          simpa only [Encoding.frame, List.cons_append] using congrArg (fun tail => true :: bit :: tail) (ih bits decoded)

theorem frameBoot_scan (left : List Symbol) (payload suffix : List Bool) :
    run (step frameBoot) (2 * payload.length + 1)
      ⟨0, ⟨left, ((Encoding.frame payload ++ suffix).map bitSymbol).headD .blank,
        ((Encoding.frame payload ++ suffix).map bitSymbol).tail⟩⟩ =
      some ⟨2, ⟨(packed payload).reverse ++ left, .zero, suffix.map bitSymbol⟩⟩ := by
  induction payload generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      rw [show 2 * (bit :: rest).length + 1 = 2 + (2 * rest.length + 1) by simp; omega, run_add]
      have first : run (step frameBoot) 2
          ⟨0, ⟨left, ((Encoding.frame (bit :: rest) ++ suffix).map bitSymbol).headD .blank,
            ((Encoding.frame (bit :: rest) ++ suffix).map bitSymbol).tail⟩⟩ =
          some ⟨0, ⟨bitSymbol bit :: .one :: left,
            ((Encoding.frame rest ++ suffix).map bitSymbol).headD .blank,
            ((Encoding.frame rest ++ suffix).map bitSymbol).tail⟩⟩ := by cases bit <;> rfl
      rw [first, Option.bind_some, ih]
      simp only [packed, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

def bootOutput (payload : List Bool) : Tape :=
  ((⟨[], .blank, (Encoding.frame payload).map bitSymbol ++ [.blank]⟩ : Tape).move .right).move .right

theorem frameBoot_rewind (backwards right : List Symbol)
    (nonblank : ∀ symbol ∈ backwards, symbol ≠ .blank) :
    run (step frameBoot) backwards.length
      ⟨4, ⟨backwards.tail, backwards.headD .blank, right⟩⟩ =
      some ⟨4, ⟨[], .blank, backwards.reverse ++ right⟩⟩ := by
  induction backwards generalizing right with
  | nil => rfl
  | cons head rest ih =>
      have notBlank := nonblank head List.mem_cons_self
      have first : step frameBoot ⟨4, ⟨rest, head, right⟩⟩ =
          some ⟨4, ⟨rest.tail, rest.headD .blank, head :: right⟩⟩ := by
        cases head <;> simp_all [step, frameBoot, Tape.move]
      simp only [List.length_cons, List.tail_cons, List.headD_cons, run, first, Option.bind_some]
      rw [ih (head :: right) (fun symbol present => nonblank symbol (List.mem_cons_of_mem head present))]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem frameBoot_frame (payload : List Bool) :
    HaltsAt frameBoot (Encoding.frame payload) (4 * payload.length + 6) ⟨6, bootOutput payload⟩ := by
  have scan := frameBoot_scan [] payload []
  simp only [List.append_nil, List.map_nil] at scan
  have rewind := frameBoot_rewind (.zero :: (packed payload).reverse) [.blank] (by
    intro symbol present
    simp only [List.mem_cons, List.mem_reverse] at present
    rcases present with rfl | present
    · decide
    · exact packed_nonblank payload symbol present)
  have backwardsLength : (.zero :: (packed payload).reverse).length = 2 * payload.length + 1 := by
    simp only [List.length_cons, List.length_reverse, packed_length]
  rw [backwardsLength] at rewind
  simp only [List.tail_cons, List.headD_cons] at rewind
  constructor
  · change run (step frameBoot) (4 * payload.length + 6)
      ⟨0, ⟨[], ((Encoding.frame payload).map bitSymbol).headD .blank,
        ((Encoding.frame payload).map bitSymbol).tail⟩⟩ = _
    rw [show 4 * payload.length + 6 = (2 * payload.length + 1) + (2 + ((2 * payload.length + 1) + 2)) by omega,
      run_add, scan, Option.bind_some, run_add]
    have check : run (step frameBoot) 2 ⟨2, ⟨(packed payload).reverse, .zero, []⟩⟩ =
        some ⟨4, ⟨(packed payload).reverse, .zero, [.blank]⟩⟩ := rfl
    rw [check, Option.bind_some, run_add, rewind, Option.bind_some]
    simp only [List.reverse_cons, List.reverse_reverse, ← frame_symbols]
    rfl
  · rfl

theorem frameBoot_suffix (payload : List Bool) (bit : Bool) (rest : List Bool) :
    ∃ output, HaltsAt frameBoot (Encoding.frame payload ++ bit :: rest) (2 * payload.length + 2) output ∧
      frameBoot.accept output.control = false := by
  let output : Config frameBoot := ⟨3, ⟨.zero :: (packed payload).reverse, bitSymbol bit, rest.map bitSymbol⟩⟩
  refine ⟨output, ⟨?_, ?_⟩, rfl⟩
  change run (step frameBoot) (2 * payload.length + 2)
    ⟨0, ⟨[], ((Encoding.frame payload ++ bit :: rest).map bitSymbol).headD .blank,
      ((Encoding.frame payload ++ bit :: rest).map bitSymbol).tail⟩⟩ = _
  rw [show 2 * payload.length + 2 = (2 * payload.length + 1) + 1 by omega, run_add]
  have scan := frameBoot_scan [] payload (bit :: rest)
  simp only [List.append_nil] at scan
  rw [scan, Option.bind_some]
  rfl
  cases bit <;> rfl

theorem frameBoot_total (input : List Bool) :
    ∃ steps output, steps ≤ 2 * input.length + 4 ∧ HaltsAt frameBoot input steps output ∧
      (frameBoot.accept output.control = true → ∃ payload, input = Encoding.frame payload ∧
        output = ⟨6, bootOutput payload⟩) := by
  cases parsed : Encoding.unframe input with
  | none =>
      obtain ⟨steps, output, cost, halted, rejected⟩ := frameBoot_malformed input parsed
      exact ⟨steps, output, by omega, halted, by simp only [rejected, Bool.false_eq_true, false_implies]⟩
  | some pair =>
      rcases pair with ⟨payload, suffix⟩
      have same := unframe_sound input payload suffix parsed
      subst input
      cases suffix with
      | nil =>
          simp only [List.append_nil]
          exact ⟨_, _, by rw [Encoding.frame_length]; omega, frameBoot_frame payload,
            fun _ => ⟨payload, rfl, rfl⟩⟩
      | cons bit rest =>
          obtain ⟨output, halted, rejected⟩ := frameBoot_suffix payload bit rest
          exact ⟨_, output, by simp only [List.length_append, Encoding.frame_length, List.length_cons]; omega,
            halted, by simp only [rejected, Bool.false_eq_true, false_implies]⟩

theorem listBlank_append_blank (symbols : List Symbol) :
    Turing.ListBlank.mk (symbols ++ [.blank]) = Turing.ListBlank.mk symbols := by
  symm
  apply Quotient.sound
  exact Or.inl ⟨1, rfl⟩

theorem listBlank_singleton_blank :
    Turing.ListBlank.mk ([.blank] : List Symbol) = Turing.ListBlank.mk [] :=
  listBlank_append_blank []

theorem skipPairs_packed (payload : List Bool) (suffix : List Symbol) :
    skipPairs (packed payload ++ suffix) = payload.map bitSymbol ++ skipPairs suffix := by
  induction payload with
  | nil => rfl
  | cons bit rest ih => simp only [packed, List.cons_append, skipPairs, List.map_cons, ih]

theorem bootOutput_decodes (payload : List Bool) :
    (bootOutput payload).unstride.denotes = Turing.Tape.mk₁ (payload.map bitSymbol) := by
  cases payload with
  | nil =>
      change (⟨.blank, Turing.ListBlank.mk [.blank], Turing.ListBlank.mk []⟩ : Turing.Tape Symbol) = _
      rw [listBlank_singleton_blank]
      rfl
  | cons bit rest =>
      unfold bootOutput
      rw [frame_symbols]
      simp only [packed, List.cons_append, List.append_assoc]
      change (⟨bitSymbol bit, Turing.ListBlank.mk [.blank],
        Turing.ListBlank.mk (skipPairs (packed rest ++ [.zero, .blank]))⟩ : Turing.Tape Symbol) = _
      rw [skipPairs_packed]
      change (⟨bitSymbol bit, Turing.ListBlank.mk [.blank],
        Turing.ListBlank.mk (rest.map bitSymbol ++ [.blank])⟩ : Turing.Tape Symbol) = _
      rw [listBlank_append_blank, listBlank_singleton_blank]
      rfl

end Counting.Machine
