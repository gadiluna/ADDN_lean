import Counting.MachineTapeBounds

/-! Concrete concatenation of finite programs. The first machine's halted
control labels are replaced by one write of the unchanged head symbol,
entering the second initial state. This costs exactly one extra transition.
The caller must establish the complete intermediate output tape. -/
namespace Counting.Machine

def firstControl (first second : Program) (control : Control first) :
    Fin (first.states + second.states + 2) := ⟨control.val, by have := control.isLt; omega⟩

def secondControl (first second : Program) (control : Control second) :
    Fin (first.states + second.states + 2) :=
  ⟨first.states + 1 + control.val, by have := control.isLt; omega⟩

def compose (first second : Program) : Program where
  states := first.states + second.states + 1
  code control symbol :=
    if inside : control.val < first.states + 1 then
      match first.code ⟨control.val, inside⟩ symbol with
      | none => some (secondControl first second 0, .write symbol)
      | some (next, action) => some (firstControl first second next, action)
    else
      (second.code ⟨control.val - (first.states + 1), by have := control.isLt; omega⟩ symbol).map
        (fun (next, action) => (secondControl first second next, action))
  accept control :=
    if inside : control.val < first.states + 1 then false
    else second.accept ⟨control.val - (first.states + 1), by have := control.isLt; omega⟩

def firstConfig (first second : Program) (config : Config first) : Config (compose first second) :=
  ⟨firstControl first second config.control, config.tape⟩

def secondConfig (first second : Program) (config : Config second) : Config (compose first second) :=
  ⟨secondControl first second config.control, config.tape⟩

theorem compose_first_code (first second : Program) (control : Control first) (symbol : Symbol) :
    (compose first second).code (firstControl first second control) symbol =
      match first.code control symbol with
      | none => some (secondControl first second 0, .write symbol)
      | some (next, action) => some (firstControl first second next, action) := by
  simp only [compose, firstControl, dif_pos control.isLt]

theorem compose_second_code (first second : Program) (control : Control second) (symbol : Symbol) :
    (compose first second).code (secondControl first second control) symbol =
      (second.code control symbol).map (fun (next, action) => (secondControl first second next, action)) := by
  have outside : ¬first.states + 1 + control.val < first.states + 1 := by omega
  simp only [compose, secondControl, dif_neg outside, Nat.add_sub_cancel_left]

theorem compose_second_accept (first second : Program) (control : Control second) :
    (compose first second).accept (secondControl first second control) = second.accept control := by
  have outside : ¬first.states + 1 + control.val < first.states + 1 := by omega
  simp only [compose, secondControl, dif_neg outside, Nat.add_sub_cancel_left]

theorem first_step {first second : Program} {config next : Config first}
    (success : step first config = some next) :
    step (compose first second) (firstConfig first second config) = some (firstConfig first second next) := by
  unfold step at success
  obtain ⟨pair, code, equal⟩ := Option.map_eq_some_iff.mp success
  rcases pair with ⟨control, action⟩
  subst next
  simp only [step, firstConfig, compose_first_code, code, Option.map_some]

theorem first_halt {first second : Program} {config : Config first}
    (halted : step first config = none) :
    step (compose first second) (firstConfig first second config) =
      some (secondConfig first second ⟨0, config.tape⟩) := by
  have code : first.code config.control config.tape.head = none := Option.map_eq_none_iff.mp halted
  simp only [step, firstConfig, compose_first_code, code, Option.map_some]
  rfl

theorem second_step (first second : Program) (config : Config second) :
    step (compose first second) (secondConfig first second config) =
      (step second config).map (secondConfig first second) := by
  simp only [step, secondConfig, compose_second_code, Option.map_map]
  rfl

theorem first_run {first second : Program} (steps : Nat) {start finish : Config first}
    (success : run (step first) steps start = some finish) :
    run (step (compose first second)) steps (firstConfig first second start) =
      some (firstConfig first second finish) := by
  induction steps generalizing start with
  | zero => have same := Option.some.inj success; subst finish; rfl
  | succ steps ih =>
      cases next : step first start with
      | none => simp only [run, next, Option.bind_none] at success; contradiction
      | some middle =>
          have rest : run (step first) steps middle = some finish := by
            simpa only [run, next, Option.bind_some] using success
          rw [run, first_step next, Option.bind_some]
          exact ih rest

theorem second_run (first second : Program) (steps : Nat) (start : Config second) :
    run (step (compose first second)) steps (secondConfig first second start) =
      (run (step second) steps start).map (secondConfig first second) :=
  (run_simulation _ _ _ (fun config => (second_step first second config).symm) steps start).symm

/-- Actual concatenated execution, retaining the exact sum of transition
counts and the one transition at the program boundary. -/
theorem compose_halts_with_accept {first second : Program} {input middle : List Bool} {firstSteps secondSteps : Nat}
    {firstOutput : Config first} {secondOutput : Config second}
    (firstHalts : HaltsAt first input firstSteps firstOutput)
    (clean : firstOutput.tape.denotes = Turing.Tape.mk₁ (middle.map bitSymbol))
    (secondHalts : HaltsAt second middle secondSteps secondOutput) :
    ∃ output : Config (compose first second),
      HaltsAt (compose first second) input (firstSteps + 1 + secondSteps) output ∧
      output.tape.denotes = secondOutput.tape.denotes ∧
      (compose first second).accept output.control = second.accept secondOutput.control := by
  let start : Config second := ⟨0, firstOutput.tape⟩
  have same : (initial second middle).denotes = start.denotes := by
    simp only [initial, Config.denotes, Tape.denotes_ofWord, start, clean]
  obtain ⟨finish, ran, tape⟩ := run_transport second secondSteps (initial second middle) start
    secondOutput same secondHalts.1
  have halted : step second finish = none := halt_transport tape.symm secondHalts.2
  refine ⟨secondConfig first second finish, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [show firstSteps + 1 + secondSteps = firstSteps + (secondSteps + 1) by omega, run_add]
    change (run (step (compose first second)) firstSteps (firstConfig first second (initial first input))).bind _ = _
    rw [first_run firstSteps firstHalts.1, Option.bind_some, run, first_halt firstHalts.2,
      Option.bind_some, second_run, ran]
    rfl
  · rw [second_step, halted]
    rfl
  · exact congrArg Turing.TM0.Cfg.Tape tape
  · change (compose first second).accept (secondControl first second finish.control) = _
    rw [compose_second_accept]
    exact congrArg second.accept (congrArg Turing.TM0.Cfg.q tape)

theorem compose_halts {first second : Program} {input middle : List Bool} {firstSteps secondSteps : Nat}
    {firstOutput : Config first} {secondOutput : Config second}
    (firstHalts : HaltsAt first input firstSteps firstOutput)
    (clean : firstOutput.tape.denotes = Turing.Tape.mk₁ (middle.map bitSymbol))
    (secondHalts : HaltsAt second middle secondSteps secondOutput) :
    ∃ output : Config (compose first second),
      HaltsAt (compose first second) input (firstSteps + 1 + secondSteps) output ∧
      output.tape.denotes = secondOutput.tape.denotes := by
  obtain ⟨output, halted, tape, _⟩ := compose_halts_with_accept firstHalts clean secondHalts
  exact ⟨output, halted, tape⟩

end Counting.Machine
