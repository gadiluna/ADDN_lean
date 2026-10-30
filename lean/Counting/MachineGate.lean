import Counting.MachineComposition

/-! Concrete guarded concatenation. A rejected first stage halts; an
accepted first stage enters the second stage through one counted write. -/
namespace Counting.Machine

def gate (first second : Program) : Program where
  states := first.states + second.states + 1
  code control symbol :=
    if inside : control.val < first.states + 1 then
      let original : Control first := ⟨control.val, inside⟩
      match first.code original symbol with
      | none => if first.accept original then some (secondControl first second 0, .write symbol) else none
      | some (next, action) => some (firstControl first second next, action)
    else
      (second.code ⟨control.val - (first.states + 1), by have := control.isLt; omega⟩ symbol).map
        (fun (next, action) => (secondControl first second next, action))
  accept control :=
    if inside : control.val < first.states + 1 then false
    else second.accept ⟨control.val - (first.states + 1), by have := control.isLt; omega⟩

def gateFirst (first second : Program) (config : Config first) : Config (gate first second) :=
  ⟨firstControl first second config.control, config.tape⟩

def gateSecond (first second : Program) (config : Config second) : Config (gate first second) :=
  ⟨secondControl first second config.control, config.tape⟩

theorem gate_first_code (first second : Program) (control : Control first) (symbol : Symbol) :
    (gate first second).code (firstControl first second control) symbol =
      match first.code control symbol with
      | none => if first.accept control then some (secondControl first second 0, .write symbol) else none
      | some (next, action) => some (firstControl first second next, action) := by
  simp only [gate, firstControl, dif_pos control.isLt]

theorem gate_second_code (first second : Program) (control : Control second) (symbol : Symbol) :
    (gate first second).code (secondControl first second control) symbol =
      (second.code control symbol).map (fun (next, action) => (secondControl first second next, action)) := by
  have outside : ¬first.states + 1 + control.val < first.states + 1 := by omega
  simp only [gate, secondControl, dif_neg outside, Nat.add_sub_cancel_left]

theorem gate_first_accept (first second : Program) (control : Control first) :
    (gate first second).accept (firstControl first second control) = false := by
  simp only [gate, firstControl, dif_pos control.isLt]

theorem gate_second_accept (first second : Program) (control : Control second) :
    (gate first second).accept (secondControl first second control) = second.accept control := by
  have outside : ¬first.states + 1 + control.val < first.states + 1 := by omega
  simp only [gate, secondControl, dif_neg outside, Nat.add_sub_cancel_left]

theorem gate_first_step {first second : Program} {config next : Config first}
    (success : step first config = some next) :
    step (gate first second) (gateFirst first second config) = some (gateFirst first second next) := by
  obtain ⟨⟨control, action⟩, code, equal⟩ := Option.map_eq_some_iff.mp success
  subst next
  simp only [step, gateFirst, gate_first_code, code, Option.map_some]

theorem gate_second_step (first second : Program) (config : Config second) :
    step (gate first second) (gateSecond first second config) =
      (step second config).map (gateSecond first second) := by
  simp only [step, gateSecond, gate_second_code, Option.map_map]
  rfl

theorem gate_first_run {first second : Program} (steps : Nat) {start finish : Config first}
    (success : run (step first) steps start = some finish) :
    run (step (gate first second)) steps (gateFirst first second start) =
      some (gateFirst first second finish) := by
  induction steps generalizing start with
  | zero => have same := Option.some.inj success; subst finish; rfl
  | succ steps ih =>
      cases firstStep : step first start with
      | none => simp only [run, firstStep, Option.bind_none] at success; contradiction
      | some next =>
          have rest : run (step first) steps next = some finish := by
            simpa only [run, firstStep, Option.bind_some] using success
          rw [run, gate_first_step firstStep, Option.bind_some]
          exact ih rest

theorem gate_second_run (first second : Program) (steps : Nat) (start : Config second) :
    run (step (gate first second)) steps (gateSecond first second start) =
      (run (step second) steps start).map (gateSecond first second) :=
  (run_simulation _ _ _ (fun config => (gate_second_step first second config).symm) steps start).symm

theorem gate_reject {first second : Program} {input : List Bool} {steps : Nat} {output : Config first}
    (halted : HaltsAt first input steps output) (rejected : first.accept output.control = false) :
    HaltsAt (gate first second) input steps (gateFirst first second output) ∧
      (gate first second).accept (gateFirst first second output).control = false := by
  refine ⟨⟨gate_first_run steps halted.1, ?_⟩, gate_first_accept first second output.control⟩
  have code := Option.map_eq_none_iff.mp halted.2
  simp only [step, gateFirst, gate_first_code, code, rejected, Bool.false_eq_true, if_false, Option.map_none]

theorem gate_continue {first second : Program} {input : List Bool} {firstSteps secondSteps : Nat}
    {firstOutput : Config first} {secondOutput : Config second}
    (firstHalts : HaltsAt first input firstSteps firstOutput)
    (accepted : first.accept firstOutput.control = true)
    (secondRun : run (step second) secondSteps ⟨0, firstOutput.tape⟩ = some secondOutput)
    (secondHalt : step second secondOutput = none) :
    HaltsAt (gate first second) input (firstSteps + 1 + secondSteps) (gateSecond first second secondOutput) ∧
      (gate first second).accept (gateSecond first second secondOutput).control = second.accept secondOutput.control := by
  have code := Option.map_eq_none_iff.mp firstHalts.2
  have bridge : step (gate first second) (gateFirst first second firstOutput) =
      some (gateSecond first second ⟨0, firstOutput.tape⟩) := by
    simp only [step, gateFirst, gate_first_code, code, accepted, if_true, Option.map_some]
    rfl
  refine ⟨⟨?_, ?_⟩, gate_second_accept first second secondOutput.control⟩
  · rw [show firstSteps + 1 + secondSteps = firstSteps + (1 + secondSteps) by omega, run_add]
    change (run (step (gate first second)) firstSteps (gateFirst first second (initial first input))).bind _ = _
    rw [gate_first_run firstSteps firstHalts.1, Option.bind_some, run_add]
    have one : run (step (gate first second)) 1 (gateFirst first second firstOutput) =
        some (gateSecond first second ⟨0, firstOutput.tape⟩) := by
      simp only [run, bridge, Option.bind_some]
    rw [one, Option.bind_some, gate_second_run, secondRun, Option.map_some]
  · rw [gate_second_step, secondHalt, Option.map_none]

end Counting.Machine
