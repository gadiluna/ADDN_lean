import Counting.StackTape
import Counting.MachineFiniteControl
import Counting.MachineStackShift
import Counting.MachineStackDelete
import Counting.MachineStackScan
import Mathlib.Logic.Equiv.Fin.Basic

/-! A concrete finite-control compiler for the fixed-register stack language.
All scans and shifts are physical tape transitions. The `entry` states are
at the unique left marker; auxiliary states retain only finite control. -/
namespace Counting.StackMachine.Compiler
open Machine

abbrev Registers (program : StackMachine.Program) := program.extraRegisters+2
abbrev State (program : StackMachine.Program) :=
  StackMachine.Control program ⊕
    ((StackMachine.Control program × Fin (Registers program+1)) ⊕
      ((StackMachine.Control program × Fin 10) ⊕
        ((StackMachine.Control program × Fin 10) ⊕ StackMachine.Control program)))

def entry {program : StackMachine.Program} (control : StackMachine.Control program) : State program := .inl control
def scan {program : StackMachine.Program} (control : StackMachine.Control program)
    (counter : Fin (Registers program+1)) : State program := .inr (.inl (control,counter))
def insert {program : StackMachine.Program} (control : StackMachine.Control program)
    (phase : Fin 10) : State program := .inr (.inr (.inl (control,phase)))
def delete {program : StackMachine.Program} (control : StackMachine.Control program)
    (phase : Fin 10) : State program := .inr (.inr (.inr (.inl (control,phase))))
def returning {program : StackMachine.Program} (control : StackMachine.Control program) : State program :=
  .inr (.inr (.inr (.inr control)))

def cardinal (program : StackMachine.Program) : Nat :=
  (program.states+1) + ((program.states+1)*(Registers program+1) +
    ((program.states+1)*10 + ((program.states+1)*10+(program.states+1))))

def stateEquiv (program : StackMachine.Program) : State program ≃ Fin (cardinal program) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr finProdFinEquiv ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv

def encode (program : StackMachine.Program) : State program ≃ Fin (cardinal program-1+1) :=
  (stateEquiv program).trans (finCongr (by dsimp [cardinal]; omega))

def code (program : StackMachine.Program) : State program → Symbol → Option (State program × Turing.TM0.Stmt Symbol)
  | .inl control, symbol =>
      match program.code control with
      | .halt => none
      | .jump next => some (entry next, .write symbol)
      | .push register _ _ | .pop register _ _ _ =>
          some (scan control ⟨register.val+1, by have := register.isLt; dsimp [Registers]; omega⟩, .move .right)
  | .inr (.inl (control,counter)), symbol =>
      match (StackScan.scanProgram (Registers program)).code counter symbol with
      | some (next,action) => some (scan control next,action)
      | none =>
          match program.code control with
          | .halt => none
          | .jump next => some (returning next, .write symbol)
          | .push _ bit next => some (insert next (StackShift.carryState (bitSymbol bit)), .write symbol)
          | .pop _ empty zero one =>
              if symbol = .separator then some (returning empty, .write symbol)
              else some (delete (if symbol = .one then one else zero) 0, .write symbol)
  | .inr (.inr (.inl (control,phase))), symbol =>
      match StackShift.insertionProgram.code phase symbol with
      | some (next,action) => some (insert control next,action)
      | none => some (returning control, .write symbol)
  | .inr (.inr (.inr (.inl (control,phase)))), symbol =>
      match StackShift.deletionProgram.code phase symbol with
      | some (next,action) => some (delete control next,action)
      | none => some (returning control, .write symbol)
  | .inr (.inr (.inr (.inr control))), symbol =>
      match StackScan.returnProgram.code 0 symbol with
      | some (_,action) => some (returning control,action)
      | none => some (entry control, .write symbol)

def machine (program : StackMachine.Program) : Machine.Program :=
  FiniteControl.compile (encode program) (code program) (fun _ => true)

abbrev Configuration (program : StackMachine.Program) := FiniteControl.Config (State program)
abbrev transition (program : StackMachine.Program) := FiniteControl.step (code program)

def atEntry {program : StackMachine.Program} (config : StackMachine.Config program) : Configuration program :=
  ⟨entry config.control, Tape.ofWord config.encoded⟩

theorem scan_instruction (program : StackMachine.Program) (control : StackMachine.Control program)
    (counter next : Machine.Control (StackScan.scanProgram (Registers program)))
    (symbol : Symbol) (action : Turing.TM0.Stmt Symbol)
    (instruction : (StackScan.scanProgram (Registers program)).code counter symbol = some (next,action)) :
    code program (scan control counter) symbol = some (scan control next,action) := by
  simp only [code, scan, instruction]

theorem insert_instruction (program : StackMachine.Program) (control : StackMachine.Control program)
    (phase next : Machine.Control StackShift.insertionProgram) (symbol : Symbol) (action : Turing.TM0.Stmt Symbol)
    (instruction : StackShift.insertionProgram.code phase symbol = some (next,action)) :
    code program (insert control phase) symbol = some (insert control next,action) := by
  simp only [code, insert, instruction]

theorem delete_instruction (program : StackMachine.Program) (control : StackMachine.Control program)
    (phase next : Machine.Control StackShift.deletionProgram) (symbol : Symbol) (action : Turing.TM0.Stmt Symbol)
    (instruction : StackShift.deletionProgram.code phase symbol = some (next,action)) :
    code program (delete control phase) symbol = some (delete control next,action) := by
  simp only [code, delete, instruction]

theorem return_instruction (program : StackMachine.Program) (control : StackMachine.Control program)
    (phase next : Machine.Control StackScan.returnProgram) (symbol : Symbol) (action : Turing.TM0.Stmt Symbol)
    (instruction : StackScan.returnProgram.code phase symbol = some (next,action)) :
    code program (returning control) symbol = some (returning control,action) := by
  have phase_zero : phase = 0 := by
    apply Fin.ext
    have bounded := phase.isLt
    change phase.val < 1 at bounded
    change phase.val = 0
    omega
  simp only [phase_zero] at instruction
  simp only [code, returning, instruction]

theorem compiled_run (program : StackMachine.Program) (steps : Nat) (source : Configuration program) :
    Machine.run (Machine.step (machine program)) steps
      (FiniteControl.config (encode program) (code program) (fun _ => true) source) =
    (Machine.run (transition program) steps source).map
      (FiniteControl.config (encode program) (code program) (fun _ => true)) :=
  FiniteControl.run_compile _ _ _ _ _

theorem entry_halted {program : StackMachine.Program} (config : StackMachine.Config program)
    (halted : StackMachine.step program config = none) : transition program (atEntry config) = none := by
  cases instruction : program.code config.control <;>
    simp_all [StackMachine.step, transition, FiniteControl.step, atEntry, entry, code]
  split at halted <;> contradiction

end Counting.StackMachine.Compiler
