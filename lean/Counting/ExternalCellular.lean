import Counting.ExternalTableauSize
import Counting.MachineModel

namespace Counting.External.Cellular
open Machine

abbrev Cell (program : Program) := Symbol × Option (Control program)

def symbolEquiv : Symbol ≃ Fin 5 where
  toFun symbol := match symbol with
    | .blank => 0 | .zero => 1 | .one => 2 | .separator => 3 | .mark => 4
  invFun i := ![.blank, .zero, .one, .separator, .mark] i
  left_inv symbol := by cases symbol <;> rfl
  right_inv i := by fin_cases i <;> rfl

def alphabet (program : Program) : ℕ := 5 * (program.states+2)

def cellEquiv (program : Program) : Cell program ≃ Fin (alphabet program) :=
  (Equiv.prodCongr symbolEquiv (finSuccEquiv (program.states+1)).symm).trans finProdFinEquiv

def incoming (program : Program) (cell : Cell program) (direction : Turing.Dir) : Option (Control program) :=
  match cell.2 with
  | none => none
  | some control =>
      match program.code control cell.1 with
      | some (next, .move movement) => if movement = direction then some next else none
      | _ => none

/-- The local rule uses three cells. A halted head is retained, so the
tableau may stutter after a real halt. This does not add machine transitions. -/
def rule (program : Program) (neighbors : Fin 3 → Cell program) : Cell program :=
  let center := neighbors 1
  match center.2 with
  | none => (center.1, (incoming program (neighbors 0) .right).orElse
      (fun _ => incoming program (neighbors 2) .left))
  | some control =>
      match program.code control center.1 with
      | none => center
      | some (next, .write symbol) => (symbol, some next)
      | some (_, .move _) => (center.1, none)

structure Config (program : Program) (Position : Type) where
  control : Control program
  position : Position
  tape : Position → Symbol

def Config.cells {program : Program} {Position : Type} [DecidableEq Position]
    (config : Config program Position) (place : Position) : Cell program :=
  (config.tape place, if place = config.position then some config.control else none)

def Config.step {program : Program} {Position : Type} [DecidableEq Position]
    (rotation : Equiv.Perm Position) (config : Config program Position) : Config program Position :=
  match program.code config.control (config.tape config.position) with
  | none => config
  | some (next, action) => match action with
      | .move .left => ⟨next, rotation.symm config.position, config.tape⟩
      | .move .right => ⟨next, rotation config.position, config.tape⟩
      | .write symbol => ⟨next, config.position, Function.update config.tape config.position symbol⟩

theorem incoming_cells {program : Program} {Position : Type} [DecidableEq Position]
    (config : Config program Position) (place : Position) (direction : Turing.Dir) :
    incoming program (config.cells place) direction =
      if place = config.position then
        match program.code config.control (config.tape config.position) with
        | some (next, .move movement) => if movement = direction then some next else none
        | _ => none
      else none := by
  by_cases same : place = config.position
  · subst place
    simp only [Config.cells, if_true, incoming]
  · simp only [Config.cells, same, if_false, incoming]

/-- A unique head is preserved and its tape/control update is exactly the
specified local rule. There is no assumption about its eventual answer. -/
theorem cells_step {program : Program} {Position : Type} [DecidableEq Position]
    (rotation : Equiv.Perm Position) (noFixed : ∀ position, rotation position ≠ position)
    (config : Config program Position) (place : Position) :
    (config.step rotation).cells place = rule program
      ![config.cells (rotation.symm place), config.cells place, config.cells (rotation place)] := by
  have leftDifferent : rotation.symm config.position ≠ config.position := by
    intro same
    have := congrArg rotation same
    simp only [Equiv.apply_symm_apply] at this
    exact noFixed _ this.symm
  by_cases center : place = config.position
  · subst place
    simp only [rule, Matrix.cons_val_one, Matrix.cons_val_zero, Config.cells, if_true]
    cases instruction : program.code config.control (config.tape config.position) with
    | none => simp [Config.step, instruction]
    | some result =>
        rcases result with ⟨next, action⟩
        cases action with
        | write symbol => simp [Config.step, instruction]
        | move direction =>
            cases direction with
            | left =>
                simp only [Config.step, instruction, Prod.mk.injEq, true_and, ite_eq_right_iff]
                exact fun same => False.elim (leftDifferent same.symm)
            | right =>
                simp only [Config.step, instruction, Prod.mk.injEq, true_and, ite_eq_right_iff]
                exact fun same => False.elim (noFixed _ same.symm)
  · have leftAt : rotation.symm place = config.position ↔ place = rotation config.position := by
      exact rotation.symm_apply_eq
    have rightAt : rotation place = config.position ↔ place = rotation.symm config.position := by
      exact rotation.apply_eq_iff_eq_symm_apply
    change (config.step rotation).cells place =
      rule program ![config.cells (rotation.symm place), config.cells place, config.cells (rotation place)]
    simp only [rule, Matrix.cons_val_one, Matrix.cons_val_zero, Config.cells, center, if_false]
    change (config.step rotation).cells place =
      (config.tape place, (incoming program (config.cells (rotation.symm place)) .right).orElse
        (fun _ => incoming program (config.cells (rotation place)) .left))
    rw [incoming_cells, incoming_cells]
    cases instruction : program.code config.control (config.tape config.position) with
    | none => simp [Config.step, instruction, Config.cells, center]
    | some result =>
        rcases result with ⟨next, action⟩
        cases action with
        | write symbol => simp [Config.step, instruction, Config.cells, center]
        | move direction =>
            cases direction <;>
              simp [Config.step, instruction, Config.cells, leftAt, rightAt]

def dynamics (program : Program) {width : ℕ} (rotation : Equiv.Perm (Fin width)) :
    Tableau.Dynamics width (alphabet program) where
  left := rotation.symm
  right := rotation
  rule neighbors := cellEquiv program (rule program (fun i => (cellEquiv program).symm (neighbors i)))

def Config.encoded {program : Program} {width : ℕ} (config : Config program (Fin width)) :
    Tableau.Configuration width (alphabet program) := fun place => cellEquiv program (config.cells place)

theorem encoded_step (program : Program) {width : ℕ} (rotation : Equiv.Perm (Fin width))
    (noFixed : ∀ position, rotation position ≠ position) (config : Config program (Fin width)) :
    (config.step rotation).encoded = (dynamics program rotation).step config.encoded := by
  funext place
  simp only [Config.encoded, Tableau.Dynamics.step, dynamics]
  rw [cells_step rotation noFixed]
  congr 2
  funext i
  fin_cases i <;> simp

def Config.run {program : Program} {Position : Type} [DecidableEq Position]
    (rotation : Equiv.Perm Position) : ℕ → Config program Position → Config program Position
  | 0, config => config
  | time+1, config => (Config.run rotation time config).step rotation

theorem encoded_run (program : Program) {width : ℕ} (rotation : Equiv.Perm (Fin width))
    (noFixed : ∀ position, rotation position ≠ position) (time : ℕ) (config : Config program (Fin width)) :
    (config.run rotation time).encoded = (dynamics program rotation).run time config.encoded := by
  induction time with
  | zero => rfl
  | succ time ih =>
      change ((config.run rotation time).step rotation).encoded = _
      rw [encoded_step program rotation noFixed, ih]
      rfl

/-- Only halted accepting heads are accepting tableau symbols. -/
def acceptCell (program : Program) (cell : Cell program) : Bool :=
  match cell.2 with
  | none => false
  | some control => (program.code control cell.1).isNone && program.accept control

def accept (program : Program) (symbol : Fin (alphabet program)) : Bool :=
  acceptCell program ((cellEquiv program).symm symbol)

theorem exists_accept_encoded (program : Program) {width : ℕ} (config : Config program (Fin width)) :
    (∃ place, accept program (config.encoded place) = true) ↔
      program.code config.control (config.tape config.position) = none ∧
        program.accept config.control = true := by
  simp only [accept, Config.encoded, Equiv.symm_apply_apply, acceptCell, Config.cells]
  constructor
  · rintro ⟨place, accepted⟩
    by_cases same : place = config.position
    · subst place
      simpa using accepted
    · simp [same] at accepted
  · intro accepted
    exact ⟨config.position, by simpa using accepted⟩

end Counting.External.Cellular
