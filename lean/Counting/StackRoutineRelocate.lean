import Counting.StackRoutineSemantics

/-! Injective register relocation changes only register addresses in finite
code. It preserves the exact abstract transition count, including halting,
and every register outside the selected image. -/
namespace Counting.StackMachine

def Instruction.relocate {registers targets states : Nat}
    (address : Fin registers → Fin targets) :
    Instruction registers states → Instruction targets states
  | .halt => .halt
  | .jump next => .jump next
  | .push register bit next => .push (address register) bit next
  | .pop register empty zero one => .pop (address register) empty zero one

namespace Routine

def relocate {registers targets : Nat} (routine : Routine registers)
    (address : Fin (registers+2) ↪ Fin (targets+2)) : Routine targets :=
  ⟨routine.states, fun control => (routine.code control).relocate address⟩

/-- A mathematical description of the resulting register file. The generated
program above is executable and does not evaluate this auxiliary extension. -/
noncomputable def relocatedStore {registers targets : Nat}
    (address : Fin registers ↪ Fin targets) (base : Fin targets → List Bool)
    (localStore : Fin registers → List Bool) : Fin targets → List Bool :=
  fun target => if member : ∃ source, address source = target then
    localStore member.choose else base target

@[simp] theorem relocatedStore_at {registers targets : Nat}
    (address : Fin registers ↪ Fin targets) (base : Fin targets → List Bool)
    (localStore : Fin registers → List Bool) (source : Fin registers) :
    relocatedStore address base localStore (address source) = localStore source := by
  unfold relocatedStore
  split_ifs with member
  · have equal := address.injective member.choose_spec
    rw [equal]
  · exact False.elim (member ⟨source,rfl⟩)

theorem relocatedStore_outside {registers targets : Nat}
    (address : Fin registers ↪ Fin targets) (base : Fin targets → List Bool)
    (localStore : Fin registers → List Bool) (target : Fin targets)
    (outside : ∀ source, address source ≠ target) :
    relocatedStore address base localStore target = base target := by
  simp [relocatedStore,not_exists.mpr outside]

theorem relocatedStore_original {registers targets : Nat}
    (address : Fin registers ↪ Fin targets) (base : Fin targets → List Bool) :
    relocatedStore address base (base ∘ address) = base := by
  funext target
  by_cases member : ∃ source, address source = target
  · obtain ⟨source,rfl⟩ := member
    simp
  · simp [relocatedStore,member]

theorem relocatedStore_update {registers targets : Nat}
    (address : Fin registers ↪ Fin targets) (base : Fin targets → List Bool)
    (localStore : Fin registers → List Bool) (source : Fin registers) (value : List Bool) :
    relocatedStore address base (Function.update localStore source value) =
      Function.update (relocatedStore address base localStore) (address source) value := by
  funext target
  by_cases member : ∃ index, address index = target
  · obtain ⟨index,rfl⟩ := member
    simp only [relocatedStore_at]
    by_cases same : index = source
    · subst index; simp
    · have different : address index ≠ address source := fun equal => same (address.injective equal)
      simp [Function.update,same,different]
  · have outside : ∀ index, address index ≠ target := not_exists.mp member
    rw [relocatedStore_outside address base _ target outside,
      Function.update_of_ne (outside source).symm,
      relocatedStore_outside address base _ target outside]

noncomputable def relocatedConfig {registers targets : Nat} (routine : Routine registers)
    (address : Fin (registers+2) ↪ Fin (targets+2))
    (base : Fin (targets+2) → List Bool) (config : Config routine.program) :
    Config (relocate routine address).program :=
  ⟨config.control,relocatedStore address base config.store⟩

theorem relocate_step {registers targets : Nat} (routine : Routine registers)
    (address : Fin (registers+2) ↪ Fin (targets+2))
    (base : Fin (targets+2) → List Bool) (config : Config routine.program) :
    step (relocate routine address).program (relocatedConfig routine address base config) =
      (step routine.program config).map (relocatedConfig routine address base) := by
  unfold step
  dsimp only [relocate,program,relocatedConfig]
  cases instruction : routine.code config.control with
  | halt => rfl
  | jump next => rfl
  | push source bit next =>
      simp only [Instruction.relocate,relocatedStore_at,Option.map_some,relocatedConfig,
        relocatedStore_update]
      rfl
  | pop source empty zero one =>
      simp only [Instruction.relocate,relocatedStore_at]
      cases contents : config.store source with
      | nil => rfl
      | cons bit rest =>
          simp only [Option.map_some,relocatedConfig,relocatedStore_update]
          rfl

theorem relocate_executes {registers targets : Nat} (routine : Routine registers)
    (address : Fin (registers+2) ↪ Fin (targets+2))
    (store : Fin (targets+2) → List Bool) (transitions : Nat)
    (output : Fin (registers+2) → List Bool)
    (executed : Executes routine (store ∘ address) transitions output) :
    Executes (relocate routine address) store transitions
      (relocatedStore address store output) := by
  obtain ⟨finish,run,halted,values⟩ := executed
  refine ⟨relocatedConfig routine address store finish,?_,?_,?_⟩
  · have simulation := (Machine.run_simulation _ _ _
      (fun config => (relocate_step routine address store config).symm) transitions
      (⟨0,store ∘ address⟩ : Config routine.program)).symm
    rw [run,Option.map_some] at simulation
    simp only [relocatedConfig,relocatedStore_original] at simulation
    exact simulation
  · rw [relocate_step,halted,Option.map_none]
  · change relocatedStore address store finish.store = _
    rw [values]

/-- Padding or relocating a whole input/output transducer preserves its
bound when the distinguished input and output addresses remain 0 and 1. -/
theorem relocate_computes {registers targets : Nat} (routine : Routine registers)
    (address : Fin (registers+2) ↪ Fin (targets+2))
    (inputAddress : address 0 = 0) (outputAddress : address 1 = 1)
    (function : List Bool → List Bool) (bound : Nat → Nat)
    (computes : ComputesIn routine.program function bound) :
    ComputesIn (relocate routine address).program function bound := by
  intro input
  obtain ⟨time,finish,bounded,⟨ran,halted⟩,result⟩ := computes input
  let base := (initial (relocate routine address).program input).store
  have restricted : base ∘ address = (initial routine.program input).store := by
    funext r
    change (if address r=0 then input else []) = (if r=0 then input else [])
    have equal : address r=0 ↔ r=0 := by rw [← inputAddress]; exact address.injective.eq_iff
    simp only [equal]
  have executed : Executes routine (base ∘ address) time finish.store := by
    rw [restricted]
    exact ⟨finish,ran,halted,rfl⟩
  obtain ⟨output,outputRun,outputHalt,outputStore⟩ := relocate_executes routine address base time finish.store executed
  refine ⟨time,output,bounded,⟨outputRun,outputHalt⟩,?_⟩
  rw [outputStore,← outputAddress,relocatedStore_at,result]

end Routine
end Counting.StackMachine
