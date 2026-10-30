import Counting.InputMultisetLocalFinite
import Counting.DagSemanticsTransport

/-! Reconstruction on finite stored node identifiers. Neither the certificate
search nor its tests expand the represented histories. The semantic transport
below permits any faithful representation of the labelled history level. -/

namespace Counting.InputMultiset.DagRecovery
open scoped BigOperators

variable {Input : Type}

structure Data (Input : Type) where
  nodes : Finset Nat
  parent : Nat → Nat
  degree : Nat → Nat
  received : Nat → Nat → Nat
  input : Nat → Input

def weightAt (data : Data Input) (w : ∀ i ∈ data.nodes, Nat) (i : Nat) : Nat :=
  if hi : i ∈ data.nodes then w i hi else 0

@[simp] theorem weightAt_mem (data : Data Input) (w : ∀ i ∈ data.nodes, Nat)
    (i : Nat) (hi : i ∈ data.nodes) : weightAt data w i = w i hi := by
  simp [weightAt, hi]

def Valid (n : Nat) (data : Data Input) (w : ∀ i ∈ data.nodes, Nat) : Prop :=
  (∀ i ∈ data.nodes, ∀ j ∈ data.nodes, data.parent i = data.parent j → i = j) ∧
  (∑ i ∈ data.nodes, weightAt data w i) = n ∧
  (∀ i ∈ data.nodes, (∑ j ∈ data.nodes, data.received i j * weightAt data w j) =
    data.degree i * weightAt data w i)

instance validDecidable (n : Nat) (data : Data Input) (w : ∀ i ∈ data.nodes, Nat) :
    Decidable (Valid n data w) := by unfold Valid; infer_instance

def solutions (n : Nat) (data : Data Input) : Finset (∀ i ∈ data.nodes, Nat) :=
  (data.nodes.pi (fun _ => Finset.range (n + 1))).filter (Valid n data)

def candidateOutput (data : Data Input) (w : ∀ i ∈ data.nodes, Nat) : Multiset Input :=
  ∑ i ∈ data.nodes, Multiset.replicate (weightAt data w i) (data.input i)

variable [DecidableEq Input]

def atRound (n : Nat) (data : Data Input) : Multiset Input :=
  (solutions n data).sup (candidateOutput data)

/-- All fields compared by the local verifier have their intended semantic
meaning on the represented finite level. -/
structure Represents (data : Data Input) (r : Nat)
    (f : Nat → InputProtocol.FullHistory Input (r + 1)) : Prop where
  injective : Set.InjOn f data.nodes
  parent : ∀ i ∈ data.nodes, ∀ j ∈ data.nodes,
    data.parent i = data.parent j ↔ (f i).1 = (f j).1
  degree : ∀ i ∈ data.nodes, data.degree i = (f i).2.1
  received : ∀ i ∈ data.nodes, ∀ j ∈ data.nodes,
    data.received i j = (f j).2.2.count (f i).1
  input : ∀ i ∈ data.nodes,
    data.input i = (InputProtocol.FullHistory.initial (r + 1) (f i)).2

variable (data : Data Input) (r : Nat) (f : Nat → InputProtocol.FullHistory Input (r + 1))

noncomputable def liftWeight (w : ∀ i ∈ data.nodes, Nat) :
    ∀ h ∈ data.nodes.image f, Nat := by
  classical
  intro h hh
  have chosen := Finset.mem_image.mp hh
  exact w chosen.choose chosen.choose_spec.1

def pullWeight (w : ∀ h ∈ data.nodes.image f, Nat) : ∀ i ∈ data.nodes, Nat :=
  fun i hi => w (f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

variable {r f}

theorem liftWeight_apply (rep : Represents data r f) (w : ∀ i ∈ data.nodes, Nat)
    (i : Nat) (hi : i ∈ data.nodes) :
    InputMultisetLocal.weightAt (data.nodes.image f) (liftWeight data r f w) (f i) =
      weightAt data w i := by
  classical
  have hm : f i ∈ data.nodes.image f := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [InputMultisetLocal.weightAt_mem _ _ _ hm, weightAt_mem _ _ _ hi]
  unfold liftWeight
  have eq : (Finset.mem_image.mp hm).choose = i :=
    rep.injective (Finset.mem_image.mp hm).choose_spec.1 hi
      (Finset.mem_image.mp hm).choose_spec.2
  simp only [eq]

@[simp] theorem pullWeight_apply (w : ∀ h ∈ data.nodes.image f, Nat)
    (i : Nat) (hi : i ∈ data.nodes) :
    weightAt data (pullWeight data r f w) i = InputMultisetLocal.weightAt (data.nodes.image f) w (f i) := by
  rw [weightAt_mem _ _ _ hi, InputMultisetLocal.weightAt_mem _ _ _
    (Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
  rfl

theorem lift_valid (rep : Represents data r f) (n : Nat)
    (w : ∀ i ∈ data.nodes, Nat) (valid : Valid n data w) :
    InputMultisetLocal.Valid n r (data.nodes.image f) (liftWeight data r f w) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h hh k hk hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact congrArg f (valid.1 i hi j hj ((rep.parent i hi j hj).mpr hp))
  · rw [Finset.sum_image rep.injective]
    exact (Finset.sum_congr rfl (fun i hi => liftWeight_apply data rep w i hi)).trans valid.2.1
  · intro h hh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
    rw [Finset.sum_image rep.injective, liftWeight_apply data rep w i hi, ← rep.degree i hi]
    calc
      (∑ j ∈ data.nodes, Multiset.count (f i).1 (f j).2.2 *
          InputMultisetLocal.weightAt (data.nodes.image f) (liftWeight data r f w) (f j)) =
          ∑ j ∈ data.nodes, data.received i j * weightAt data w j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← rep.received i hi j hj, liftWeight_apply data rep w j hj]
      _ = data.degree i * weightAt data w i := valid.2.2 i hi

theorem pull_valid (rep : Represents data r f) (n : Nat)
    (w : ∀ h ∈ data.nodes.image f, Nat)
    (valid : InputMultisetLocal.Valid n r (data.nodes.image f) w) :
    Valid n data (pullWeight data r f w) := by
  classical
  have mem : ∀ i ∈ data.nodes, f i ∈ data.nodes.image f :=
    fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj hp
    exact rep.injective hi hj (valid.1 _ (mem i hi) _ (mem j hj)
      ((rep.parent i hi j hj).mp hp))
  · have total := valid.2.1
    rw [Finset.sum_image rep.injective] at total
    exact (Finset.sum_congr rfl (fun i hi => pullWeight_apply data w i hi)).trans total
  · intro i hi
    have hv := valid.2.2 _ (mem i hi)
    rw [Finset.sum_image rep.injective] at hv
    rw [pullWeight_apply data w i hi, rep.degree i hi]
    convert hv using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [rep.received i hi j hj, pullWeight_apply data w j hj]

theorem lift_output (rep : Represents data r f) (w : ∀ i ∈ data.nodes, Nat) :
    InputMultisetLocal.candidateOutput r (data.nodes.image f) (liftWeight data r f w) =
      candidateOutput data w := by
  classical
  unfold InputMultisetLocal.candidateOutput candidateOutput
  rw [Finset.sum_image rep.injective]
  apply Finset.sum_congr rfl
  intro i hi
  rw [liftWeight_apply data rep w i hi, ← rep.input i hi]

theorem pull_output (rep : Represents data r f) (w : ∀ h ∈ data.nodes.image f, Nat) :
    candidateOutput data (pullWeight data r f w) =
      InputMultisetLocal.candidateOutput r (data.nodes.image f) w := by
  classical
  unfold InputMultisetLocal.candidateOutput candidateOutput
  rw [Finset.sum_image rep.injective]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pullWeight_apply data w i hi, rep.input i hi]

theorem lift_mem_solutions (rep : Represents data r f) (n : Nat)
    (w : ∀ i ∈ data.nodes, Nat) (hw : w ∈ solutions n data) :
    liftWeight data r f w ∈ InputMultisetLocal.solutions n r (data.nodes.image f) := by
  classical
  obtain ⟨bounded, valid⟩ := Finset.mem_filter.mp hw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_pi.mpr ?_, lift_valid data rep n w valid⟩
  intro h hh
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
  have eq := liftWeight_apply data rep w i hi
  rw [InputMultisetLocal.weightAt_mem _ _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩),
    weightAt_mem _ _ _ hi] at eq
  rw [eq]
  exact Finset.mem_pi.mp bounded i hi

theorem pull_mem_solutions (rep : Represents data r f) (n : Nat)
    (w : ∀ h ∈ data.nodes.image f, Nat)
    (hw : w ∈ InputMultisetLocal.solutions n r (data.nodes.image f)) :
    pullWeight data r f w ∈ solutions n data := by
  classical
  obtain ⟨bounded, valid⟩ := Finset.mem_filter.mp hw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_pi.mpr ?_, pull_valid data rep n w valid⟩
  intro i hi
  exact Finset.mem_pi.mp bounded (f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- Finite index search agrees exactly with the proved local history search. -/
theorem atRound_eq (rep : Represents data r f) (n : Nat) :
    atRound n data = InputMultisetLocal.atRound n r (data.nodes.image f) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro w hw
    apply Finset.le_sup_of_le (lift_mem_solutions data rep n w hw)
    exact le_of_eq (lift_output data rep w).symm
  · apply Finset.sup_le
    intro w hw
    apply Finset.le_sup_of_le (pull_mem_solutions data rep n w hw)
    exact le_of_eq (pull_output data rep w).symm

/-- Data are read directly from the compressed DAG, with input metadata at
virtual level one reached by following stored parent pointers. -/
def fromVista (vista : Executable.Vista) (inputOf : Nat → Input) (r : Nat) : Data Input where
  nodes := (Executable.levelNodes vista (r + 2)).toFinset
  parent i := (vista.node i).parent.getD 0
  degree i := (vista.node i).degree
  received i j := Executable.countFrom (vista.node j) ((vista.node i).parent.getD 0)
  input i := inputOf (vista.node ((Executable.ascend vista (r + 1) i).getD 0)).degree

def reconstruction (n : Nat) (vista : Executable.Vista) (inputOf : Nat → Input) : Multiset Input :=
  (Finset.range (n - 1)).sup (fun r => atRound n (fromVista vista inputOf r))

def ownInput (vista : Executable.Vista) (inputOf : Nat → Input) : Input :=
  inputOf (vista.node ((Executable.ascend vista ((vista.node vista.bottom).level - 1)
    vista.bottom).getD 0)).degree

def recover (n : Nat) (vista : Executable.Vista) (inputOf : Nat → Input) : Option (Multiset Input) :=
  if ∀ i ∈ (Executable.levelNodes vista 1).toFinset,
      inputOf (vista.node i).degree = ownInput vista inputOf then
    some (Multiset.replicate n (ownInput vista inputOf))
  else
    let result := reconstruction n vista inputOf
    if result.card = n then some result else none

end Counting.InputMultiset.DagRecovery
