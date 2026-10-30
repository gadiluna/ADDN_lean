import Counting.StackPolynomialLength
import Counting.ExternalCookLevin

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

abbrev Workspace (extra : Nat) := Fin 8 ↪ Fin (extra+8)

def witnessSelection : Fin 6 ↪ Fin 8 := ⟨![0,1,2,5,6,7], by decide⟩
def timeSelection : Fin 5 ↪ Fin 8 := ⟨![3,4,5,6,7], by decide⟩

def Workspace.witnessRoles (w : Workspace extra) : PolynomialWorkspace (extra+2) := witnessSelection.trans w
def Workspace.timeRoles (w : Workspace extra) : PowerWorkspace (extra+3) := timeSelection.trans w

theorem roles_ne (w : Workspace extra) {first second : Fin 8} (different : first ≠ second) :
    w first ≠ w second := fun same => different (w.injective same)

/-- The first source contains `L+1`, the second the witness bound. Assemble
`2*(L+1)+W` and raise it to the fixed verifier exponent. -/
def timeRoutine (extra : Nat) (w : Workspace extra) (coefficient exponent : Nat) : Routine (extra+6) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 3) (w 7)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 3) (w 7)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+5) (w 2) (w 3) (w 7)))
        (monomial (extra+3) w.timeRoles coefficient exponent)))

def timeRoutineCost (length witness coefficient exponent : Nat) : Nat :=
  10*(length+1)+5*witness+9+monomialTime (2*(length+1)+witness) coefficient exponent

theorem timeRoutine_executes (extra : Nat) (w : Workspace extra) (length witness coefficient exponent : Nat)
    (store : Fin (extra+8) → List Bool)
    (base : store (w 1) = List.replicate (length+1) true)
    (witnessValue : store (w 2) = List.replicate witness true)
    (timeBaseEmpty : store (w 3) = []) (timeEmpty : store (w 4) = [])
    (counterEmpty : store (w 5) = []) (productEmpty : store (w 6) = []) (workEmpty : store (w 7) = []) :
    Executes (timeRoutine extra w coefficient exponent) store (timeRoutineCost length witness coefficient exponent)
      (Function.update (Function.update store (w 3) (List.replicate (2*(length+1)+witness) true))
        (w 4) (List.replicate (coefficient*(2*(length+1)+witness)^exponent) true)) := by
  let first := Function.update store (w 3) (List.replicate (length+1) true)
  have copyOne : Executes (ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 3) (w 7))) store
      (5*(length+1)+2) first := by
    obtain ⟨finish,run,halted,result⟩ := copy_executes (extra+5) (w 1) (w 3) (w 7)
      (roles_ne w (by decide)) (roles_ne w (by decide)) (roles_ne w (by decide)) store workEmpty
    refine ⟨finish,?_,halted,?_⟩
    · simpa only [base,List.length_replicate] using run
    · rw [result]
      funext register
      by_cases equal : register = w 3
      · subst register; simp [first,base,timeBaseEmpty]
      · simp [first,Function.update,equal]
        intro same
        exact False.elim (equal same)
  let second := Function.update store (w 3) (List.replicate (2*(length+1)) true)
  have firstBase : first (w 1) = List.replicate (length+1) true := by simp [first,w.injective.eq_iff,base]
  have copyTwo : Executes (ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 3) (w 7))) first
      (5*(length+1)+2) second := by
    obtain ⟨finish,run,halted,result⟩ := copy_executes (extra+5) (w 1) (w 3) (w 7)
      (roles_ne w (by decide)) (roles_ne w (by decide)) (roles_ne w (by decide)) first
      (by simp [first,w.injective.eq_iff,workEmpty])
    refine ⟨finish,?_,halted,?_⟩
    · simpa only [firstBase,List.length_replicate] using run
    · rw [result]
      funext register
      by_cases equal : register = w 3
      · subst register; simp [second,first,base,w.injective.eq_iff,two_mul]
      · simp [second,first,Function.update,equal]
        exact (if_neg equal).trans (if_neg equal).symm
  let third := Function.update store (w 3) (List.replicate (2*(length+1)+witness) true)
  have secondWitness : second (w 2) = List.replicate witness true := by simp [second,w.injective.eq_iff,witnessValue]
  have copyWitness : Executes (ofProgram (ListPrograms.copyProgram (extra+5) (w 2) (w 3) (w 7))) second
      (5*witness+2) third := by
    obtain ⟨finish,run,halted,result⟩ := copy_executes (extra+5) (w 2) (w 3) (w 7)
      (roles_ne w (by decide)) (roles_ne w (by decide)) (roles_ne w (by decide)) second
      (by simp [second,w.injective.eq_iff,workEmpty])
    refine ⟨finish,?_,halted,?_⟩
    · simpa only [secondWitness,List.length_replicate] using run
    · rw [result]
      funext register
      by_cases equal : register = w 3
      · subst register; simp [third,second,witnessValue,w.injective.eq_iff,Nat.add_comm]
      · simp [third,second,Function.update,equal]
        exact (if_neg equal).trans (if_neg equal).symm
  have powered := monomial_executes (extra+3) w.timeRoles (2*(length+1)+witness) coefficient exponent third
    (by simp [third,Workspace.timeRoles,timeSelection])
    (by simp [third,Workspace.timeRoles,timeSelection,w.injective.eq_iff,timeEmpty])
    (by simp [third,Workspace.timeRoles,timeSelection,w.injective.eq_iff,counterEmpty])
    (by simp [third,Workspace.timeRoles,timeSelection,w.injective.eq_iff,productEmpty])
    (by simp [third,Workspace.timeRoles,timeSelection,w.injective.eq_iff,workEmpty])
  have combined := copyOne.sequence (copyTwo.sequence (copyWitness.sequence powered))
  have cost : (5*(length+1)+2)+1+((5*(length+1)+2)+1+((5*witness+2)+1+
      monomialTime (2*(length+1)+witness) coefficient exponent)) = timeRoutineCost length witness coefficient exponent := by
    unfold timeRoutineCost
    ring
  simpa [ListPrograms.copyProgram,timeRoutine,cost,third,Workspace.timeRoles,timeSelection] using combined

/-- Roles: input, `L+1`, witness bound, time base, time bound, three scratch
registers. All bounds are computed by executable stack instructions. -/
def boundsRoutine (extra : Nat) (w : Workspace extra)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) : Routine (extra+6) :=
  sequence (polynomialLength (extra+2) w.witnessRoles witnessCoefficient witnessExponent)
    (timeRoutine extra w coefficient exponent)

def boundsCost (length coefficient exponent witnessCoefficient witnessExponent : Nat) : Nat :=
  polynomialLengthTime length witnessCoefficient witnessExponent+1+
    timeRoutineCost length (Complexity.polynomial witnessCoefficient witnessExponent length) coefficient exponent

/-- No population or external size is provided: the two runtime counters
are precisely the witness and verifier-time bounds used in `reduceInput`. -/
theorem boundsRoutine_executes (extra : Nat) (w : Workspace extra)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) (store : Fin (extra+8) → List Bool)
    (empty : ∀ index : Fin 8, index ≠ 0 → store (w index) = []) :
    let input := store (w 0)
    let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
    let time := timeBound coefficient exponent input witness
    Executes (boundsRoutine extra w coefficient exponent witnessCoefficient witnessExponent) store
      (boundsCost input.length coefficient exponent witnessCoefficient witnessExponent)
      (Function.update (Function.update (Function.update (Function.update store
        (w 1) (List.replicate (input.length+1) true)) (w 2) (List.replicate witness true))
        (w 3) (List.replicate (2*(input.length+1)+witness) true)) (w 4) (List.replicate time true)) := by
  dsimp only
  let witness := Complexity.polynomial witnessCoefficient witnessExponent (store (w 0)).length
  let middle := Function.update (Function.update store (w 1) (List.replicate ((store (w 0)).length+1) true))
    (w 2) (List.replicate witness true)
  have measured := polynomialLength_executes (extra+2) w.witnessRoles witnessCoefficient witnessExponent store
    (empty 1 (by decide)) (empty 2 (by decide)) (empty 5 (by decide)) (empty 6 (by decide)) (empty 7 (by decide))
  have measuredRun : Executes (polynomialLength (extra+2) w.witnessRoles witnessCoefficient witnessExponent) store
      (polynomialLengthTime (store (w 0)).length witnessCoefficient witnessExponent) middle := by
    simpa [middle,witness,Complexity.polynomial,Workspace.witnessRoles,witnessSelection] using measured
  have timed := timeRoutine_executes extra w (store (w 0)).length witness coefficient exponent middle
    (by simp [middle,w.injective.eq_iff]) (by simp [middle])
    (by simp [middle,w.injective.eq_iff,empty 3 (by decide)])
    (by simp [middle,w.injective.eq_iff,empty 4 (by decide)])
    (by simp [middle,w.injective.eq_iff,empty 5 (by decide)])
    (by simp [middle,w.injective.eq_iff,empty 6 (by decide)])
    (by simp [middle,w.injective.eq_iff,empty 7 (by decide)])
  have timeIdentity : coefficient*(2*((store (w 0)).length+1)+witness)^exponent =
      timeBound coefficient exponent (store (w 0)) witness := by
    unfold timeBound Complexity.polynomial capacity
    rw [Encoding.frame_length]
    congr 2
    omega
  have combined := measuredRun.sequence timed
  simpa only [boundsRoutine,boundsCost,middle,timeIdentity,witness] using combined

end Counting.External.CookLevin.StackGenerator
