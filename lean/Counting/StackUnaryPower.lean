import Counting.StackUnaryMultiply
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine

abbrev PowerWorkspace (extra : Nat) := Fin 5 ↪ Fin (extra+5)

/-- Workspace roles: base, accumulator, loop counter, product, temporary. -/
def powerStep (extra : Nat) (workspace : PowerWorkspace extra) : Routine (extra+3) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+2) (workspace 0) (workspace 2) (workspace 4)))
    (sequence (repeatedCopy (extra+2) (workspace 1) (workspace 2) (workspace 3) (workspace 4))
      (sequence (clear (workspace 1))
        (ofProgram (ListPrograms.reverseProgram (extra+3) (workspace 3) (workspace 1)))))

theorem workspace_ne (workspace : PowerWorkspace extra) {first second : Fin 5} (distinct : first ≠ second) :
    workspace first ≠ workspace second := fun same => distinct (workspace.injective same)

theorem powerStep_executes (extra : Nat) (w : PowerWorkspace extra) (store : Fin (extra+5) → List Bool)
    (base accumulator : Nat) (baseValue : store (w 0) = List.replicate base true)
    (accValue : store (w 1) = List.replicate accumulator true)
    (counterEmpty : store (w 2) = []) (productEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    Executes (powerStep extra w) store (7*accumulator*base+9*base+accumulator+8)
      (Function.update store (w 1) (List.replicate (accumulator*base) true)) := by
  let copied := Function.update store (w 2) (List.replicate base true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+2) (w 0) (w 2) (w 4))) store
      (5*base+2) copied := by
    obtain ⟨finish, run, halted, finalStore⟩ := copy_executes (extra+2) (w 0) (w 2) (w 4)
      (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide)) store workEmpty
    refine ⟨finish, ?_, halted, ?_⟩
    · simpa only [baseValue,List.length_replicate] using run
    · rw [finalStore]
      funext register
      by_cases equal : register = w 2
      · subst register; simp [copied,baseValue,counterEmpty]
      · simp [copied,Function.update,equal]
        intro same
        exact False.elim (equal same)
  let multiplied := Function.update (Function.update copied (w 2) []) (w 3) (List.replicate (base*accumulator) true)
  have multiplication : Executes (repeatedCopy (extra+2) (w 1) (w 2) (w 3) (w 4)) copied
      ((5*accumulator+4)*base+1) multiplied := by
    have left : copied (w 1) = List.replicate accumulator true := by simp [copied,w.injective.eq_iff,accValue]
    have right : copied (w 2) = List.replicate base true := by simp [copied]
    have work : copied (w 4) = [] := by simp [copied,w.injective.eq_iff,workEmpty]
    have product : copied (w 3) = [] := by simp [copied,w.injective.eq_iff,productEmpty]
    simpa only [product,List.append_nil,multiplied] using
      unary_multiply_executes (extra+2) (w 1) (w 2) (w 3) (w 4)
        (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide))
        (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide))
        accumulator base copied left right work
  let cleared := Function.update multiplied (w 1) []
  have accMultiplied : multiplied (w 1) = List.replicate accumulator true := by
    simp [multiplied,copied,w.injective.eq_iff,accValue]
  have clearing : Executes (clear (w 1)) multiplied (accumulator+1) cleared := by
    simpa only [accMultiplied,List.length_replicate,cleared] using clear_executes (w 1) multiplied
  have source : cleared (w 3) = List.replicate (base*accumulator) true := by
    simp [cleared,multiplied,w.injective.eq_iff]
  have target : cleared (w 1) = [] := by simp [cleared]
  let result := Function.update (Function.update cleared (w 3) []) (w 1) (List.replicate (base*accumulator) true)
  have reversed : Executes (ofProgram (ListPrograms.reverseProgram (extra+3) (w 3) (w 1))) cleared
      (2*(base*accumulator)+1) result := by
    obtain ⟨finish, run, halted, finalStore⟩ :=
      reverse_executes (extra+3) (w 3) (w 1) (workspace_ne w (by decide)) cleared
    refine ⟨finish, ?_, halted, ?_⟩
    · simpa only [source,List.length_replicate] using run
    · rw [finalStore]
      funext register
      by_cases equal : register = w 1
      · subst register; simp [result,source,target]
      · simp [result,Function.update,equal]
        exact (if_neg equal).symm
  have combined := copy.sequence (multiplication.sequence (clearing.sequence reversed))
  have cost : 5*base+2+1+(((5*accumulator+4)*base+1)+1+((accumulator+1)+1+(2*(base*accumulator)+1))) =
      7*accumulator*base+9*base+accumulator+8 := by ring
  have result_eq : result = Function.update store (w 1) (List.replicate (accumulator*base) true) := by
    funext register
    by_cases a : register = w 1
    · subst register
      simp [result, Nat.mul_comm]
    · by_cases b : register = w 2
      · subst register
        simp [result,cleared,multiplied,copied,w.injective.eq_iff,counterEmpty]
      · by_cases c : register = w 3
        · subst register
          simp [result,cleared,multiplied,copied,w.injective.eq_iff,productEmpty]
        · simp [result,cleared,multiplied,copied,a,b,c]
  rw [cost,result_eq] at combined
  exact combined

/-- The exponent is a compile-time parameter; each multiplication is a
finite routine and each connecting jump is charged. -/
def power (extra : Nat) (workspace : PowerWorkspace extra) : Nat → Routine (extra+3)
  | 0 => skip (extra+3)
  | exponent+1 => sequence (power extra workspace exponent) (powerStep extra workspace)

def powerTime (base accumulator : Nat) : Nat → Nat
  | 0 => 0
  | exponent+1 => powerTime base accumulator exponent+1+
      (7*(accumulator*base^exponent)*base+9*base+accumulator*base^exponent+8)

theorem power_executes (extra : Nat) (w : PowerWorkspace extra) (exponent : Nat)
    (store : Fin (extra+5) → List Bool) (base accumulator : Nat)
    (baseValue : store (w 0) = List.replicate base true)
    (accValue : store (w 1) = List.replicate accumulator true)
    (counterEmpty : store (w 2) = []) (productEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    Executes (power extra w exponent) store (powerTime base accumulator exponent)
      (Function.update store (w 1) (List.replicate (accumulator*base^exponent) true)) := by
  induction exponent with
  | zero =>
      simpa only [power,powerTime,pow_zero,Nat.mul_one,← accValue,Function.update_eq_self] using skip_executes store
  | succ exponent ih =>
      let middle := Function.update store (w 1) (List.replicate (accumulator*base^exponent) true)
      have baseMiddle : middle (w 0) = List.replicate base true := by simp [middle,w.injective.eq_iff,baseValue]
      have accMiddle : middle (w 1) = List.replicate (accumulator*base^exponent) true := by simp [middle]
      have counterMiddle : middle (w 2) = [] := by simp [middle,w.injective.eq_iff,counterEmpty]
      have productMiddle : middle (w 3) = [] := by simp [middle,w.injective.eq_iff,productEmpty]
      have workMiddle : middle (w 4) = [] := by simp [middle,w.injective.eq_iff,workEmpty]
      have next := powerStep_executes extra w middle base (accumulator*base^exponent)
        baseMiddle accMiddle counterMiddle productMiddle workMiddle
      have combined := ih.sequence next
      simpa only [power,powerTime,middle,Function.update_idem,pow_succ,Nat.mul_assoc] using combined

/-- Explicit polynomial bound for a fixed exponent. -/
theorem powerTime_bound (base accumulator exponent : Nat) :
    powerTime base accumulator exponent ≤ 20*exponent*(accumulator+1)*(base+1)^exponent := by
  induction exponent with
  | zero => simp [powerTime]
  | succ exponent ih =>
      have one : 1 ≤ (base+1)^exponent := Nat.one_le_pow exponent _ (by omega)
      have powerMono : base^exponent ≤ (base+1)^exponent := Nat.pow_le_pow_left (by omega) _
      have previous : powerTime base accumulator exponent ≤
          20*exponent*(accumulator+1)*(base+1)^(exponent+1) := by
        apply ih.trans
        rw [pow_succ]
        nlinarith
      have contribution : 1+(7*(accumulator*base^exponent)*base+9*base+accumulator*base^exponent+8) ≤
          20*(accumulator+1)*(base+1)^(exponent+1) := by
        rw [pow_succ]
        have product := Nat.mul_le_mul_left (7*accumulator*base+accumulator) powerMono
        have constant := Nat.mul_le_mul_left (9*base+9) one
        have coefficient : 7*accumulator*base+accumulator+9*base+9 ≤ 20*(accumulator+1)*(base+1) := by
          nlinarith
        have scaled := Nat.mul_le_mul_right ((base+1)^exponent) coefficient
        nlinarith
      simp only [powerTime]
      nlinarith

end Counting.StackMachine.Routine
