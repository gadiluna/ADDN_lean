import Counting.StackLookupDrop

/-! Reading a possibly absent bit retains an explicit presence flag. -/
namespace Counting.StackMachine.Lookup

set_option backward.isDefEq.respectTransparency false

def headProgram (extra : Nat) (source output status : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 5
  code control := match control.val with
    | 0 => .pop source 3 1 2
    | 1 => .push output false 4
    | 2 => .push output true 4
    | 3 => .push status false 5
    | 4 => .push status true 5
    | _ => .halt

def headCost (input : List Bool) : Nat := if input=[] then 2 else 3

theorem headCost_le (input : List Bool) : headCost input ≤ 3 := by
  unfold headCost
  split_ifs <;> omega

/-- None is represented by a false flag and no output bit; Some false
therefore remains distinguishable from a missing bit. -/
theorem head_executes (extra : Nat) (source output status : Fin (extra+2))
    (so : source ≠ output) (sf : source ≠ status) (of : output ≠ status)
    (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (headProgram extra source output status)) store
      (headCost (store source))
      (Function.update (Function.update (Function.update store source (store source).tail)
        output ((store source).head?.toList++store output))
        status ((store source).head?.isSome::store status)) := by
  refine ⟨⟨5,_⟩,?_,rfl,rfl⟩
  cases input : store source with
  | nil =>
      simp +instances [headCost,input,Machine.run,step,headProgram]
      funext r
      cases h : instDecidableEqFin (extra+2) r status <;> simp_all [Function.update]
      split_ifs <;> simp_all
  | cons bit rest =>
      cases bit <;>
        simp +instances [headCost,input,Machine.run,step,headProgram,Ne.symm so,Ne.symm sf,Ne.symm of]
      all_goals
        funext r
        cases h : instDecidableEqFin (extra+2) r status <;> simp_all [Function.update]

end Counting.StackMachine.Lookup
