import Counting.StackMachine

/-! A regression interpreter for the same stack transitions. Materializing
finite register stores prevents host-language function-update chains. Neither
the machine nor the number of executed transitions changes. -/
namespace Counting.StackMachine.TestRun

/-- Refresh the finite representation of a register store. -/
def materialize {program : Program} (config : Config program) : Config program :=
  let registers := Array.ofFn config.store
  ⟨config.control,fun r => registers[r.val]'(by simpa only [registers,Array.size_ofFn] using r.isLt)⟩

theorem materialize_eq {program : Program} (config : Config program) : materialize config=config := by
  cases config with
  | mk control store =>
    dsimp [materialize]
    congr 1
    funext r
    simp

/-- Exactly `time` original stack steps, with equal register stores. -/
def run (program : Program) : Nat → Config program → Option (Config program)
  | 0,config => some config
  | time+1,config => (step program config).bind (fun next => run program time (materialize next))

theorem run_eq (program : Program) (time : Nat) (config : Config program) :
    run program time config=Machine.run (step program) time config := by
  induction time generalizing config with
  | zero => rfl
  | succ time ih =>
    simp only [run,Machine.run,materialize_eq,ih]

/-- Bounded halting search; the returned counter counts executed transitions,
not the final inspection of a halted instruction. -/
def searchSpec (program : Program) : Nat → Config program → Option (Nat × Config program)
  | 0,_ => none
  | fuel+1,config => match step program config with
    | none => some (0,config)
    | some next => (searchSpec program fuel (materialize next)).map (fun pair => (pair.1+1,pair.2))

theorem searchSpec_sound (program : Program) (fuel : Nat) (config finish : Config program) (time : Nat)
    (finished : searchSpec program fuel config=some (time,finish)) :
    time<fuel ∧ Machine.run (step program) time config=some finish ∧ step program finish=none := by
  induction fuel generalizing config time with
  | zero => simp [searchSpec] at finished
  | succ fuel ih =>
    cases transition : step program config with
    | none =>
      simp only [searchSpec,transition,Option.some.injEq,Prod.mk.injEq] at finished
      obtain ⟨rfl,rfl⟩ := finished
      exact ⟨by omega,rfl,transition⟩
    | some next =>
      simp only [searchSpec,transition,materialize_eq] at finished
      obtain ⟨pair,recursive,equal⟩ := Option.map_eq_some_iff.mp finished
      obtain ⟨previous,output⟩ := pair
      cases equal
      obtain ⟨bounded,run,halted⟩ := ih next previous recursive
      exact ⟨by omega,by simpa only [Machine.run,transition,Option.bind_some] using run,halted⟩

/-- Tail-recursive regression loop with an accumulated step counter. -/
def finishWithinFrom (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0,_,_ => none
  | fuel+1,elapsed,config => match step program config with
    | none => some (elapsed,config)
    | some next => finishWithinFrom program fuel (elapsed+1) (materialize next)

theorem finishWithinFrom_eq (program : Program) (fuel elapsed : Nat) (config : Config program) :
    finishWithinFrom program fuel elapsed config=
      (searchSpec program fuel config).map (fun pair => (elapsed+pair.1,pair.2)) := by
  induction fuel generalizing elapsed config with
  | zero => rfl
  | succ fuel ih =>
    cases transition : step program config with
    | none => simp [finishWithinFrom,searchSpec,transition]
    | some next =>
      simp only [finishWithinFrom,searchSpec,transition,ih,Option.map_map]
      congr 1
      funext pair
      change (elapsed+1+pair.1,pair.2)=(elapsed+(pair.1+1),pair.2)
      congr 1
      omega

/-- Halt within fuel, counting the original transitions exactly. -/
def finishWithin (program : Program) (fuel : Nat) (config : Config program) : Option (Nat × Config program) :=
  finishWithinFrom program fuel 0 config

theorem finishWithin_eq (program : Program) (fuel : Nat) (config : Config program) :
    finishWithin program fuel config=searchSpec program fuel config := by
  rw [finishWithin,finishWithinFrom_eq]
  cases searchSpec program fuel config with
  | none => rfl
  | some pair => cases pair; simp

theorem finishWithin_sound (program : Program) (fuel : Nat) (config finish : Config program) (time : Nat)
    (finished : finishWithin program fuel config=some (time,finish)) :
    time<fuel ∧ Machine.run (step program) time config=some finish ∧ step program finish=none := by
  rw [finishWithin_eq] at finished
  exact searchSpec_sound program fuel config finish time finished

end Counting.StackMachine.TestRun
