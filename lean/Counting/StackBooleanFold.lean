import Counting.StackRoutineBasic

namespace Counting.StackMachine.BooleanFold
open Routine

inductive Kind where
  | conjunction | disjunction
  deriving DecidableEq, Repr

def operation : Kind → Bool → Bool → Bool
  | .conjunction, a, b => a && b
  | .disjunction, a, b => a || b

def pushState (bit : Bool) : Fin 6 := if bit then 4 else 3

/-- Five fixed states consume a source bit, read the accumulator head and
write the Boolean result. The looping form stops at the empty source. -/
def routine {registers : Nat} (kind : Kind) (source accumulator : Fin (registers+2))
    (looping : Bool) : Routine registers where
  states := 5
  code control := match control.val with
    | 0 => .pop source (if looping then 5 else 1) 1 2
    | 1 => .pop accumulator (pushState (operation kind false false))
        (pushState (operation kind false false)) (pushState (operation kind true false))
    | 2 => .pop accumulator (pushState (operation kind false true))
        (pushState (operation kind false true)) (pushState (operation kind true true))
    | 3 => .push accumulator false (if looping then 0 else 5)
    | 4 => .push accumulator true (if looping then 0 else 5)
    | _ => .halt

abbrev single {registers : Nat} (kind : Kind) (source accumulator : Fin (registers+2)) :=
  routine kind source accumulator false
abbrev fold {registers : Nat} (kind : Kind) (source accumulator : Fin (registers+2)) :=
  routine kind source accumulator true

def updated {registers : Nat} (source accumulator : Fin (registers+2))
    (store : Store registers) (remaining : List Bool) (value : Bool) (tail : List Bool) :=
  Function.update (Function.update store source remaining) accumulator (value::tail)

theorem iteration (kind : Kind) (source accumulator : Fin (registers+2))
    (distinct : source ≠ accumulator) (looping : Bool) (store : Store registers)
    (bit value : Bool) (rest tail : List Bool)
    (contents : store source=bit::rest) (accumulated : store accumulator=value::tail) :
    Machine.run (step (routine kind source accumulator looping).program) 3 ⟨0,store⟩ =
      some ⟨if looping then 0 else 5,updated source accumulator store rest (operation kind value bit) tail⟩ := by
  cases kind <;> cases bit <;> cases value <;> cases looping <;>
    simp [Machine.run,step,routine,program,contents,accumulated,pushState,operation,
      updated,Function.update_of_ne distinct.symm,Function.update_idem] <;> rfl

theorem single_executes (kind : Kind) (source accumulator : Fin (registers+2))
    (distinct : source ≠ accumulator) (store : Store registers)
    (bit value : Bool) (rest tail : List Bool)
    (contents : store source=bit::rest) (accumulated : store accumulator=value::tail) :
    Executes (single kind source accumulator) store 3
      (updated source accumulator store rest (operation kind value bit) tail) := by
  exact ⟨⟨5,_⟩,iteration kind source accumulator distinct false store bit value rest tail contents accumulated,rfl,rfl⟩

theorem fold_executes (kind : Kind) (source accumulator : Fin (registers+2))
    (distinct : source ≠ accumulator) (store : Store registers)
    (bits : List Bool) (value : Bool) (tail : List Bool)
    (contents : store source=bits) (accumulated : store accumulator=value::tail) :
    Executes (fold kind source accumulator) store (3*bits.length+1)
      (updated source accumulator store [] (bits.foldl (operation kind) value) tail) := by
  induction bits generalizing store value with
  | nil =>
      have same : updated source accumulator store [] value tail=store := by
        simp [updated,←contents,Function.update_eq_self,←accumulated]
      refine ⟨⟨5,store⟩,?_,rfl,same.symm⟩
      simp [Machine.run,step,fold,routine,program,contents]
      rfl
  | cons bit rest ih =>
      let next := updated source accumulator store rest (operation kind value bit) tail
      have nextSource : next source=rest := by simp [next,updated,distinct]
      have nextAccumulator : next accumulator=operation kind value bit::tail := by simp [next,updated]
      obtain ⟨finish,ran,halted,result⟩ := ih next (operation kind value bit) nextSource nextAccumulator
      refine ⟨finish,?_,halted,?_⟩
      · rw [List.length_cons,show 3*(rest.length+1)+1=3+(3*rest.length+1) by omega,
          Machine.run_add,iteration kind source accumulator distinct true store bit value rest tail contents accumulated,
          Option.bind_some]
        exact ran
      · rw [result]
        simp only [List.foldl_cons,updated,next]
        funext r
        by_cases atSource : r=source
        · subst r; simp [distinct]
        · by_cases atAccumulator : r=accumulator
          · subst r; simp
          · simp [Function.update_of_ne,atSource,atAccumulator]

theorem fold_conjunction (bits : List Bool) (value : Bool) :
    bits.foldl (operation .conjunction) value = (value && bits.all id) := by
  induction bits generalizing value with
  | nil => simp
  | cons bit rest ih => simp only [List.foldl_cons,ih,List.all_cons,operation,id_eq,Bool.and_assoc]

theorem fold_disjunction (bits : List Bool) (value : Bool) :
    bits.foldl (operation .disjunction) value = (value || bits.any id) := by
  induction bits generalizing value with
  | nil => simp
  | cons bit rest ih => simp only [List.foldl_cons,ih,List.any_cons,operation,id_eq,Bool.or_assoc]

end Counting.StackMachine.BooleanFold
