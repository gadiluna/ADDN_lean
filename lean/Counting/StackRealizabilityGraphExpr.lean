import Counting.StackReadBranch
import Counting.StackBooleanFold

namespace Counting.StackMachine.RealizabilityCheck.GraphExpr
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A fixed Boolean circuit is compiled into finite stack control; its
arity are read from previously computed flags, never semantic oracles. -/
inductive Expr (arity : Nat) where
  | constant : Bool → Expr arity
  | atom : Fin arity → Expr arity
  | binary : BooleanFold.Kind → Expr arity → Expr arity → Expr arity
  deriving Repr

def eval (values : Fin arity → Bool) : Expr arity → Bool
  | .constant bit=>bit
  | .atom index=>values index
  | .binary kind left right=>BooleanFold.operation kind (eval values left) (eval values right)

def cost : Expr arity → Nat
  | .constant _=>1
  | .atom _=>4
  | .binary _ left right=>cost left+cost right+5

def combine (kind : BooleanFold.Kind) (output : Fin (registers+2)) : Routine registers where
  states:=5
  code control:=match control.val with
    | 0=>.pop output 1 1 2
    | 1=>.pop output (BooleanFold.pushState (BooleanFold.operation kind false false))
        (BooleanFold.pushState (BooleanFold.operation kind false false))
        (BooleanFold.pushState (BooleanFold.operation kind true false))
    | 2=>.pop output (BooleanFold.pushState (BooleanFold.operation kind false true))
        (BooleanFold.pushState (BooleanFold.operation kind false true))
        (BooleanFold.pushState (BooleanFold.operation kind true true))
    | 3=>.push output false 5
    | 4=>.push output true 5
    | _=>.halt

theorem combine_executes (kind : BooleanFold.Kind) (output : Fin (registers+2))
    (store : Store registers) (first second : Bool) (tail : List Bool)
    (content : store output=second::first::tail) :
    Executes (combine kind output) store 3
      (Function.update store output (BooleanFold.operation kind first second::tail)):=by
  refine ⟨⟨5,Function.update store output (BooleanFold.operation kind first second::tail)⟩,?_,rfl,rfl⟩
  cases kind <;> cases first <;> cases second <;>
    simp [Machine.run,step,combine,program,content,BooleanFold.pushState,
      BooleanFold.operation,Function.update_idem]

def compile (flags : Fin arity → Fin (registers+2)) (output : Fin (registers+2)) :
    Expr arity → Routine registers
  | .constant bit=>pushBit output bit
  | .atom index=>branchRead (flags index) (pushBit output true) (pushBit output false)
  | .binary kind left right=>sequence (compile flags output left)
      (sequence (compile flags output right) (combine kind output))

theorem compile_executes (flags : Fin arity → Fin (registers+2))
    (output : Fin (registers+2)) (separate : ∀i,flags i≠output)
    (expression : Expr arity) (values : Fin arity → Bool)
    (store : Store registers) (tails : Fin arity → List Bool)
    (contents : ∀i,store (flags i)=values i::tails i) :
    Executes (compile flags output expression) store (cost expression)
      (Function.update store output (eval values expression::store output)):=by
  induction expression generalizing store with
  | constant bit=>exact pushBit_executes output bit store
  | atom index=>
    apply branchRead_executes (flags index) (pushBit output true) (pushBit output false)
      (values index) (tails index) store _ 1 (contents index)
    cases answer : values index <;> simp only [eval,answer,Bool.false_eq_true,if_false,if_true]
    all_goals exact pushBit_executes output _ store
  | binary kind left right ihLeft ihRight=>
    have first:=ihLeft store contents
    let pushed:=Function.update store output (eval values left::store output)
    have second:=ihRight pushed (by intro i;simp [pushed,Function.update_of_ne (separate i),contents i])
    have leftAt : pushed output=eval values left::store output:=by simp [pushed]
    rw [leftAt] at second
    let read:=Function.update pushed output (eval values right::eval values left::store output)
    have combined:=combine_executes kind output read (eval values left) (eval values right)
      (store output) (by simp [read])
    have final : Function.update read output (BooleanFold.operation kind (eval values left) (eval values right)::store output)=
        Function.update store output (BooleanFold.operation kind (eval values left) (eval values right)::store output):=by
      simp [read,pushed]
    rw [final] at combined
    convert first.sequence (second.sequence combined) using 1 <;> first | rfl | (simp only [cost];omega)

/-- Order: new-x, old-x, outside-x, new-y, old-y, outside-y,
degree-x, leaving-x, leaving-y, deficit-x, parent(x,y), incoming(y,x). -/
def arc : Expr 12:=
  .binary .disjunction
    (.binary .disjunction
      (.binary .disjunction
        (.binary .conjunction (.atom 0) (.binary .conjunction (.atom 4)
          (.binary .conjunction (.atom 10) (.atom 6))))
        (.binary .conjunction (.atom 1)
          (.binary .conjunction (.atom 3) (.atom 11))))
      (.binary .conjunction (.atom 2)
        (.binary .conjunction (.atom 4) (.atom 8))))
    (.binary .conjunction (.atom 1) (.binary .conjunction (.atom 5)
      (.binary .disjunction (.atom 7) (.atom 9))))

def active : Expr 3:=.binary .disjunction
  (.binary .disjunction (.atom 0) (.atom 1)) (.atom 2)

theorem eval_arc (values : Fin 12 → Bool) : eval values arc=(
    (values 0 && values 4 && (values 10 && values 6)) ||
    (values 1 && values 3 && values 11) ||
    (values 2 && values 4 && values 8) ||
    (values 1 && values 5 && (values 7 || values 9))):=by
  simp only [arc,eval,BooleanFold.operation,Bool.and_assoc]

theorem eval_active (values : Fin 3 → Bool) : eval values active=(values 0 || values 1 || values 2):=rfl

example : cost arc=121:=by decide
example : cost active=22:=by decide

end Counting.StackMachine.RealizabilityCheck.GraphExpr
