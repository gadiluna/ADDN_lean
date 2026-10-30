import Counting.StackRealizabilityReachSource

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Consume one bit from each vector (missing bits mean false), preserving
the tail below the Boolean accumulator. Every branch takes four instructions. -/
def implicationItem : Routine 2 where
  states:=7
  code control:=match control.val with
    | 0=>.pop 0 1 1 2
    | 1=>.pop 1 3 3 3
    | 2=>.pop 1 4 4 3
    | 3=>.pop 3 5 5 6
    | 4=>.pop 3 5 5 5
    | 5=>.push 3 false 7
    | 6=>.push 3 true 7
    | _=>.halt

def implicationItemStore (store : Store 2) (value : Bool) (tail : List Bool) : Store 2:=
  Function.update (Function.update (Function.update store 0 (store 0).tail) 1 (store 1).tail) 3
    ((value && (!(store 0).headD false || (store 1).headD false))::tail)

theorem implicationItem_executes (store : Store 2) (value : Bool) (tail : List Bool)
    (accumulated : store 3=value::tail) :
    Executes implicationItem store 4 (implicationItemStore store value tail):=by
  refine ⟨⟨7,_⟩,?_,rfl,rfl⟩
  cases first : store 0 with
  | nil=>
    cases second : store 1 with
    | nil=>cases value <;> simp [Machine.run,step,implicationItem,program,first,second,accumulated] <;>
        (funext r;fin_cases r <;> simp_all [Function.update] <;> rfl)
    | cons b bs=>cases b <;> cases value <;> simp [Machine.run,step,implicationItem,program,first,second,accumulated] <;>
        (funext r;fin_cases r <;> simp_all [Function.update] <;> rfl)
  | cons a as=>
    cases second : store 1 with
    | nil=>cases a <;> cases value <;> simp [Machine.run,step,implicationItem,program,first,second,accumulated] <;>
        (funext r;fin_cases r <;> simp_all [Function.update] <;> rfl)
    | cons b bs=>cases a <;> cases b <;> cases value <;> simp [Machine.run,step,implicationItem,program,first,second,accumulated] <;>
        (funext r;fin_cases r <;> simp_all [Function.update] <;> rfl)

def implicationFold : Nat → List Bool → List Bool → Bool → Bool
  | 0,_,_,value=>value
  | count+1,active,seen,value=>implicationFold count active.tail seen.tail
      (value && (!active.headD false || seen.headD false))

def implicationLoopStore (store : Store 2) (count : Nat) (value : Bool) (tail : List Bool) : Store 2:=
  Function.update (Function.update (Function.update (Function.update store 2 [])
    0 ((store 0).drop count)) 1 ((store 1).drop count)) 3
    (implicationFold count (store 0) (store 1) value::tail)

theorem implicationLoop_executes (store : Store 2) (counter : List Bool) (counted : store 2=counter)
    (value : Bool) (tail : List Bool) (accumulated : store 3=value::tail) :
    Executes (forEach 2 implicationItem) store (6*counter.length+1)
      (implicationLoopStore store counter.length value tail):=by
  induction counter generalizing store value with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (2:Fin 4) implicationItem store counted
    have final : implicationLoopStore store 0 value tail=store:=by
      funext r
      fin_cases r <;> simp [implicationLoopStore,implicationFold,counted,accumulated]
    exact ⟨⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit counter ih=>
    let consumed:=Function.update store 2 counter
    obtain ⟨finishBody,bodyRun,bodyHalted,bodyStore⟩:=implicationItem_executes consumed value tail
      (by simp [consumed,accumulated])
    let middle:=implicationItemStore consumed value tail
    let next:=value && (!(store 0).headD false || (store 1).headD false)
    obtain ⟨finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,implicationItemStore,consumed]) next
      (by simp [middle,implicationItemStore,consumed,next])
    have firstRun:=repeat_iteration (2:Fin 4) implicationItem store bit counter counted 4 finishBody bodyRun bodyHalted
    have final : implicationLoopStore middle counter.length next tail=
        implicationLoopStore store (bit::counter).length value tail:=by
      funext r
      fin_cases r <;> simp [implicationLoopStore,implicationFold,middle,implicationItemStore,consumed,next,
        List.drop_tail]
    refine ⟨finishTail,?_,tailHalted,tailStore.trans final⟩
    rw [List.length_cons,show 6*(counter.length+1)+1=4+2+(6*counter.length+1) by omega,
      Machine.run_add,firstRun,Option.bind_some,bodyStore]
    exact tailRun

theorem implicationFold_all (count : Nat) (active seen : List Bool) (value : Bool) :
    implicationFold count active seen value=
      (value && (List.range count).all (fun i=>!RealizabilityVerifier.BitGraph.bitAt active i ||
        RealizabilityVerifier.BitGraph.bitAt seen i)):=by
  induction count generalizing active seen value with
  | zero=>simp [implicationFold]
  | succ count ih=>
    rw [implicationFold,ih]
    simp only [List.range_succ_eq_map,List.all_cons,List.all_map,Bool.and_assoc]
    congr 2
    · cases active <;> cases seen <;> rfl
    · apply congrArg (fun f=>(List.range count).all f)
      funext i
      simp [RealizabilityVerifier.BitGraph.bitAt,List.getElem?_tail]

end Counting.StackMachine.RealizabilityCheck
