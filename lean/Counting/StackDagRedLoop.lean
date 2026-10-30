import Counting.StackDagRedItem

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def redLoopStore (store : Store 30) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current targetLevel : Nat) (edges : List (Nat×Nat))
    (suffix : List Bool) : Store 30:=
  Function.update (Function.update (Function.update store 30 []) 28 suffix) 1
    ((accepted && edges.all (fun edge=>redCondition values current targetLevel edge.1))::tail)

theorem redLoop_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 32,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 32,r∈({18,19,20,22,25,26,31}:Finset (Fin 32)) → store r=[])
    (values : List Executable.Node) (current targetLevel : Nat) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (level : store 21=targetLevel.bits) (budget : (store 29).length=current)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 28=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix)
    (bits : List Bool) (counter : store 30=bits) (length : bits.length=edges.length)
    (limit : Nat) (inputBound : (store 28).length≤limit) :
    ∃ time ≤ edges.length*(20100*((store 17).length+limit+targetLevel.size+1)^4+2)+1,
      Executes (forEach 30 redItem) store time (redLoopStore store accepted tail values current targetLevel edges suffix) := by
  induction edges generalizing store accepted bits with
  | nil=>
    have bitsEmpty : bits=[]:=List.length_eq_zero_iff.mp length
    have counterEmpty : store 30=[]:=counter.trans bitsEmpty
    obtain ⟨ran,halted⟩:=repeat_empty (30:Fin 32) redItem store counterEmpty
    have same : redLoopStore store accepted tail values current targetLevel [] suffix=store := by
      have inputEq : store 28=suffix:=by simpa [Encoding.sequence] using input
      simp only [redLoopStore,List.all_nil,Bool.and_true,←counterEmpty,←inputEq,←status,
        Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | cons edge edges ih=>
    cases bits with
    | nil=>simp at length
    | cons bit bits=>
      let consumed:=Function.update store 30 bits
      have consumedWork (r : Fin 32) (small : r.val<17) (ne : r≠1) : consumed r=[] := by
        have n30 : r≠30:=by intro eq;subst r;norm_num at small
        simp [consumed,n30,work r small ne]
      have consumedExtra (r : Fin 32) (member : r∈({18,19,20,22,25,26,31}:Finset (Fin 32))) : consumed r=[] := by
        have n30 : r≠30:=by intro eq;subst r;exact (by decide : (30:Fin 32)∉({18,19,20,22,25,26,31}:Finset (Fin 32))) member
        simp [consumed,n30,extraWork r member]
      have inputEq : consumed 28=(Encoding.product Encoding.natural Encoding.natural).encode edge++
          (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix) := by
        simpa [consumed,Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=redItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork consumedExtra values current targetLevel inside sourceSuffix
        (by simp [consumed,source]) (by simp [consumed,level]) (by simp [consumed,budget]) edge
        (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix) inputEq
      let nextAccepted:=accepted && redCondition values current targetLevel edge.1
      let middle:=redItemStore consumed accepted tail values current targetLevel edge
        (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix)
      have middleWork (r : Fin 32) (small : r.val<17) (ne : r≠1) : middle r=[] := by
        have n28 : r≠28:=by intro eq;subst r;norm_num at small
        simp [middle,redItemStore,ne,n28,consumedWork r small ne]
      have middleExtra (r : Fin 32) (member : r∈({18,19,20,22,25,26,31}:Finset (Fin 32))) : middle r=[] := by
        have n1 : r≠1:=by intro eq;subst r;exact (by decide : (1:Fin 32)∉({18,19,20,22,25,26,31}:Finset (Fin 32))) member
        have n28 : r≠28:=by intro eq;subst r;exact (by decide : (28:Fin 32)∉({18,19,20,22,25,26,31}:Finset (Fin 32))) member
        simp [middle,redItemStore,n1,n28,consumedExtra r member]
      have sourceSame : middle 17=store 17:=by simp [middle,redItemStore,consumed]
      have nextSource : middle 17=Encoding.sequence Encoding.node values++sourceSuffix:=sourceSame.trans source
      have nextStatus : middle 1=nextAccepted::tail:=by simp [middle,redItemStore,nextAccepted]
      have nextLevel : middle 21=targetLevel.bits:=by simp [middle,redItemStore,consumed,level]
      have nextBudget : (middle 29).length=current:=by simp [middle,redItemStore,consumed,budget]
      have nextInput : middle 28=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix:=by
        simp [middle,redItemStore]
      have nextCounter : middle 30=bits:=by simp [middle,redItemStore,consumed]
      have nextLength : bits.length=edges.length:=by simpa using length
      have nextBound : (middle 28).length≤limit := by
        rw [nextInput]
        rw [input,Encoding.sequence,List.length_append,List.length_append] at inputBound
        simp only [List.length_append]
        omega
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted nextStatus
        middleWork middleExtra nextSource nextLevel nextBudget nextInput bits nextCounter nextLength nextBound
      have firstRun:=repeat_iteration (30:Fin 32) redItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have result : redLoopStore middle nextAccepted tail values current targetLevel edges suffix=
          redLoopStore store accepted tail values current targetLevel (edge::edges) suffix := by
        funext r
        by_cases r1 : r=1
        · subst r;simp [redLoopStore,nextAccepted,Bool.and_assoc]
        · by_cases r28 : r=28
          · subst r;simp [redLoopStore]
          · by_cases r30 : r=30
            · subst r;simp [redLoopStore]
            · simp [redLoopStore,middle,redItemStore,consumed,r1,r28,r30]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans result⟩
      · have bodyLimit : bodyTime≤20100*((store 17).length+limit+targetLevel.size+1)^4 := by
          apply bodyBound.trans
          simp only [consumed]
          simp
          gcongr
        rw [sourceSame] at tailBound
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.DagValidation
