import Counting.StackDagReferenceItem

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def noIncomingReference (target : Nat) (edges : List (Nat×Nat)) : Bool:=
  edges.all (fun edge=>decide (edge.1≠target))

def referenceEdgesStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (target : Nat) (edges : List (Nat×Nat)) (suffix : List Bool) : Store 33:=
  Function.update (Function.update (Function.update store 30 []) 28 suffix) 1
    ((accepted && noIncomingReference target edges)::tail)

theorem referenceEdges_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e22 : store 22=[]) (e31 : store 31=[])
    (target : Nat) (targetCode : store 26=target.bits)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 28=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix)
    (bits : List Bool) (counter : store 30=bits) (countEq : bits.length=edges.length) :
    ∃ time ≤ edges.length*(50*((store 28).length+target.size+1)+2)+1,
      Executes (forEach 30 referenceItem) store time (referenceEdgesStore store accepted tail target edges suffix) := by
  induction edges generalizing store accepted bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 30=[]:=counter.trans emptyBits
    have source : store 28=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (30:Fin 35) referenceItem store empty
    have same : referenceEdgesStore store accepted tail target [] suffix=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r28 : r=28 <;> by_cases r30 : r=30 <;>
        simp [referenceEdgesStore,noIncomingReference,r1,r28,r30,status,empty,source]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | cons edge edges ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      let consumed:=Function.update store 30 bits
      let remaining:=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix
      have headInput : consumed 28=(Encoding.product Encoding.natural Encoding.natural).encode edge++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (28:Fin 35)≠30),Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=referenceItem_executes consumed accepted tail
        (by simp [consumed,status]) (by simp [consumed,e2]) (by simp [consumed,e3]) (by simp [consumed,e4])
        (by simp [consumed,e22]) (by simp [consumed,e31]) target (by simp [consumed,targetCode]) edge remaining headInput
      let middle:=referenceItemStore consumed accepted tail target edge remaining
      let nextAccepted:=accepted && decide (edge.1≠target)
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted
        (by simp [middle,referenceItemStore,nextAccepted])
        (by simp [middle,referenceItemStore,consumed,e2]) (by simp [middle,referenceItemStore,consumed,e3])
        (by simp [middle,referenceItemStore,consumed,e4]) (by simp [middle,referenceItemStore,consumed,e22])
        (by simp [middle,referenceItemStore,consumed,e31])
        (by simp [middle,referenceItemStore,consumed,targetCode]) (by simp [middle,referenceItemStore,remaining])
        bits (by simp [middle,referenceItemStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (30:Fin 35) referenceItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : referenceEdgesStore middle nextAccepted tail target edges suffix=
          referenceEdgesStore store accepted tail target (edge::edges) suffix:=by
        funext r
        by_cases r1 : r=1 <;> by_cases r28 : r=28 <;> by_cases r30 : r=30 <;>
          simp [referenceEdgesStore,noIncomingReference,middle,referenceItemStore,consumed,nextAccepted,
            r1,r28,r30,Bool.and_assoc,decide_not]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 28=store 28:=by simp [consumed]
        rw [inputSame] at bodyBound
        have remainingLength : (middle 28).length≤(store 28).length:=by
          rw [input]
          simp only [middle,referenceItemStore,Function.update_of_ne (by decide : (28:Fin 35)≠1),Function.update_self]
          simp only [remaining,Encoding.sequence,List.length_append]
          omega
        have tailLimit : tailTime≤edges.length*(50*((store 28).length+target.size+1)+2)+1:=by
          apply tailBound.trans;gcongr
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.DagValidation
