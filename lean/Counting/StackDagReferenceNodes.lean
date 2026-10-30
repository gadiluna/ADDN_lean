import Counting.StackDagReferenceNode

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def noTableReference (target : Nat) (nodes : List Executable.Node) : Bool:=nodes.all (noNodeReference target)

def referenceNodesStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (target : Nat) (nodes : List Executable.Node) (suffix : List Bool) : Store 33:=
  Function.update (Function.update (Function.update store 27 []) 28 suffix) 1
    ((accepted && noTableReference target nodes)::tail)

theorem referenceNodes_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,30,31}:Finset (Fin 35)) → store r=[])
    (target : Nat) (targetCode : store 26=target.bits) (targetPlus : store 24=(target+1).bits)
    (nodes : List Executable.Node) (suffix : List Bool)
    (input : store 28=Encoding.sequence Encoding.node nodes++suffix)
    (bits : List Bool) (counter : store 27=bits) (countEq : bits.length=nodes.length) :
    ∃ time ≤ nodes.length*(2200*((store 28).length+target.size+1)^3+2)+1,
      Executes (forEach 27 referenceNode) store time (referenceNodesStore store accepted tail target nodes suffix) := by
  induction nodes generalizing store accepted bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 27=[]:=counter.trans emptyBits
    have source : store 28=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (27:Fin 35) referenceNode store empty
    have same : referenceNodesStore store accepted tail target [] suffix=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r27 : r=27 <;> by_cases r28 : r=28 <;>
        simp [referenceNodesStore,noTableReference,r1,r27,r28,status,empty,source]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | cons node nodes ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      let consumed:=Function.update store 27 bits
      let remaining:=Encoding.sequence Encoding.node nodes++suffix
      have headInput : consumed 28=Encoding.node.encode node++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (28:Fin 35)≠27),Encoding.sequence,List.append_assoc] using input
      have consumedWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : consumed r=[]:=by
        have n27 : r≠27:=by intro eq;subst r;norm_num at small
        simp [consumed,n27,work r small ne]
      have consumedExtra (r : Fin 35) (member : r∈({21,22,23,30,31}:Finset (Fin 35))) : consumed r=[]:=by
        have n27 : r≠27:=by intro eq;subst r;exact (by decide : (27:Fin 35)∉({21,22,23,30,31}:Finset (Fin 35))) member
        simp [consumed,n27,extraWork r member]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=referenceNode_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork consumedExtra target (by simp [consumed,targetCode])
        (by simp [consumed,targetPlus]) node remaining headInput
      let middle:=referenceNodeStore consumed accepted tail target node remaining
      let nextAccepted:=accepted && noNodeReference target node
      have middleWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : middle r=[]:=by
        have n28 : r≠28:=by intro eq;subst r;norm_num at small
        simp [middle,referenceNodeStore,ne,n28,consumedWork r small ne]
      have middleExtra (r : Fin 35) (member : r∈({21,22,23,30,31}:Finset (Fin 35))) : middle r=[]:=by
        have n1 : r≠1:=by intro eq;subst r;exact (by decide : (1:Fin 35)∉({21,22,23,30,31}:Finset (Fin 35))) member
        have n28 : r≠28:=by intro eq;subst r;exact (by decide : (28:Fin 35)∉({21,22,23,30,31}:Finset (Fin 35))) member
        simp [middle,referenceNodeStore,n1,n28,consumedExtra r member]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted
        (by simp [middle,referenceNodeStore,nextAccepted]) middleWork middleExtra
        (by simp [middle,referenceNodeStore,consumed,targetCode])
        (by simp [middle,referenceNodeStore,consumed,targetPlus]) (by simp [middle,referenceNodeStore,remaining])
        bits (by simp [middle,referenceNodeStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (27:Fin 35) referenceNode store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : referenceNodesStore middle nextAccepted tail target nodes suffix=
          referenceNodesStore store accepted tail target (node::nodes) suffix:=by
        funext r
        by_cases r1 : r=1 <;> by_cases r27 : r=27 <;> by_cases r28 : r=28 <;>
          simp [referenceNodesStore,noTableReference,middle,referenceNodeStore,consumed,nextAccepted,
            r1,r27,r28,Bool.and_assoc]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 28=store 28:=by simp [consumed]
        rw [inputSame] at bodyBound
        have remainingLength : (middle 28).length≤(store 28).length:=by
          rw [input]
          simp only [middle,referenceNodeStore,Function.update_of_ne (by decide : (28:Fin 35)≠1),Function.update_self]
          simp only [remaining,Encoding.sequence,List.length_append]
          omega
        have tailLimit : tailTime≤nodes.length*(2200*((store 28).length+target.size+1)^3+2)+1:=by
          apply tailBound.trans;gcongr
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.DagValidation
