import Counting.StackDagReferenceTarget

/-! Reuse the complete canonical node scan to extract its following suffix.
The temporary reference predicate is discarded, restoring the caller status.
The original source and unary node count are preserved. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def referenceReadSuffix : Routine 33:=sequence (pushBit 1 true)
  (sequence (ofProgram (ListPrograms.copyProgram 32 17 28 2))
    (sequence (ofProgram (ListPrograms.copyProgram 32 25 27 2))
      (sequence (forEach 27 referenceNode) (dropFlag 33 1))))

theorem referenceReadSuffix_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,27,28,30,31}:Finset (Fin 35)) → store r=[])
    (target : Nat) (targetCode : store 26=target.bits) (targetPlus : store 24=(target+1).bits)
    (nodes : List Executable.Node) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node nodes++suffix) (count : (store 25).length=nodes.length) :
    ∃ time ≤ 2400*((store 17).length+target.size+1)^4,
      Executes referenceReadSuffix store time (Function.update store 28 suffix) := by
  have starting:=pushBit_executes (1:Fin 35) true store
  rw [status] at starting
  let initialized:=Function.update store 1 (true::accepted::tail)
  have copying:=copy_executes 32 17 28 2 (by decide) (by decide) (by decide) initialized
    (by simp [initialized,work])
  have sourceValue : initialized 17=store 17:=by simp [initialized]
  have emptyOutput : initialized 28=[]:=by simp [initialized,extraWork]
  rw [sourceValue,emptyOutput,List.append_nil] at copying
  let copied:=Function.update initialized 28 (store 17)
  have counting:=copy_executes 32 25 27 2 (by decide) (by decide) (by decide) copied
    (by simp [copied,initialized,work])
  have countValue : copied 25=store 25:=by simp [copied,initialized]
  have emptyCounter : copied 27=[]:=by simp [copied,initialized,extraWork]
  rw [countValue,emptyCounter,List.append_nil,count] at counting
  let ready:=Function.update copied 27 (store 25)
  have readyWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : ready r=[]:=by
    have n27 : r≠27:=by intro eq;subst r;norm_num at small
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    simp [ready,copied,initialized,ne,n27,n28,work r small ne]
  have readyExtra (r : Fin 35) (member : r∈({21,22,23,30,31}:Finset (Fin 35))) : ready r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    all_goals simp [ready,copied,initialized,extraWork]
  obtain ⟨loopTime,loopBound,loopRun⟩:=referenceNodes_executes ready true (accepted::tail)
    (by simp [ready,copied,initialized]) readyWork readyExtra target
    (by simp [ready,copied,initialized,targetCode]) (by simp [ready,copied,initialized,targetPlus]) nodes suffix
    (by simp [ready,copied,source]) (store 25) (by simp [ready]) count
  let checked:=referenceNodesStore ready true (accepted::tail) target nodes suffix
  have checkedFlag : checked 1=noTableReference target nodes::accepted::tail:=by simp [checked,referenceNodesStore]
  have dropping:=dropFlag_executes 33 1 checked (noTableReference target nodes) (accepted::tail) checkedFlag
  have final : Function.update checked 1 (accepted::tail)=Function.update store 28 suffix:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r27 : r=27 <;> by_cases r28 : r=28 <;>
      simp [checked,referenceNodesStore,ready,copied,initialized,r1,r27,r28,extraWork,status]
  rw [final] at dropping
  have nodesBound : nodes.length≤(store 17).length:=by
    have bounded:=node_sequence_count_le nodes
    rw [source,List.length_append]
    omega
  have inputSame : ready 28=store 17:=by simp [ready,copied]
  rw [inputSame] at loopBound
  let S:=(store 17).length+target.size+1
  have spos : 1≤S:=by dsimp only [S];omega
  have nodesS : nodes.length≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤2200*S^4+2*S+1:=by
    have bounded : loopTime≤S*(2200*S^3+2)+1:=loopBound.trans (by gcongr)
    nlinarith [show S*S^3=S^4 by ring]
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  have one : 1≤S^4:=Nat.one_le_pow _ _ spos
  refine ⟨_,?_,starting.sequence (copying.sequence (counting.sequence (loopRun.sequence
    dropping)))⟩
  change _≤2400*S^4
  dsimp only [S] at *
  omega

end Counting.StackMachine.DagValidation
