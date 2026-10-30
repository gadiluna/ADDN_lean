import Counting.StackAuditAscendBridge
import Counting.StackBinaryPredecessor
import Counting.StackEncodingFrameStore
import Counting.StackRoutineMove

namespace Counting.StackMachine.AuditAscend
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def stepPredRoles : Binary.PredWorkspace 24 := ⟨![24,27,0,1,2,3,4,5],by decide⟩
def parentBank : Fin 24 ↪ Fin 32 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun r : Fin 32=>r.val) same)⟩

def positiveStep : Routine 30 := sequence (Binary.predecessor 24 stepPredRoles)
  (sequence (frameRoutine 29 27 21 28)
    (sequence (relocate binaryParentAt parentBank)
      (sequence (clear 24) (sequence (move 29 2 24 28) (clear 21)))))

/-- One positive optional-index code is replaced by the physically read
parent code. The node table, unary step counter and external registers
survive; all predecessor, framing, lookup and cleanup steps are charged. -/
theorem positiveStep_executes (store : Store 30) (vista : Executable.Vista) (code : Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=code.bits) (nonzero : code≠0)
    (empty : ∀ r : Fin 32,r.val≤28 → r≠17 → r≠24 → r≠25 → store r=[]) :
    ∃ time ≤ 4000000*((store 17).length+code.size+1)^4,
      Executes positiveStep store time (Function.update store 24 (nextCode vista code).bits) := by
  obtain ⟨predTime,predBound,a⟩:=Binary.predecessor_executes 24 stepPredRoles store code
    (by simp [stepPredRoles,current]) (by
      intro i member;fin_cases i <;> simp_all [stepPredRoles])
  let previous:=Function.update store 27 (code-1).bits
  change Executes _ store predTime previous at a
  have b:=frame_executes_updates 29 (27:Fin 32) 21 28 (by decide) (by decide) (by decide) previous
    (by simp [previous,empty])
  let framed:=Function.update store 21 (Encoding.natural.encode (code-1))
  have framedResult : Function.update (Function.update previous 27 []) 21
      (Encoding.frame (previous 27)++previous 21)=framed := by
    funext r
    by_cases h:r=27 <;> by_cases j:r=21 <;>
      simp [previous,framed,h,j,empty,Encoding.natural]
  rw [framedResult] at b
  change Executes _ previous (5*(code-1).bits.length+4) framed at b
  let localStore : Store 22:=framed ∘ parentBank
  have localEmpty (r : Fin 24) (n17 : r≠17) (n21 : r≠21) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,framed,parentBank]
  obtain ⟨readTime,readBound,c⟩:=binaryParentAt_vista localStore vista (code-1)
    (by simp [localStore,framed,parentBank,source])
    (by simp [localStore,framed,parentBank]) localEmpty
  have outputEq : indexCode (vista.node (code-1)).parent=nextCode vista code := by
    rw [nextCode,if_neg nonzero]
  rw [outputEq] at c
  let found:=Function.update framed 2 (nextCode vista code).bits
  have reading : Executes (relocate binaryParentAt parentBank) framed readTime found := by
    apply relocate_executes_frame binaryParentAt parentBank framed found localStore _ readTime rfl _ _ c
    · intro r;fin_cases r <;> simp [found,localStore,parentBank]
    · intro r outside
      have n2 : r≠2 := by intro eq;subst r;exact outside 2 rfl
      simp [found,n2]
  have d:=clear_executes (24:Fin 32) found
  have oldAt : found 24=code.bits := by simp [found,framed,current]
  rw [oldAt] at d
  let cleared:=Function.update found 24 []
  have e:=move_executes 29 (2:Fin 32) 24 28 (by decide) (by decide) (by decide) cleared
    (by simp [cleared,found,framed,empty])
  have resultAt : cleared 2=(nextCode vista code).bits := by simp [cleared,found]
  have emptyAt : cleared 24=[] := by simp [cleared]
  rw [resultAt,emptyAt,List.append_nil] at e
  let moved:=Function.update (Function.update cleared 24 (nextCode vista code).bits) 2 []
  have f:=clear_executes (21:Fin 32) moved
  have queryAt : moved 21=Encoding.natural.encode (code-1) := by simp [moved,cleared,found,framed]
  rw [queryAt] at f
  have final : Function.update moved 21 []=Function.update store 24 (nextCode vista code).bits := by
    funext r
    by_cases a:r=2 <;> by_cases b:r=21 <;> by_cases c:r=24 <;>
      simp [moved,cleared,found,framed,a,b,c,empty]
  rw [final] at f
  have tableAt : localStore 17=store 17 := by simp [localStore,framed,parentBank]
  have queryLength : localStore 21=Encoding.natural.encode (code-1) := by simp [localStore,framed,parentBank]
  rw [tableAt,queryLength,Encoding.natural_length] at readBound
  have outputBound:=nextCode_size vista code
  rw [←source] at outputBound
  have predecessorBound : (code-1).size≤code.size := Nat.size_le_size (Nat.sub_le _ _)
  let K:=(store 17).length+code.size+1
  have factor : (store 17).length+(2*(code-1).size+1)+1≤2*K := by dsimp only [K];omega
  have raised:=readBound.trans (Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left factor 4))
  have positive : 1≤K := by dsimp only [K];omega
  have linear : K≤K^4 := Nat.le_self_pow (by decide) _
  have codeBound : code.size+1≤K := by dsimp only [K];omega
  have sourceBound : (store 17).length≤K := by dsimp only [K];omega
  refine ⟨_,?_,a.sequence (b.sequence (reading.sequence (d.sequence (e.sequence f))))⟩
  simp only [Encoding.bits_length,Encoding.natural_length]
  change _≤4000000*K^4
  nlinarith only [raised,predBound,outputBound,predecessorBound,codeBound,sourceBound,linear,positive]

end Counting.StackMachine.AuditAscend

