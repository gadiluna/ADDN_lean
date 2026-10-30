import Counting.StackAuditAscendStep

namespace Counting.StackMachine.AuditAscend
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev ascendLoop : Routine 30 := forEach 25 stepParent

def loopResult (store : Store 30) (vista : Executable.Vista) (steps code : Nat) : Store 30 :=
  Function.update (Function.update store 25 []) 24 (walkCode vista steps code).bits

/-- Every loop iteration performs the physical parent lookup, except that
None is retained. The explicit unary counter is consumed; the complete
table and all external registers survive. -/
theorem ascendLoop_executes (store : Store 30) (vista : Executable.Vista) (code : Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=code.bits)
    (empty : ∀ r : Fin 32,r.val≤28 → r≠17 → r≠24 → r≠25 → store r=[])
    (width : Nat) (codeWidth : code.size≤width) (tableWidth : (store 17).length≤width)
    (bits : List Bool) (counter : store 25=bits) :
    ∃ time ≤ bits.length*(5000000*((store 17).length+width+1)^4+2)+1,
      Executes ascendLoop store time (loopResult store vista bits.length code) := by
  induction bits generalizing store code with
  | nil =>
    obtain ⟨ran,halted⟩:=repeat_empty (25:Fin 32) stepParent store counter
    have final : loopResult store vista 0 code=store := by
      funext r
      by_cases a:r=24 <;> by_cases b:r=25 <;>
        simp [loopResult,walkCode,a,b,counter,current]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih =>
    let consumed:=Function.update store 25 bits
    have consumedEmpty (r : Fin 32) (small : r.val≤28) (n17 : r≠17) (n24 : r≠24) (n25 : r≠25) :
        consumed r=[] := by simp [consumed,n25,empty r small n17 n24 n25]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=
      stepParent_executes consumed vista code (by simp [consumed,source])
        (by simp [consumed,current]) consumedEmpty
    let next:=nextCode vista code
    let middle:=Function.update consumed 24 next.bits
    have middleEmpty (r : Fin 32) (small : r.val≤28) (n17 : r≠17) (n24 : r≠24) (n25 : r≠25) :
        middle r=[] := by simp [middle,n24,consumedEmpty r small n17 n24 n25]
    have nextWidth : next.size≤width := by
      have bound:=nextCode_size vista code
      rw [←source] at bound
      exact bound.trans tableWidth
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih middle next
      (by simp [middle,consumed,source]) (by simp [middle]) middleEmpty nextWidth
      (by simpa [middle,consumed] using tableWidth) (by simp [middle,consumed])
    have first:=repeat_iteration (25:Fin 32) stepParent store bit bits counter
      bodyTime bodyFinish bodyRun bodyHalt
    have final : loopResult middle vista bits.length next=loopResult store vista (bit::bits).length code := by
      funext r
      by_cases a:r=24 <;> by_cases b:r=25 <;>
        simp [loopResult,middle,consumed,walkCode,next,a,b]
    have bodyUniform : bodyTime≤5000000*((store 17).length+width+1)^4 := by
      change bodyTime≤5000000*((store 17).length+code.size+1)^4 at bodyBound
      exact bodyBound.trans (Nat.mul_le_mul_left 5000000 (Nat.pow_le_pow_left (by omega) 4))
    have sameLength : (middle 17).length=(store 17).length := by simp [middle,consumed]
    rw [sameLength] at tailBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · simp only [List.length_cons]
      nlinarith only [bodyUniform,tailBound]
    · rw [Machine.run_add,first,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.AuditAscend

