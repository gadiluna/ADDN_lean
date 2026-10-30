import Counting.StackAuditDescendantLevel
import Counting.StackAuditDescendantAncestor
import Counting.StackEncodingBranch

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def rejectLevel : Routine 38 := sequence (clear 24)
  (sequence (clear 25) (pushBit 35 false))

theorem rejectLevel_executes (store : Store 38) :
    Executes rejectLevel store ((store 24).length+(store 25).length+5)
      (Function.update (Function.update (Function.update store 25 []) 24 []) 35
        (false::store 35)) := by
  have a:=clear_executes (24:Fin 40) store
  have b:=clear_executes (25:Fin 40) (Function.update store 24 [])
  have c:=pushBit_executes (35:Fin 40) false
    (Function.update (Function.update store 24 []) 25 [])
  have same : Function.update (Function.update store 24 []) 25 []=
      Function.update (Function.update store 25 []) 24 [] := by
    funext r
    by_cases a:r=24 <;> by_cases b:r=25 <;> simp [a,b]
  have combined:=a.sequence (b.sequence c)
  simp only [Function.update_of_ne (by decide : (25:Fin 40)≠24),
    Function.update_of_ne (by decide : (35:Fin 40)≠24),
    Function.update_of_ne (by decide : (35:Fin 40)≠25),same] at combined
  convert combined using 1 <;> first | rfl | omega

/-- The selected node contributes exactly when its level and its actual
ancestor both match. Both branches consume the supplied lookup counters. -/
def selected : Routine 38 := sequence levelTest (branchRoutine 35 runAncestor rejectLevel)

theorem selected_executes (store : Store 38) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (last ancestor : Nat) (bits : List Bool)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (indexAt : (store 18).length=index.val) (lastAt : store 34=last.bits)
    (current : store 24=(index.val+1).bits) (target : store 29=(ancestor+1).bits)
    (counter : store 25=bits)
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → r≠18 → r≠24 → r≠25 → store r=[]) :
    ∃ time ≤ 400000000*((store 17).length+(index.val+1).size+
        bits.length+(ancestor+1).size+last.size+1)^5,
      Executes selected store time
        (Function.update (Function.update (Function.update (Function.update store 18 []) 25 []) 24 []) 35
          (Executable.descendantSelected vista bits.length last ancestor index.val::store 35)) := by
  obtain ⟨levelTime,levelBound,a⟩:=levelTest_executes store vista index last source indexAt lastAt empty
  let noIndex:=Function.update store 18 []
  let checked:=Function.update noIndex 35 (decide ((vista.node index.val).level=last)::store 35)
  have popped : Function.update checked 35 (store 35)=noIndex := by
    simp [checked,noIndex]
  have clean (r : Fin 40) (small : r.val ≤ 28) (n17 : r≠17) (n24 : r≠24) (n25 : r≠25) :
      noIndex r=[] := by
    by_cases n18:r=18
    · simp [noIndex,n18]
    · simp [noIndex,n18,empty r small n17 n18 n24 n25]
  let K:=(store 17).length+(index.val+1).size+bits.length+(ancestor+1).size+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have one : 1 ≤ K^5:=Nat.one_le_pow _ _ positive
  have linear : K ≤ K^5:=Nat.le_self_pow (by decide) _
  have levelLimit : levelTime ≤ 9000*K^5 := levelBound.trans
    (Nat.mul_le_mul_left 9000 ((Nat.pow_le_pow_left (by dsimp only [K];omega) 4).trans
      (Nat.pow_le_pow_right positive (by decide))))
  by_cases same : (vista.node index.val).level=last
  · obtain ⟨ancestorTime,ancestorBound,b⟩:=runAncestor_executes noIndex vista index.val ancestor bits
      (by simp [noIndex,source]) (by simp [noIndex,current]) (by simp [noIndex,target])
      (by simp [noIndex,counter]) clean
    have branch:=branch_executes_true (35:Fin 40) runAncestor rejectLevel checked _ (store 35) ancestorTime
      (by simp [checked,same]) (by rw [popped];exact b)
    have combined:=a.sequence branch
    have ancestorLimit : ancestorTime ≤ 200000000*K^5 := ancestorBound.trans
      (Nat.mul_le_mul_left 200000000 (Nat.pow_le_pow_left (by simp only [noIndex,Function.update_of_ne (by decide : (17:Fin 40)≠18)];dsimp only [K];omega) 5))
    refine ⟨levelTime+1+(1+ancestorTime),?_,?_⟩
    · change levelTime+1+(1+ancestorTime) ≤ 400000000*K^5
      omega
    · simpa [selected,noIndex,Executable.descendantSelected,same] using combined
  · have b:=rejectLevel_executes noIndex
    have branch:=branch_executes_false (35:Fin 40) runAncestor rejectLevel checked _ (store 35)
      ((noIndex 24).length+(noIndex 25).length+5)
      (by simp [checked,same]) (by rw [popped];exact b)
    have combined:=a.sequence branch
    have small : (noIndex 24).length+(noIndex 25).length ≤ K := by
      simp only [noIndex,Function.update_of_ne (by decide : (24:Fin 40)≠18),
        Function.update_of_ne (by decide : (25:Fin 40)≠18),current,counter,Encoding.bits_length]
      dsimp only [K];omega
    refine ⟨levelTime+1+(1+((noIndex 24).length+(noIndex 25).length+5)),?_,?_⟩
    · change levelTime+1+(1+((noIndex 24).length+(noIndex 25).length+5)) ≤ 400000000*K^5
      omega
    · simpa [selected,noIndex,Executable.descendantSelected,same] using combined

end Counting.StackMachine.AuditDescendant
