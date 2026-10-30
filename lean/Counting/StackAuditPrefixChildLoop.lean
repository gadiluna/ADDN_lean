import Counting.StackAuditPrefixChildItem
import Counting.AuditPrefixChildRange

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

abbrev childLoop : Routine 50 := forEach 44 childItem

def childLoopResult (store : Store 50) (vista : Executable.Vista) (level start count : Nat)
    (present unique : Bool) (tailPresent tailUnique : List Bool) : Store 50 :=
  Function.update (Function.update (Function.update
    (childSelectedResult store present unique tailPresent tailUnique (childRange vista level start count))
      32 (start+count+1).bits) 36 (List.replicate count true++store 36)) 44 []

/-- Scan a genuine finite interval of candidate parents. Both conjunctions
are accumulated even after a failure, and both index representations are
advanced by real instructions. No local label is expanded into unary. -/
theorem childLoop_executes (store : Store 50) (vista : Executable.Vista)
    (start level : Nat) (bits : List Bool) (inside : start+bits.length≤vista.nodes.size)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (indexAt : (store 36).length=start) (parentAt : store 32=(start+1).bits)
    (levelAt : store 41=level.bits) (childAt : store 30=(level+1).bits) (counter : store 44=bits)
    (present unique : Bool) (tailPresent tailUnique : List Bool)
    (presentAt : store 42=present::tailPresent) (uniqueAt : store 43=unique::tailUnique) :
    ∃ time ≤ bits.length*(1400000*((store 17).length+level.size+(level+1).size+1)^5+2)+1,
      Executes childLoop store time
        (childLoopResult store vista level start bits.length present unique tailPresent tailUnique) := by
  induction bits generalizing store start present unique with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (44:Fin 52) childItem store counter
    have final : childLoopResult store vista level start 0 present unique tailPresent tailUnique=store := by
      simp only [childLoopResult,childRange_zero,childSelectedResult,Bool.and_true,
        List.replicate_zero,List.nil_append,Nat.add_zero]
      rw [←presentAt,Function.update_eq_self,←uniqueAt,Function.update_eq_self,
        ←parentAt,Function.update_eq_self,Function.update_eq_self,←counter,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 44 bits
    have validIndex:start<vista.nodes.size := by simp only [List.length_cons] at inside;omega
    let index:Fin vista.nodes.size:=⟨start,validIndex⟩
    have consumedWork (r:Fin 52) (small:r.val<17) (different:r≠1) : consumed r=[] := by
      have n44:r≠44 := by intro same;subst r;norm_num at small
      simp [consumed,n44,work r small different]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=childItem_executes consumed vista index level
      accepted tail (by simp [consumed,status]) consumedWork
      (by simp [consumed,e18]) (by simp [consumed,e19]) (by simp [consumed,e28]) (by simp [consumed,e29])
      (by simp [consumed,e31]) (by simp [consumed,e33]) (by simp [consumed,e34]) (by simp [consumed,e35])
      suffix (by simp [consumed,source]) (by simp [consumed,nodeCount])
      (by simpa [consumed,index] using indexAt) (by simp [consumed,index,parentAt])
      (by simp [consumed,levelAt]) (by simp [consumed,childAt]) present unique tailPresent tailUnique
      (by simp [consumed,presentAt]) (by simp [consumed,uniqueAt])
    let predicates:=childPredicates vista level start
    let middle:=childItemResult consumed start present unique tailPresent tailUnique predicates
    have bodyResult : bodyFinish.store=middle := bodyStore
    have middleWork (r:Fin 52) (small:r.val<17) (different:r≠1) : middle r=[] := by
      have n32:r≠32 := by intro same;subst r;norm_num at small
      have n36:r≠36 := by intro same;subst r;norm_num at small
      have n42:r≠42 := by intro same;subst r;norm_num at small
      have n43:r≠43 := by intro same;subst r;norm_num at small
      simp [middle,childItemResult,childSelectedResult,n32,n36,n42,n43,consumedWork r small different]
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih middle (start+1)
      (by simp only [List.length_cons] at inside;omega)
      (by simp [middle,childItemResult,childSelectedResult,consumed,status]) middleWork
      (by simp [middle,childItemResult,childSelectedResult,consumed,e18])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e19])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e28])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e29])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e31])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e33])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e34])
      (by simp [middle,childItemResult,childSelectedResult,consumed,e35])
      (by simp [middle,childItemResult,childSelectedResult,consumed,source])
      (by simp [middle,childItemResult,childSelectedResult,consumed,nodeCount])
      (by simp [middle,childItemResult,consumed,indexAt])
      (by simp [middle,childItemResult])
      (by simp [middle,childItemResult,childSelectedResult,consumed,levelAt])
      (by simp [middle,childItemResult,childSelectedResult,consumed,childAt])
      (by simp [middle,childItemResult,childSelectedResult,consumed])
      (present && predicates.1) (unique && predicates.2)
      (by simp [middle,childItemResult,childSelectedResult])
      (by simp [middle,childItemResult,childSelectedResult])
    have first:=repeat_iteration (44:Fin 52) childItem store bit bits counter bodyTime bodyFinish bodyRun bodyHalt
    have final : childLoopResult middle vista level (start+1) bits.length
        (present && predicates.1) (unique && predicates.2) tailPresent tailUnique=
        childLoopResult store vista level start (bit::bits).length present unique tailPresent tailUnique := by
      funext r
      by_cases a:r=32 <;> by_cases b:r=36 <;> by_cases c:r=42 <;> by_cases d:r=43 <;> by_cases e:r=44 <;>
        simp [childLoopResult,childSelectedResult,middle,childItemResult,consumed,childRange_succ,predicates,
          a,b,c,d,e,Bool.and_assoc,List.replicate_succ',List.append_assoc,Nat.add_comm,Nat.add_left_comm]
    have tableSame : (middle 17).length=(store 17).length := by
      simp [middle,childItemResult,childSelectedResult,consumed]
    rw [tableSame] at tailBound
    let S:=(store 17).length+level.size+(level+1).size+1
    have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
    have nodesBound : vista.nodes.size≤(store 17).length := by
      rw [source,List.length_append];simp only [Array.length_toList] at nodes;omega
    have indexSize : (start+1).size≤(store 17).length :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have bodyLimit : bodyTime≤1400000*S^5 := by
      have base : (consumed 17).length+level.size+(level+1).size+(index.val+1).size+1≤2*S := by
        simp only [consumed,Function.update_of_ne (by decide : (17:Fin 52)≠44),index]
        dsimp only [S];omega
      have raised:=bodyBound.trans (Nat.mul_le_mul_left 41000 (Nat.pow_le_pow_left base 5))
      have power : 41000*(2*S)^5=1312000*S^5 := by ring
      rw [power] at raised
      omega
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · simp only [List.length_cons]
      change bodyTime+2+tailTime≤(bits.length+1)*(1400000*S^5+2)+1
      change tailTime≤bits.length*(1400000*S^5+2)+1 at tailBound
      nlinarith only [bodyLimit,tailBound]
    · change Machine.run (step (forEach 44 childItem).program) (bodyTime+2+tailTime) ⟨0,store⟩=some tailFinish
      rw [Machine.run_add,first,Option.bind_some,bodyResult]
      exact tailRun

end Counting.StackMachine.AuditPrefix
