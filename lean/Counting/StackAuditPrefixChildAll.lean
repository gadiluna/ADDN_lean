import Counting.StackAuditPrefixChildLoop

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

abbrev childAll : Routine 50 := sequence (ofProgram (ListPrograms.copyProgram 49 20 44 4))
  (sequence (pushBit 32 true)
    (sequence (pushBit 42 true)
      (sequence (pushBit 43 true)
        (sequence childLoop (sequence (clear 32) (clear 36))))))

/-- Prepare and consume the parent traversal from the actual persistent
node budget. Results are the full nonempty/singleton conjunctions, and both
temporary index representations are cleared. -/
theorem childAll_executes (store : Store 50) (vista : Executable.Vista)
    (level : Nat) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e32 : store 32=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (e36 : store 36=[]) (e44 : store 44=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (levelAt : store 41=level.bits) (childAt : store 30=(level+1).bits) :
    ∃ time ≤ 2000000*((store 17).length+level.size+(level+1).size+1)^6,
      Executes childAll store time
        (Function.update (Function.update store 42
          ((childRange vista level 0 vista.nodes.size).1::store 42)) 43
          ((childRange vista level 0 vista.nodes.size).2::store 43)) := by
  have a:=copy_executes 49 (20:Fin 52) 44 4 (by decide) (by decide) (by decide) store
    (work 4 (by decide) (by decide))
  rw [nodeCount,e44,List.append_nil,List.length_replicate] at a
  let copied:=Function.update store 44 (List.replicate vista.nodes.size true)
  have b:=pushBit_executes (32:Fin 52) true copied
  have empty32 : copied 32=[] := by simp [copied,e32]
  rw [empty32] at b
  let indexed:=Function.update copied 32 [true]
  have c:=pushBit_executes (42:Fin 52) true indexed
  let present:=Function.update indexed 42 (true::store 42)
  have presentAt : indexed 42=store 42 := by simp [indexed,copied]
  rw [presentAt] at c
  have d:=pushBit_executes (43:Fin 52) true present
  have uniqueAt : present 43=store 43 := by simp [present,indexed,copied]
  rw [uniqueAt] at d
  let ready:=Function.update present 43 (true::store 43)
  have readyWork (r:Fin 52) (small:r.val<17) (different:r≠1) : ready r=[] := by
    have n32:r≠32 := by intro same;subst r;norm_num at small
    have n42:r≠42 := by intro same;subst r;norm_num at small
    have n43:r≠43 := by intro same;subst r;norm_num at small
    have n44:r≠44 := by intro same;subst r;norm_num at small
    simp [ready,present,indexed,copied,n32,n42,n43,n44,work r small different]
  obtain ⟨loopTime,loopBound,e⟩:=childLoop_executes ready vista 0 level (List.replicate vista.nodes.size true)
    (by simp) accepted tail (by simp [ready,present,indexed,copied,status]) readyWork
    (by simp [ready,present,indexed,copied,e18]) (by simp [ready,present,indexed,copied,e19])
    (by simp [ready,present,indexed,copied,e28]) (by simp [ready,present,indexed,copied,e29])
    (by simp [ready,present,indexed,copied,e31]) (by simp [ready,present,indexed,copied,e33])
    (by simp [ready,present,indexed,copied,e34]) (by simp [ready,present,indexed,copied,e35])
    suffix (by simp [ready,present,indexed,copied,source])
    (by simp [ready,present,indexed,copied,nodeCount])
    (by simp [ready,present,indexed,copied,e36]) (by simp [ready,present,indexed,Nat.bits])
    (by simp [ready,present,indexed,copied,levelAt]) (by simp [ready,present,indexed,copied,childAt])
    (by simp [ready,present,indexed,copied]) true true (store 42) (store 43)
    (by simp [ready,present]) (by simp [ready])
  simp only [List.length_replicate] at e loopBound
  let scanned:=childLoopResult ready vista level 0 vista.nodes.size true true (store 42) (store 43)
  have f:=clear_executes (32:Fin 52) scanned
  have codeLength : (scanned 32).length=(vista.nodes.size+1).size := by
    simp [scanned,childLoopResult,Encoding.bits_length]
  rw [codeLength] at f
  let cleared:=Function.update scanned 32 []
  have g:=clear_executes (36:Fin 52) cleared
  have indexLength : (cleared 36).length=vista.nodes.size := by
    simp [cleared,scanned,childLoopResult,ready,present,indexed,copied,e36]
  rw [indexLength] at g
  have final : Function.update cleared 36 []=
      Function.update (Function.update store 42 ((childRange vista level 0 vista.nodes.size).1::store 42))
        43 ((childRange vista level 0 vista.nodes.size).2::store 43) := by
    funext r
    by_cases a:r=32 <;> by_cases b:r=36 <;> by_cases c:r=42 <;> by_cases d:r=43 <;> by_cases e:r=44 <;>
      simp [cleared,scanned,childLoopResult,childSelectedResult,ready,present,indexed,copied,a,b,c,d,e,e32,e36,e44]
  rw [final] at g
  have tableSame : (ready 17).length=(store 17).length := by simp [ready,present,indexed,copied]
  rw [tableSame] at loopBound
  let S:=(store 17).length+level.size+(level+1).size+1
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  have nodeBound : vista.nodes.size≤(store 17).length := by
    rw [source,List.length_append];simp only [Array.length_toList] at nodes;omega
  have countBound : vista.nodes.size≤S := by dsimp only [S];omega
  have codeBound : (vista.nodes.size+1).size≤S := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp only [S];omega)
  have multiplied:=Nat.mul_le_mul_right (1400000*S^5+2) countBound
  have power : S*S^5=S^6 := by ring
  have linear : S≤S^6:=Nat.le_self_pow (by decide) _
  have one : 1≤S^6:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change loopTime≤vista.nodes.size*(1400000*S^5+2)+1 at loopBound
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence g)))))⟩
  change 5*vista.nodes.size+2+1+(1+1+(1+1+(1+1+(loopTime+1+
    (((vista.nodes.size+1).size+1)+1+(vista.nodes.size+1))))))≤2000000*S^6
  nlinarith only [loopBound,multiplied,power,linear,one,countBound,codeBound]

end Counting.StackMachine.AuditPrefix
