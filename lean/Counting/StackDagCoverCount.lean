import Counting.StackDagCoverLoop
import Counting.StackDagReadSuffix
import Counting.StackDagBottomCheck
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def coverFromCount : Routine 33:=sequence (pushBit 24 true)
  (sequence (ofProgram (ListPrograms.copyProgram 32 25 34 2))
    (sequence (discardBit 34) (sequence (forEach 34 coverStep)
      (sequence referenceReadSuffix (sequence bottomCheck
        (sequence (emptyFlag 25 1) (sequence (negateFlag 33 1)
          (sequence (ofProgram (combineFlagsProgram 33 1)) (sequence (clear 24) (clear 26))))))))))

def coverCheck (nodes : List Executable.Node) (bottom : Nat) : Bool:=
  bottom+1==nodes.length && coverRange nodes 0 (nodes.length-1)

theorem cover_check_flags (nodes : List Executable.Node) (bottom : Nat) :
    ((coverRange nodes 0 (nodes.length-1) && decide (bottom=nodes.length-1)) &&
      !decide (nodes.length=0))=coverCheck nodes bottom:=by
  apply Bool.eq_iff_iff.mpr
  simp only [coverCheck,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not,beq_iff_eq]
  constructor
  · rintro ⟨⟨covered,last⟩,nonempty⟩
    exact ⟨by omega,covered⟩
  · rintro ⟨last,covered⟩
    exact ⟨⟨covered,by omega⟩,by omega⟩

theorem coverFromCount_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,24,26,27,28,30,31,34}:Finset (Fin 35)) → store r=[])
    (nodes : List Executable.Node) (bottom : Nat)
    (source : store 17=Encoding.sequence Encoding.node nodes++Encoding.natural.encode bottom)
    (nodeCount : (store 25).length=nodes.length) :
    ∃ time ≤ 100000*((store 17).length+1)^5,
      Executes coverFromCount store time (Function.update store 1 ((accepted && coverCheck nodes bottom)::tail)) := by
  have starting:=pushBit_executes (24:Fin 35) true store
  rw [extraWork 24 (by decide)] at starting
  let initialized:=Function.update store 24 [true]
  have copying:=copy_executes 32 25 34 2 (by decide) (by decide) (by decide) initialized
    (by simp [initialized,work])
  have sourceCount : initialized 25=store 25:=by simp [initialized]
  have counterEmpty : initialized 34=[]:=by simp [initialized,extraWork]
  rw [sourceCount,counterEmpty,List.append_nil,nodeCount] at copying
  let copied:=Function.update initialized 34 (store 25)
  have discarding:=discardBit_executes (34:Fin 35) copied
  have copiedCounter : copied 34=store 25:=by simp [copied]
  rw [copiedCounter] at discarding
  let ready:=Function.update copied 34 (store 25).tail
  have readyWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : ready r=[]:=by
    have n24 : r≠24:=by intro eq;subst r;norm_num at small
    have n34 : r≠34:=by intro eq;subst r;norm_num at small
    simp [ready,copied,initialized,n24,n34,work r small ne]
  have readyExtra (r : Fin 35) (member : r∈({21,22,23,27,28,30,31}:Finset (Fin 35))) : ready r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [ready,copied,initialized,extraWork]
  obtain ⟨loopTime,loopBound,loopRun⟩:=coverLoop_executes ready accepted tail
    (by simp [ready,copied,initialized,status]) readyWork readyExtra nodes 0 (nodes.length-1)
    (by omega) (Encoding.natural.encode bottom) (by simp [ready,copied,initialized,source])
    (by simp [ready,copied,initialized,extraWork]) (by simp [ready,copied,initialized])
    (by simp [ready,copied,initialized,nodeCount]) (store 25).tail (by simp [ready])
    (by simp [List.length_tail,nodeCount])
  let scanned:=coverLoopStore ready accepted tail nodes 0 (nodes.length-1)
  let covered:=accepted && coverRange nodes 0 (nodes.length-1)
  have scannedStatus : scanned 1=covered::tail:=by simp [scanned,coverLoopStore,covered]
  have scannedWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : scanned r=[]:=by
    have n24 : r≠24:=by intro eq;subst r;norm_num at small
    have n26 : r≠26:=by intro eq;subst r;norm_num at small
    have n34 : r≠34:=by intro eq;subst r;norm_num at small
    simp [scanned,coverLoopStore,ne,n24,n26,n34,readyWork r small ne]
  have scannedExtra (r : Fin 35) (member : r∈({21,22,23,27,28,30,31}:Finset (Fin 35))) : scanned r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [scanned,coverLoopStore,ready,copied,initialized,extraWork]
  have scannedSource : scanned 17=store 17:=by simp [scanned,coverLoopStore,ready,copied,initialized]
  have scannedCount : scanned 25=store 25:=by simp [scanned,coverLoopStore,ready,copied,initialized]
  have scannedTarget : scanned 26=(nodes.length-1).bits:=by simp [scanned,coverLoopStore]
  have scannedPlus : scanned 24=(nodes.length-1+1).bits:=by simp [scanned,coverLoopStore]
  obtain ⟨readTime,readBound,reading⟩:=referenceReadSuffix_executes scanned covered tail scannedStatus scannedWork scannedExtra
    (nodes.length-1) scannedTarget scannedPlus nodes (Encoding.natural.encode bottom)
    (scannedSource.trans source) (by rw [scannedCount];exact nodeCount)
  let selected:=Function.update scanned 28 (Encoding.natural.encode bottom)
  obtain ⟨bottomTime,bottomBound,bottomRun⟩:=bottomCheck_executes selected covered tail
    (by simp [selected,scannedStatus]) (by simp [selected,scannedWork]) (by simp [selected,scannedWork])
    (by simp [selected,scannedWork]) (by simp [selected,scannedExtra])
    (nodes.length-1) bottom (by simp [selected,scannedTarget]) [] (by simp [selected])
  let checked:=Function.update (Function.update selected 28 []) 1
    ((covered && decide (bottom=nodes.length-1))::tail)
  let lastAccepted:=covered && decide (bottom=nodes.length-1)
  have emptyTest:=emptyFlag_executes (25:Fin 35) 1 checked
  have countValue : checked 25=store 25:=by simp [checked,selected,scannedCount]
  have statusValue : checked 1=lastAccepted::tail:=by simp [checked,lastAccepted]
  rw [countValue,statusValue] at emptyTest
  have emptyIff : store 25=[] ↔ nodes.length=0:=by rw [←List.length_eq_zero_iff,nodeCount]
  simp only [emptyIff] at emptyTest
  let tested:=Function.update checked 1 (decide (nodes.length=0)::lastAccepted::tail)
  have negating:=negateFlag_executes 33 1 tested (decide (nodes.length=0)) (lastAccepted::tail) (by simp [tested])
  let negated:=Function.update tested 1 ((!decide (nodes.length=0))::lastAccepted::tail)
  have combining:=combineFlags_executes 33 1 negated lastAccepted (!decide (nodes.length=0)) tail (by simp [negated])
  have flagEqual : (lastAccepted && !decide (nodes.length=0))=(accepted && coverCheck nodes bottom):=by
    dsimp only [lastAccepted,covered]
    simpa only [Bool.and_assoc] using congrArg (fun b=>accepted && b) (cover_check_flags nodes bottom)
  rw [flagEqual] at combining
  let allChecked:=Function.update negated 1 ((accepted && coverCheck nodes bottom)::tail)
  have clearPlus:=clear_executes (24:Fin 35) allChecked
  have plusValue : allChecked 24=(nodes.length-1+1).bits:=by
    simp [allChecked,negated,tested,checked,selected,scannedPlus]
  rw [plusValue,Encoding.bits_length] at clearPlus
  let noPlus:=Function.update allChecked 24 []
  have clearTarget:=clear_executes (26:Fin 35) noPlus
  have targetValue : noPlus 26=(nodes.length-1).bits:=by
    simp [noPlus,allChecked,negated,tested,checked,selected,scannedTarget]
  rw [targetValue,Encoding.bits_length] at clearTarget
  have final : Function.update noPlus 26 []=Function.update store 1 ((accepted && coverCheck nodes bottom)::tail):=by
    funext r
    fin_cases r <;> simp [noPlus,allChecked,negated,tested,checked,selected,scanned,coverLoopStore,
      ready,copied,initialized,extraWork]
  rw [final] at clearTarget
  have nodeBound : nodes.length≤(store 17).length:=by
    have bounded:=node_sequence_count_le nodes
    rw [source,List.length_append]
    omega
  have bottomLength : (Encoding.natural.encode bottom).length≤(store 17).length:=by rw [source,List.length_append];omega
  have size : (nodes.length-1).size≤nodes.length-1:=Nat.size_le.mpr Nat.lt_two_pow_self
  have plusSize : (nodes.length-1+1).size≤nodes.length-1+1:=Nat.size_le.mpr Nat.lt_two_pow_self
  have loopSource : ready 17=store 17:=by simp [ready,copied,initialized]
  rw [loopSource] at loopBound
  rw [scannedSource] at readBound
  have bottomSource : selected 28=Encoding.natural.encode bottom:=by simp [selected]
  rw [bottomSource] at bottomBound
  let S:=(store 17).length+1
  have spos : 1≤S:=by dsimp only [S];omega
  have nodesS : nodes.length≤S:=by dsimp only [S];omega
  have base : (store 17).length+(nodes.length-1).size+1≤2*S:=by dsimp only [S];omega
  have loopLimit : loopTime≤42000*S^5+2*S+1:=by
    have upper : loopTime≤S*(42000*S^4+2)+1:=loopBound.trans (by gcongr;omega)
    nlinarith [show S*S^4=S^5 by ring]
  have readLimit : readTime≤38400*S^4:=by
    calc
      readTime≤2400*(2*S)^4:=readBound.trans (by gcongr)
      _=38400*S^4:=by ring
  have fourth : S^4≤S^5:=Nat.pow_le_pow_right spos (by decide)
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have one : 1≤S^5:=Nat.one_le_pow _ _ spos
  have emptyCost : emptyFlagCost (store 25)≤3:=by unfold emptyFlagCost;split <;> omega
  refine ⟨_,?_,starting.sequence (copying.sequence (discarding.sequence (loopRun.sequence
    (reading.sequence (bottomRun.sequence (emptyTest.sequence (negating.sequence
      (combining.sequence (clearPlus.sequence clearTarget)))))))))⟩
  change _≤100000*S^5
  dsimp only [S] at *
  omega

end Counting.StackMachine.DagValidation
