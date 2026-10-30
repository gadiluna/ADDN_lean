import Counting.AuditPrefixScanState
import Counting.StackAuditPrefixSaveConditional

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

abbrev prefixRound : Routine 50 := sequence widthGuard
  (sequence childAll (sequence (mergeFlag 42 1) (sequence saveIfFlat advanceLevel)))

/-- One physical prefix round checks the next level's width, scans every
current parent, updates the running status, saves the latest flat level,
and advances both binary level queries. -/
theorem prefixRound_executes (vista : Executable.Vista) (valid : vista.valid=true)
    (leaders candidate last level : Nat) (within : level≤(vista.node vista.bottom).level)
    (remaining : List Bool) (accepted : Bool) (anchor : Option Nat) :
    ∃ time ≤ 3000000*((Encoding.sequence Encoding.node vista.nodes.toList++
      Encoding.natural.encode vista.bottom).length+level.size+(level+1).size+
        candidate.size+(anchorCode anchor).size+1)^6,
      Executes prefixRound (roundFile vista leaders candidate last level remaining accepted anchor) time
        (roundFile vista leaders candidate last (level+1) remaining
          (accepted && roundCheck vista candidate level) (nextAnchor vista level anchor)) := by
  let initial:=roundFile vista leaders candidate last level remaining accepted anchor
  have initialWork (r:Fin 52) (small:r.val<17) (different:r≠1) : initial r=[] := by
    fin_cases r <;> simp_all [initial,roundFile,openingFile,tableFile,inputFile]
  obtain ⟨widthTime,widthBound,a⟩:=widthGuard_executes initial vista (level+1) candidate accepted []
    (by simp [initial,roundFile]) initialWork
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [initial,roundFile,openingFile,tableFile,inputFile])
    (Encoding.natural.encode vista.bottom) (by simp [initial,roundFile,openingFile,tableFile])
    (by simp [initial,roundFile,openingFile,tableFile])
    (by simp [initial,roundFile]) (by simp [initial,roundFile])
  let widthOK:=decide ((Executable.levelNodes vista (level+1)).length≤candidate)
  let checked:=Function.update initial 1 [accepted && widthOK]
  have checkedWork (r:Fin 52) (small:r.val<17) (different:r≠1) : checked r=[] := by
    simp [checked,different,initialWork r small different]
  obtain ⟨childTime,childBound,b⟩:=childAll_executes checked vista level (accepted && widthOK) []
    (by simp [checked]) checkedWork
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile,inputFile])
    (Encoding.natural.encode vista.bottom) (by simp [checked,initial,roundFile,openingFile,tableFile])
    (by simp [checked,initial,roundFile,openingFile,tableFile])
    (by simp [checked,initial,roundFile]) (by simp [checked,initial,roundFile])
  have empty42 : checked 42=[] := by simp [checked,initial,roundFile,openingFile,tableFile,inputFile]
  have empty43 : checked 43=[] := by simp [checked,initial,roundFile,openingFile,tableFile,inputFile]
  rw [empty42,empty43,childRange_present,childRange_flat vista valid level within] at b
  let scanned:=Function.update (Function.update checked 42 [childrenPresent vista level])
    43 [Executable.flat vista (level+1)]
  have c:=mergeFlag_executes 42 1 (by decide) (by decide) (by decide) scanned
    (by simp [scanned,checked,initialWork]) (childrenPresent vista level) (accepted && widthOK) []
    (by simp [scanned]) (by simp [scanned,checked])
  let combined:=Function.update (Function.update scanned 42 []) 1
    [(accepted && widthOK) && childrenPresent vista level]
  obtain ⟨saveTime,saveBound,d⟩:=saveIfFlat_executes combined (level+1)
    (Executable.flat vista (level+1)) (by simp [combined,scanned,checked,initial,roundFile])
    (by simp [combined,scanned,checked,initialWork]) (by simp [combined,scanned,checked,initialWork])
    (by simp [combined,scanned])
  let saved:=Function.update (Function.update combined 43 []) 46
    (if Executable.flat vista (level+1) then (level+1+1).bits else combined 46)
  obtain ⟨advanceTime,advanceBound,e⟩:=advanceLevel_executes saved level
    (by simp [saved,combined,scanned,checked,initial,roundFile])
    (by simp [saved,combined,scanned,checked,initial,roundFile])
    (by simp [saved,combined,scanned,checked,initialWork])
    (by simp [saved,combined,scanned,checked,initialWork])
  have final : Function.update (Function.update saved 41 (level+1).bits) 30 (level+1+1).bits=
      roundFile vista leaders candidate last (level+1) remaining
        (accepted && roundCheck vista candidate level) (nextAnchor vista level anchor) := by
    funext r
    fin_cases r <;> simp [saved,combined,scanned,checked,initial,roundFile,openingFile,
      tableFile,inputFile,roundCheck,widthOK,Bool.and_assoc,nextAnchor,anchorCode]
    split <;> simp_all
  rw [final] at e
  let table:=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  have initialTable : initial 17=table := by simp [initial,roundFile,openingFile,tableFile,table]
  have checkedTable : checked 17=table := by simp [checked,initialTable]
  have oldAnchor : (combined 46).length=(anchorCode anchor).size := by
    simp [combined,scanned,checked,initial,roundFile,Encoding.bits_length]
  rw [initialTable] at widthBound
  rw [checkedTable] at childBound
  rw [oldAnchor] at saveBound
  let S:=table.length+level.size+(level+1).size+candidate.size+(anchorCode anchor).size+1
  have positive : 1≤S := by dsimp only [S];omega
  have linear : S≤S^6:=Nat.le_self_pow (by decide) _
  have one : 1≤S^6:=Nat.one_le_pow _ _ positive
  have widthLimit : widthTime≤31000*S^6:=widthBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [S];omega) 5).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have childLimit : childTime≤2000000*S^6:=childBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 6))
  have levelSize : level.size≤S := by dsimp only [S];omega
  have childSize : (level+1).size≤S := by dsimp only [S];omega
  have anchorSize : (anchorCode anchor).size≤S := by dsimp only [S];omega
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  change widthTime+1+(childTime+1+(14+1+(saveTime+1+advanceTime)))≤3000000*S^6
  omega

end Counting.StackMachine.AuditPrefix
