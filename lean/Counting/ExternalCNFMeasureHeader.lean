import Counting.ExternalSATHeader
import Counting.ExternalSATClause

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536

/-- Read a list length into role 31, restoring the original encoded source.
The copied source and all header work are physically cleared. -/
def measureHeader (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 30) (w 3)))
    (sequence (readListHeader (extra+15) (satHeaderRoles extra w 1))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 24) (w 31) (w 3)))
        (sequence (clear (w 24))
          (sequence (clear (w 0))
            (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 30) (w 0) (w 3))) (clear (w 30)))))))

theorem measureHeader_executes {α : Type} (extra : Nat) (w : SATWorkspace extra)
    (codec : Encoding.Codec α) (positive : ∀ value,0<(codec.encode value).length)
    (values : List α) (suffix : List Bool) (store : Fin (extra+32) → List Bool)
    (accepted : Bool) (tail : List Bool)
    (source : store (w 0)=(Encoding.list codec).encode values++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈clauseScratch++[30],store (w i)=[]) :
    ∃ time ≤ 1900*((store (w 0)).length+1)^3,
      Executes (measureHeader extra w) store time
        (Function.update store (w 31) (List.replicate values.length true++store (w 31))) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let input := store (w 0)
  let copied := Function.update store (w 30) input
  have copying : Executes (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 30) (w 3)))
      store (5*input.length+2) copied := by
    simpa only [copied,input,empty 30 (by simp),List.append_nil] using
      copy_executes (extra+29) (w 0) (w 30) (w 3) (ne 0 30 (by decide)) (ne 0 3 (by decide))
        (ne 30 3 (by decide)) store (empty 3 (by simp [clauseScratch]))
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      copied ((satHeaderRoles extra w 1) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,copied,w.injective.eq_iff,empty,clauseScratch]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+15) (satHeaderRoles extra w 1)
    copied accepted tail (by change copied (w 1)=accepted::tail;simp [copied,w.injective.eq_iff,status])
    headerEmpty codec positive values suffix
    (by change copied (w 0)=(Encoding.list codec).encode values++suffix;simp [copied,w.injective.eq_iff,source])
  let rest := Encoding.sequence codec values++suffix
  let prepared := Function.update (Function.update copied (w 0) rest) (w 24) (List.replicate values.length true)
  change Executes (readListHeader (extra+15) (satHeaderRoles extra w 1)) copied headerTime prepared at headerRun
  have counting := copy_executes (extra+29) (w 24) (w 31) (w 3)
    (ne 24 31 (by decide)) (ne 24 3 (by decide)) (ne 31 3 (by decide)) prepared
    (by simp [prepared,copied,w.injective.eq_iff,empty,clauseScratch])
  have count : prepared (w 24)=List.replicate values.length true := by simp [prepared]
  have output : prepared (w 31)=store (w 31) := by simp [prepared,copied,w.injective.eq_iff]
  rw [count,output,List.length_replicate] at counting
  let counted := Function.update prepared (w 31) (List.replicate values.length true++store (w 31))
  have clearingCount := clear_executes (w 24) counted
  have countedCount : counted (w 24)=List.replicate values.length true := by simp [counted,prepared,w.injective.eq_iff]
  rw [countedCount,List.length_replicate] at clearingCount
  let clearedCount := Function.update counted (w 24) []
  have clearingSource := clear_executes (w 0) clearedCount
  have remaining : clearedCount (w 0)=rest := by simp [clearedCount,counted,prepared,w.injective.eq_iff]
  rw [remaining] at clearingSource
  let clearedSource := Function.update clearedCount (w 0) []
  have restoring := copy_executes (extra+29) (w 30) (w 0) (w 3)
    (ne 30 0 (by decide)) (ne 30 3 (by decide)) (ne 0 3 (by decide)) clearedSource
    (by simp [clearedSource,clearedCount,counted,prepared,copied,w.injective.eq_iff,empty,clauseScratch])
  have saved : clearedSource (w 30)=input := by
    simp [clearedSource,clearedCount,counted,prepared,copied,w.injective.eq_iff]
  have clearSource : clearedSource (w 0)=[] := by simp [clearedSource]
  rw [saved,clearSource,List.append_nil] at restoring
  let restored := Function.update clearedSource (w 0) input
  have clearingSaved := clear_executes (w 30) restored
  have stillSaved : restored (w 30)=input := by simp [restored,w.injective.eq_iff,saved]
  rw [stillSaved] at clearingSaved
  have finalStore : Function.update restored (w 30) []=
      Function.update store (w 31) (List.replicate values.length true++store (w 31)) := by
    funext r
    by_cases a : r=w 30
    · subst r;simp [w.injective.eq_iff,empty]
    · by_cases b : r=w 0
      · subst r;simp [restored,w.injective.eq_iff,input]
      · by_cases c : r=w 24
        · subst r;simp [restored,clearedSource,clearedCount,w.injective.eq_iff,empty,clauseScratch]
        · by_cases d : r=w 31
          · subst r;simp [restored,clearedSource,clearedCount,counted,w.injective.eq_iff]
          · simp [restored,clearedSource,clearedCount,counted,prepared,copied,a,b,c,d]
  rw [finalStore] at clearingSaved
  have combined := copying.sequence (headerRun.sequence (counting.sequence (clearingCount.sequence
    (clearingSource.sequence (restoring.sequence clearingSaved)))))
  refine ⟨5*input.length+2+1+(headerTime+1+(5*values.length+2+1+(values.length+1+1+
    (rest.length+1+1+(5*input.length+2+1+(input.length+1)))))),?_,combined⟩
  have restBound : rest.length≤ input.length := by
    dsimp [input];rw [source];simp only [Encoding.list,List.length_append];dsimp [rest];simp only [List.length_append];omega
  have countBound := VerifiedParser.sequence_count_le positive values
  have countLarge : values.length≤ input.length := by dsimp [rest] at restBound;simp only [List.length_append] at restBound;omega
  change headerTime≤1820*((copied (w 0)).length+1)^3 at headerBound
  have copiedInput : copied (w 0)=input := by simp [copied,w.injective.eq_iff,input]
  rw [copiedInput] at headerBound
  have linear : input.length+1≤(input.length+1)^3 := Nat.le_self_pow (by decide) _
  change _≤1900*(input.length+1)^3
  nlinarith only [headerBound,linear,restBound,countLarge]

end Counting.External.CNFMachine
