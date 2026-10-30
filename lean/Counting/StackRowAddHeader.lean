import Counting.StackRowAddLoop
import Counting.StackRowScaleHeader

namespace Counting.StackMachine.RowAdd
open Routine EncodingPrograms

def headerRoles : FullListWorkspace 19 := ⟨![0,32,4,6,3,5,14,15,7,16,17,8,9,10,11,12,13],by decide⟩
abbrev readLeftHeader : Routine 34 := listHeaderRoutine 19 headerRoles
abbrev dropRightHeader : Routine 34 := sequence (ofProgram (unframeProgram 33 1 33 7)) (clear 33)
abbrev readHeaders : Routine 34 := sequence readLeftHeader dropRightHeader

theorem readLeftHeader_executes (left : List Rat) (leftSuffix right : List Bool) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode left++leftSuffix).length+1)^3,
      Executes readLeftHeader (file (Encoding.rationalRow.encode left++leftSuffix) right [] [] [] [] [] [] [] [] []) time
        (file (Encoding.sequence (Encoding.framed Encoding.rational) left++leftSuffix) right []
          (List.replicate left.length true) [] [] [] [] (Encoding.natural.encode left.length) [true] []) := by
  let store := file (Encoding.rationalRow.encode left++leftSuffix) right [] [] [] [] [] [] [] [] []
  have empty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) : store (headerRoles i)=[] := by
    fin_cases i <;> simp_all [store,file,headerRoles]
  obtain ⟨time,bounded,ran⟩ := listHeader_executes 19 headerRoles store empty
  have result : listHeaderStore 19 headerRoles store =
      file (Encoding.sequence (Encoding.framed Encoding.rational) left++leftSuffix) right []
        (List.replicate left.length true) [] [] [] [] (Encoding.natural.encode left.length) [true] [] := by
    funext r; fin_cases r <;> simp [listHeaderStore,store,headerRoles,file,RowScale.header_count,RowScale.header_accepted,
      unframeSuffix,unframePayload,RowScale.header_parsed,Encoding.natural]
  rw [result] at ran
  exact ⟨time,bounded,ran⟩

theorem dropRightHeader_executes (left : List Bool) (right : List Rat) (suffix counter header status : List Bool) :
    Executes dropRightHeader (file left (Encoding.rationalRow.encode right++suffix) [] counter [] [] [] [] header status [])
      (6*right.length.bits.length+4)
      (file left (Encoding.sequence (Encoding.framed Encoding.rational) right++suffix) [] counter [] [] [] [] header status []) := by
  let base := file left (Encoding.rationalRow.encode right++suffix) [] counter [] [] [] [] header status []
  let rest := Encoding.sequence (Encoding.framed Encoding.rational) right++suffix
  have start : unframeConfig 33 1 33 7 0 base (Encoding.frame right.length.bits++rest) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 33 1 33 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 36 => _) = base
    funext r; fin_cases r <;> simp [base,rest,file,Encoding.rationalRow,Encoding.list,Encoding.natural,List.append_assoc]
  have ran := unframe_frames 33 1 33 7 (by decide) (by decide) (by decide) base right.length.bits rest []
  rw [start] at ran
  have parsed : Executes (ofProgram (unframeProgram 33 1 33 7)) base (5*right.length.bits.length+2)
      (file left rest [] counter [] [] [] [] header status right.length.bits) := by
    refine ⟨unframeConfig 33 1 33 7 7 base rest (right.length.bits++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
    change (fun r : Fin 36 => _) = _
    funext r; fin_cases r <;> simp [unframeConfig,base,file]
  have cleared := clear_executes (registers:=34) 33 (file left rest [] counter [] [] [] [] header status right.length.bits)
  have clearedStore : Function.update (file left rest [] counter [] [] [] [] header status right.length.bits) 33 [] =
      file left rest [] counter [] [] [] [] header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 33) _ (right.length.bits.length+1)
    (Function.update (file left rest [] counter [] [] [] [] header status right.length.bits) 33 []) at cleared
  rw [clearedStore] at cleared
  have combined := parsed.sequence cleared
  change Executes dropRightHeader base (5*right.length.bits.length+2+1+(right.length.bits.length+1))
    (file left rest [] counter [] [] [] [] header status []) at combined
  convert combined using 1
  omega

theorem readHeaders_executes (pairs : List (Rat×Rat)) (leftSuffix rightSuffix : List Bool) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix).length+1)^3+
      6*pairs.length.bits.length+5,
      Executes readHeaders (file (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix)
        (Encoding.rationalRow.encode (pairs.map Prod.snd)++rightSuffix) [] [] [] [] [] [] [] [] []) time
        (file (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)++leftSuffix)
          (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.snd)++rightSuffix) []
          (List.replicate pairs.length true) [] [] [] [] (Encoding.natural.encode pairs.length) [true] []) := by
  obtain ⟨time,bounded,ran⟩ := readLeftHeader_executes (pairs.map Prod.fst) leftSuffix
    (Encoding.rationalRow.encode (pairs.map Prod.snd)++rightSuffix)
  have dropped := dropRightHeader_executes
    (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)++leftSuffix)
    (pairs.map Prod.snd) rightSuffix (List.replicate pairs.length true) (Encoding.natural.encode pairs.length) [true]
  simp only [List.length_map] at ran dropped
  exact ⟨_,by omega,ran.sequence dropped⟩

end Counting.StackMachine.RowAdd
