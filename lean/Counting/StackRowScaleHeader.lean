import Counting.StackRowScaleLoop
import Counting.StackEncodingListHeader

namespace Counting.StackMachine.RowScale
open Routine EncodingPrograms

def headerRoles : FullListWorkspace 15 := ⟨![1,28,4,6,3,5,14,15,7,16,17,8,9,10,11,12,13],by decide⟩
abbrev readHeader : Routine 30 := listHeaderRoutine 15 headerRoles

theorem fields_count_le (row : List Rat) : row.length ≤
    (Encoding.sequence (Encoding.framed Encoding.rational) row).length := by
  induction row with
  | nil => rfl
  | cons value rest ih =>
    simp only [Encoding.sequence,List.length_append,List.length_cons,Encoding.framed_length]
    omega

theorem header_parsed (row : List Rat) (suffix : List Bool) :
    Encoding.unframe (Encoding.rationalRow.encode row++suffix) =
      some (row.length.bits,Encoding.sequence (Encoding.framed Encoding.rational) row++suffix) := by
  change Encoding.unframe ((Encoding.frame row.length.bits++Encoding.sequence (Encoding.framed Encoding.rational) row)++suffix)=_
  rw [List.append_assoc,Encoding.unframe_frame]

theorem header_count (row : List Rat) (suffix : List Bool) :
    listCount (Encoding.rationalRow.encode row++suffix)=row.length := by
  simp only [listCount,unframePayload,unframeSuffix,header_parsed,Option.map_some,Option.getD_some]
  rw [countRun_natural _ _ _ (by omega),Nat.zero_add,Nat.min_eq_right]
  have bound := fields_count_le row
  simp only [List.length_append]
  omega

theorem header_accepted (row : List Rat) (suffix : List Bool) :
    listHeaderAccepted (Encoding.rationalRow.encode row++suffix)=true := by
  simp only [listHeaderAccepted,header_parsed,unframePayload,header_count,
    Option.isSome_some,Option.map_some,Option.getD_some]
  simp [Encoding.natural]

theorem readHeader_executes (factor : List Bool) (row : List Rat) (suffix : List Bool) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode row++suffix).length+1)^3,
      Executes readHeader (file factor (Encoding.rationalRow.encode row++suffix) [] [] [] [] [] [] []) time
        (file factor (Encoding.sequence (Encoding.framed Encoding.rational) row++suffix) []
          (List.replicate row.length true) [] [] (Encoding.natural.encode row.length) [true] []) := by
  let store := file factor (Encoding.rationalRow.encode row++suffix) [] [] [] [] [] [] []
  have empty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) : store (headerRoles i)=[] := by
    fin_cases i <;> simp_all [store,file,headerRoles]
  obtain ⟨time,bounded,ran⟩ := listHeader_executes 15 headerRoles store empty
  have result : listHeaderStore 15 headerRoles store =
      file factor (Encoding.sequence (Encoding.framed Encoding.rational) row++suffix) []
        (List.replicate row.length true) [] [] (Encoding.natural.encode row.length) [true] [] := by
    funext r; fin_cases r <;> simp [listHeaderStore,store,headerRoles,file,header_count,header_accepted,
      unframeSuffix,unframePayload,header_parsed,Encoding.natural]
  rw [result] at ran
  exact ⟨time,bounded,ran⟩

end Counting.StackMachine.RowScale
