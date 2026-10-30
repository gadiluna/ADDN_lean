import Counting.StackGaussianPivotCorrectness
import Counting.StackEncodingListReadHeader
import Counting.StackRoutineLists

namespace Counting.StackMachine.GaussianPivot
open Routine EncodingPrograms

abbrev seed (matrix pivot counter : List Bool) : Fin 31 → List Bool :=
  file matrix pivot [] [] [] [] [] [] counter []

def headerRoles : FullListWorkspace 14 := ⟨![3,4,5,6,29,7,8,9,10,11,12,13,14,15,16,17,18],by decide⟩
abbrev copyMatrix : Routine 29 := ofProgram (ListPrograms.copyProgram 28 0 3 5)
abbrev parseHeader : Routine 29 := readListHeader 14 headerRoles
abbrev readCount : Routine 29 := sequence copyMatrix (sequence (pushBit 4 true)
  (sequence parseHeader (sequence (clear 3) (clear 4))))

/-- Read the row count from the actual binary matrix header. The matrix
itself survives, and the unary count is built by the bounded parser. -/
theorem readCount_executes (rows : List (List Rat)) (pivot : List Bool) :
    ∃ time ≤ 1900*((Encoding.rationalMatrix.encode rows).length+1)^3,
      Executes readCount (seed (Encoding.rationalMatrix.encode rows) pivot []) time
        (seed (Encoding.rationalMatrix.encode rows) pivot (List.replicate rows.length true)) := by
  let matrix := Encoding.rationalMatrix.encode rows
  let suffix := Encoding.sequence (Encoding.framed Encoding.rationalRow) rows
  let initial := seed matrix pivot []
  let copied := file matrix pivot [] matrix [] [] [] [] [] []
  let ready := file matrix pivot [] matrix [true] [] [] [] [] []
  let parsed := file matrix pivot [] suffix [true] [] [] [] (List.replicate rows.length true) []
  let erased := file matrix pivot [] [] [true] [] [] [] (List.replicate rows.length true) []
  have copy := copy_executes 28 (0 : Fin 31) 3 5 (by decide) (by decide) (by decide) initial rfl
  have copyResult : Function.update initial 3 (initial 0++initial 3)=copied := by
    funext r;fin_cases r <;> simp [initial,copied,file]
  change Executes _ initial (5*matrix.length+2) (Function.update initial 3 (initial 0++initial 3)) at copy
  rw [copyResult] at copy
  have status := pushBit_executes (4 : Fin 31) true copied
  have statusResult : Function.update copied 4 (true::copied 4)=ready := by
    funext r;fin_cases r <;> simp [copied,ready,file]
  rw [statusResult] at status
  have empty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) : ready (headerRoles i)=[] := by
    fin_cases i <;> simp_all [ready,headerRoles,file]
  obtain ⟨headerTime,headerBound,header⟩ := readListHeader_canonical 14 headerRoles ready true [] rfl empty
    (Encoding.framed Encoding.rationalRow) (by intro row;simp [Encoding.framed_length]) rows [] (by simp [ready,headerRoles,file,matrix,Encoding.rationalMatrix])
  have headerResult : Function.update (Function.update ready (headerRoles 0) (suffix++[]))
      (headerRoles 4) (List.replicate rows.length true)=parsed := by
    funext r;fin_cases r <;> simp [ready,parsed,headerRoles,file]
  rw [headerResult] at header
  have eraseSuffix := clear_executes (3 : Fin 31) parsed
  have eraseResult : Function.update parsed 3 []=erased := by
    funext r;fin_cases r <;> simp [parsed,erased,file]
  rw [eraseResult] at eraseSuffix
  have eraseStatus := clear_executes (4 : Fin 31) erased
  have final : Function.update erased 4 []=seed matrix pivot (List.replicate rows.length true) := by
    funext r;fin_cases r <;> simp [erased,file]
  rw [final] at eraseStatus
  change Executes _ parsed (suffix.length+1) erased at eraseSuffix
  change Executes _ erased 2 (seed matrix pivot (List.replicate rows.length true)) at eraseStatus
  refine ⟨5*matrix.length+2+1+(1+1+(headerTime+1+(suffix.length+1+1+2))),?_,
    copy.sequence (status.sequence (header.sequence (eraseSuffix.sequence eraseStatus)))⟩
  have suffixBound : suffix.length ≤ matrix.length := by
    change suffix.length≤(Encoding.frame rows.length.bits++suffix).length
    simp
  change headerTime≤1820*(matrix.length+1)^3 at headerBound
  have linear := Nat.le_self_pow (by decide : 3≠0) (matrix.length+1)
  change _ ≤1900*(matrix.length+1)^3
  omega

end Counting.StackMachine.GaussianPivot
