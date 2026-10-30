import Counting.StackGaussianNormalColumns
import Counting.StackGaussianNormalHeaders
import Counting.StackGaussianPivotHeader

namespace Counting.StackMachine.GaussianNormal
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def inputWord (width : Nat) (matrix : List (List Rat)) : List Bool :=
  Encoding.frame (List.replicate width true)++Encoding.rationalMatrix.encode matrix

def inputBank (input matrix width count first second rows rowHeader matrixHeader : List Bool) : Fin 53 → List Bool :=
  fun r => if r=0 then input else if r=36 then matrix else if r=37 then count
    else if r=38 then first else if r=39 then second else if r=44 then width else if r=46 then rows
    else if r=49 then rowHeader else if r=50 then matrixHeader else []

def countRoles : Fin 31 ↪ Fin 53 :=
  ⟨![36,38,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,37,30],by decide⟩
abbrev parseInput : Routine 51 := sequence (move 50 0 36 52) (ofProgram (unframeProgram 50 36 44 52))
abbrev readCount : Routine 51 := relocate GaussianPivot.readCount countRoles
abbrev seedIndices : Routine 51 := sequence (ofProgram (ListPrograms.copyProgram 50 44 46 52))
  (sequence (pushBit 38 true) (pushBit 39 true))
abbrev prepareInput : Routine 51 := sequence parseInput (sequence readCount (sequence seedIndices emitHeaders))

theorem parseInput_executes (width : Nat) (matrix : List (List Rat)) :
    Executes parseInput (inputBank (inputWord width matrix) [] [] [] [] [] [] [] [])
      (6*(inputWord width matrix).length+5*width+7)
      (inputBank [] (Encoding.rationalMatrix.encode matrix) (List.replicate width true) [] [] [] [] [] []) := by
  let initial := inputBank (inputWord width matrix) [] [] [] [] [] [] [] []
  let moved := inputBank [] (inputWord width matrix) [] [] [] [] [] [] []
  have a := move_executes 50 (0 : Fin 53) 36 52 (by decide) (by decide) (by decide) initial rfl
  have aStore : Function.update (Function.update initial 36 (inputWord width matrix++[])) 0 []=moved := by
    funext r;fin_cases r <;> simp [initial,moved,inputBank]
  change Executes _ initial (6*(inputWord width matrix).length+4)
    (Function.update (Function.update initial 36 (inputWord width matrix++[])) 0 []) at a
  rw [aStore] at a
  have b := unframe_canonical_executes 50 (36 : Fin 53) 44 52 (by decide) (by decide) (by decide) moved
    (List.replicate width true) (Encoding.rationalMatrix.encode matrix) rfl rfl
  have bStore : Function.update (Function.update moved 36 (Encoding.rationalMatrix.encode matrix)) 44 (List.replicate width true++[])=
      inputBank [] (Encoding.rationalMatrix.encode matrix) (List.replicate width true) [] [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [moved,inputBank]
  change Executes _ moved (5*(List.replicate width true).length+2)
    (Function.update (Function.update moved 36 (Encoding.rationalMatrix.encode matrix)) 44 (List.replicate width true++[])) at b
  rw [bStore] at b
  simp only [List.length_replicate] at b
  convert a.sequence b using 1
  omega

theorem readCount_executes (width : List Bool) (matrix : List (List Rat)) :
    ∃ time ≤ 1900*((Encoding.rationalMatrix.encode matrix).length+1)^3,
      Executes readCount (inputBank [] (Encoding.rationalMatrix.encode matrix) width [] [] [] [] [] []) time
        (inputBank [] (Encoding.rationalMatrix.encode matrix) width (List.replicate matrix.length true) [] [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := GaussianPivot.readCount_executes matrix []
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame GaussianPivot.readCount countRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [inputBank,countRoles,GaussianPivot.file]
  · intro r;fin_cases r <;> simp [inputBank,countRoles,GaussianPivot.file]
  · intro r outside
    by_cases same : r=37
    · subst r;exact False.elim (outside 29 rfl)
    · simp [inputBank,same]

theorem seedIndices_executes (matrix width count : List Bool) :
    Executes seedIndices (inputBank [] matrix width count [] [] [] [] []) (5*width.length+6)
      (inputBank [] matrix width count [true] [true] width [] []) := by
  let initial := inputBank [] matrix width count [] [] [] [] []
  let copied := inputBank [] matrix width count [] [] width [] []
  let first := inputBank [] matrix width count [true] [] width [] []
  have a := copy_executes 50 (44 : Fin 53) 46 52 (by decide) (by decide) (by decide) initial rfl
  have aStore : Function.update initial 46 (width++[])=copied := by
    funext r;fin_cases r <;> simp [initial,copied,inputBank]
  change Executes _ initial (5*width.length+2) (Function.update initial 46 (width++[])) at a
  rw [aStore] at a
  have b := pushBit_executes (38 : Fin 53) true copied
  have bStore : Function.update copied 38 (true::copied 38)=first := by
    funext r;fin_cases r <;> simp [copied,first,inputBank]
  rw [bStore] at b
  have c := pushBit_executes (39 : Fin 53) true first
  have cStore : Function.update first 39 (true::first 39)=inputBank [] matrix width count [true] [true] width [] [] := by
    funext r;fin_cases r <;> simp [first,inputBank]
  rw [cStore] at c
  convert a.sequence (b.sequence c) using 1

/-- All unary counters and binary headers are computed by actual programs.
The width is explicit in unary on this internal solver input. -/
theorem prepareInput_executes (width : Nat) (equations : List Executable.Equation) :
    ∃ time ≤ 2200*((Encoding.rationalMatrix.encode (GaussianNormalMatrix.equationMatrix width equations)).length+2*width+3)^3,
      Executes prepareInput
        (inputBank (inputWord width (GaussianNormalMatrix.equationMatrix width equations)) [] [] [] [] [] [] [] []) time
        (state width equations 0 0 [] (List.replicate width true) [] [] []) := by
  let matrix := GaussianNormalMatrix.equationMatrix width equations
  let code := Encoding.rationalMatrix.encode matrix
  let unary := List.replicate width true
  let count := List.replicate matrix.length true
  let seeded := inputBank [] code unary count [true] [true] unary [] []
  have a := parseInput_executes width matrix
  obtain ⟨countTime,countBound,b⟩ := readCount_executes unary matrix
  have c := seedIndices_executes code unary count
  obtain ⟨headerTime,headerBound,d⟩ := emitHeaders_executes seeded rfl rfl rfl rfl rfl
  have final : Function.update (Function.update seeded 50 (Encoding.natural.encode (seeded 44).length))
      49 (Encoding.natural.encode ((seeded 44).length+1))=state width equations 0 0 [] unary [] [] [] := by
    funext r;fin_cases r <;> simp [seeded,inputBank,unary,count,matrix,code,state,outerBank,ready,bank]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  let size := code.length+2*width+3
  have inputLength : (inputWord width matrix).length=2*width+1+code.length := by
    simp [inputWord,Encoding.frame_length,code]
  change countTime ≤ 1900*(code.length+1)^3 at countBound
  change headerTime ≤ 50*(unary.length+2)^2 at headerBound
  simp only [unary,List.length_replicate] at headerBound ⊢
  have firstPower := Nat.pow_le_pow_left (show code.length+1≤ size by omega) 3
  have secondPower := Nat.pow_le_pow_left (show width+2≤ size by omega) 2
  have squares : size^2≤ size^3 := Nat.pow_le_pow_right (by omega) (by decide : 2≤3)
  have linear : size≤ size^3 := Nat.le_self_pow (by decide : 3≠0) size
  have positive : 1≤ size^3 := Nat.one_le_pow 3 size (by omega)
  change _ ≤ 2200*size^3
  rw [inputLength]
  omega

end Counting.StackMachine.GaussianNormal
