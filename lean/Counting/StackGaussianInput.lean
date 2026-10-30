import Counting.StackGaussianOuter
import Counting.StackGaussianPivotHeader

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def inputFile (input matrix pivot dimension active : List Bool) : Fin 53 → List Bool :=
  fun r => if r=0 then input else if r=37 then matrix else if r=42 then pivot
    else if r=43 then dimension else if r=45 then active else []

def dimensionRoles : Fin 31 ↪ Fin 53 :=
  ⟨![37,42,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,43,30],by decide⟩

abbrev readDimension : Routine 51 := relocate GaussianPivot.readCount dimensionRoles
abbrev prepareInput : Routine 51 := sequence (move 50 0 37 1)
  (sequence (pushBit 42 true) (sequence (pushBit 45 true) readDimension))
abbrev generateInput : Routine 51 := sequence prepareInput generate

/-- The unary dimension is read from the actual canonical binary header;
it is never supplied to the program as an external parameter. -/
theorem readDimension_executes (rows : List (List Rat)) :
    ∃ time ≤ 1900*((Encoding.rationalMatrix.encode rows).length+1)^3,
      Executes readDimension (inputFile [] (Encoding.rationalMatrix.encode rows) [true] [] [true]) time
        (inputFile [] (Encoding.rationalMatrix.encode rows) [true] (List.replicate rows.length true) [true]) := by
  obtain ⟨time,bounded,ran⟩ := GaussianPivot.readCount_executes rows [true]
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame GaussianPivot.readCount dimensionRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [inputFile,dimensionRoles,GaussianPivot.file]
  · intro r;fin_cases r <;> simp [inputFile,dimensionRoles,GaussianPivot.file]
  · intro r outside
    by_cases same : r=43
    · subst r;exact False.elim (outside 29 rfl)
    · simp [inputFile,same]

theorem prepareInput_executes (rows : List (List Rat)) :
    ∃ time ≤ 2000*((Encoding.rationalMatrix.encode rows).length+1)^3,
      Executes prepareInput (inputFile (Encoding.rationalMatrix.encode rows) [] [] [] []) time
        (inputFile [] (Encoding.rationalMatrix.encode rows) [true] (List.replicate rows.length true) [true]) := by
  let matrix := Encoding.rationalMatrix.encode rows
  let initial := inputFile matrix [] [] [] []
  let moved := inputFile [] matrix [] [] []
  let positioned := inputFile [] matrix [true] [] []
  let activated := inputFile [] matrix [true] [] [true]
  have a := move_executes 50 (0 : Fin 53) 37 1 (by decide) (by decide) (by decide) initial rfl
  have aStore : Function.update (Function.update initial 37 (initial 0++initial 37)) 0 []=moved := by
    funext r;fin_cases r <;> simp [initial,moved,inputFile]
  rw [aStore] at a
  change Executes _ initial (6*matrix.length+4) moved at a
  have b := pushBit_executes (42 : Fin 53) true moved
  have bStore : Function.update moved 42 (true::moved 42)=positioned := by
    funext r;fin_cases r <;> simp [moved,positioned,inputFile]
  rw [bStore] at b
  have c := pushBit_executes (45 : Fin 53) true positioned
  have cStore : Function.update positioned 45 (true::positioned 45)=activated := by
    funext r;fin_cases r <;> simp [positioned,activated,inputFile]
  rw [cStore] at c
  obtain ⟨countTime,countBound,counted⟩ := readDimension_executes rows
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence counted))⟩
  have linear := Nat.le_self_pow (by decide : 3≠0) (matrix.length+1)
  change countTime ≤ 1900*(matrix.length+1)^3 at countBound
  change _≤2000*(matrix.length+1)^3
  omega

theorem inputFile_initial {q : Nat} (system : RationalSystem q) :
    inputFile [] (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system))
      [true] (List.replicate q true) [true]=outerStore ⟨system,[],true⟩ 0 [] := by
  funext r;fin_cases r <;>
    simp [inputFile,outerStore,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,
      Encoding.gaussianOpsRev,Encoding.sequence]

/-- Execution from the ordinary single input register, with every other
register initially empty. Its final bank stores exactly the original
materialized generator result, including the reverse transcript. -/
theorem generateInput_executes {q : Nat} (system : RationalSystem q) :
    ∃ time ≤ 2000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)^3+
        1+(5*q+3+pivotsCost 0 q ⟨system,[],true⟩),
      Executes generateInput
        (inputFile (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] [] [] []) time
        (outerStore (StoredGaussian.runGaussian system) q []) := by
  obtain ⟨prepareTime,prepareBound,prepared⟩ := prepareInput_executes (StoredGaussian.augmentedMatrix system)
  rw [StoredGaussian.augmentedMatrix_length,inputFile_initial] at prepared
  obtain ⟨generateTime,generateBound,generated⟩ := generate_executes system
  exact ⟨_,by omega,prepared.sequence generated⟩

end Counting.StackMachine.GaussianBank
