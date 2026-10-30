import Counting.StackGaussianCheckLoop
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.GaussianCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def inputCodec : Encoding.Codec (List Rat×List (List Rat)) :=
  Encoding.product (Encoding.framed Encoding.rationalRow) Encoding.rationalMatrix
def headerRoles : FullListWorkspace 26 :=
  ⟨![36,39,3,4,38,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩
abbrev parseInput : Routine 41 := sequence (move 40 0 36 40)
  (ofProgram (unframeProgram 40 36 37 40))
abbrev readHeader : Routine 41 := sequence (pushBit 39 true) (readListHeader 26 headerRoles)
abbrev prepare : Routine 41 := sequence parseInput readHeader

theorem parseInput_executes (rows : List (List Rat)) (solution : List Rat) :
    Executes parseInput (file (inputCodec.encode (solution,rows)) [] [] [] [] [] [] [])
      (6*(inputCodec.encode (solution,rows)).length+5*(Encoding.rationalRow.encode solution).length+7)
      (file [] [] [] (Encoding.rationalMatrix.encode rows) (Encoding.rationalRow.encode solution) [] [] []) := by
  let initial := file (inputCodec.encode (solution,rows)) [] [] [] [] [] [] []
  let moved := file [] [] [] (inputCodec.encode (solution,rows)) [] [] [] []
  have a := move_executes 40 (0:Fin 43) 36 40 (by decide) (by decide) (by decide) initial rfl
  have movedStore : Function.update (Function.update initial 36 (initial 0++initial 36)) 0 []=moved := by
    funext r;fin_cases r <;> simp [initial,moved,file,RowAdd.file]
  rw [movedStore] at a
  change Executes _ initial (6*(inputCodec.encode (solution,rows)).length+4) moved at a
  have b := unframe_canonical_executes 40 (36:Fin 43) 37 40 (by decide) (by decide) (by decide) moved
    (Encoding.rationalRow.encode solution) (Encoding.rationalMatrix.encode rows) rfl rfl
  have stored : Function.update (Function.update moved 36 (Encoding.rationalMatrix.encode rows)) 37
      (Encoding.rationalRow.encode solution++[])=
      file [] [] [] (Encoding.rationalMatrix.encode rows) (Encoding.rationalRow.encode solution) [] [] [] := by
    funext r;fin_cases r <;> simp [moved,file,RowAdd.file]
  change Executes _ moved (5*(Encoding.rationalRow.encode solution).length+2)
    (Function.update (Function.update moved 36 (Encoding.rationalMatrix.encode rows)) 37
      (Encoding.rationalRow.encode solution++[])) at b
  rw [stored] at b
  convert a.sequence b using 1
  omega

theorem readHeader_executes (rows : List (List Rat)) (solution : List Rat) :
    ∃ time ≤ 1820*((Encoding.rationalMatrix.encode rows).length+1)^3+2,
      Executes readHeader
        (file [] [] [] (Encoding.rationalMatrix.encode rows) (Encoding.rationalRow.encode solution) [] [] []) time
        (file [] [] [] (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows)
          (Encoding.rationalRow.encode solution) (List.replicate rows.length true) [true] []) := by
  let initial := file [] [] [] (Encoding.rationalMatrix.encode rows) (Encoding.rationalRow.encode solution) [] [] []
  let seeded := file [] [] [] (Encoding.rationalMatrix.encode rows) (Encoding.rationalRow.encode solution) [] [true] []
  have a := pushBit_executes (39:Fin 43) true initial
  have pushed : Function.update initial 39 (true::initial 39)=seeded := by
    funext r;fin_cases r <;> simp [initial,seeded,file,RowAdd.file]
  rw [pushed] at a
  have empty (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      seeded (headerRoles i)=[] := by fin_cases i <;> simp_all [seeded,headerRoles,file,RowAdd.file]
  obtain ⟨headerTime,headerBound,b⟩ := readListHeader_canonical 26 headerRoles seeded true [] rfl empty
    (Encoding.framed Encoding.rationalRow) (by intro row;simp [Encoding.framed_length]) rows []
      (by simp [seeded,headerRoles,file,Encoding.rationalMatrix])
  have stored : Function.update (Function.update seeded (headerRoles 0)
      (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows++[])) (headerRoles 4)
        (List.replicate rows.length true)=
      file [] [] [] (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows)
        (Encoding.rationalRow.encode solution) (List.replicate rows.length true) [true] [] := by
    funext r;fin_cases r <;> simp [seeded,headerRoles,file,RowAdd.file]
  rw [stored] at b
  exact ⟨_,by change headerTime≤ 1820*((Encoding.rationalMatrix.encode rows).length+1)^3 at headerBound;omega,
    a.sequence b⟩

theorem prepare_executes (rows : List (List Rat)) (solution : List Rat) :
    ∃ time ≤ 1900*((inputCodec.encode (solution,rows)).length+1)^3,
      Executes prepare (file (inputCodec.encode (solution,rows)) [] [] [] [] [] [] []) time
        (file [] [] [] (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows)
          (Encoding.rationalRow.encode solution) (List.replicate rows.length true) [true] []) := by
  have a := parseInput_executes rows solution
  obtain ⟨headerTime,headerBound,b⟩ := readHeader_executes rows solution
  have length : (inputCodec.encode (solution,rows)).length=
      2*(Encoding.rationalRow.encode solution).length+1+(Encoding.rationalMatrix.encode rows).length := by
    change (Encoding.frame (Encoding.rationalRow.encode solution)++Encoding.rationalMatrix.encode rows).length=_
    simp [Encoding.frame_length]
  have power := Nat.pow_le_pow_left
    (show (Encoding.rationalMatrix.encode rows).length+1≤ (inputCodec.encode (solution,rows)).length+1 by omega) 3
  have linear := Nat.le_self_pow (by decide:3≠0) ((inputCodec.encode (solution,rows)).length+1)
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.GaussianCheck
