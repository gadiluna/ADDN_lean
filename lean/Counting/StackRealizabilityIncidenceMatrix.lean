import Counting.StackRealizabilityIncidenceOutside

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Tabulate both incidence matrices from a preserved serialized node sequence.
The supplied unary counter is the node count, and is extended by one outside
slot. The two completed row-major matrices are returned in registers 0 and 1. -/
def incidenceMatrix : Routine 44 := sequence (ofProgram (ListPrograms.copyProgram 43 42 44 0))
  (sequence (pushBit 42 false)
    (sequence (forEach 44 incidenceRow)
      (sequence (ofProgram (ListPrograms.copyProgram 43 42 43 0))
        (sequence (forEach 43 incidenceZeroPair)
          (sequence (ofProgram (ListPrograms.reverseProgram 44 22 0))
            (sequence (ofProgram (ListPrograms.reverseProgram 44 37 1)) (clear 36)))))))

theorem incidenceMatrix_executes (nodes : List Executable.Node) (source width : List Bool)
    (accepted : Bool) (tail suffix : List Bool)
    (input : source=Encoding.sequence Encoding.node nodes++suffix) (counted : width.length=nodes.length) :
    ∃ time ≤ 40000*(source.length+width.length+2)^8,
      Executes incidenceMatrix
        (incidenceTableFile source [] [] [] [] (accepted::tail) width [] []) time
        (Function.update (Function.update
          (incidenceTableFile source [] [] [] [] (accepted::tail) (false::width) [] [])
          0 (incomingMatrixValues nodes)) 1 (parentMatrixValues nodes)) := by
  let original := incidenceTableFile source [] [] [] [] (accepted::tail) width [] []
  have copying := copy_executes 43 42 44 0 (by decide) (by decide) (by decide) original
    (by simp [original,incidenceTableFile,incidenceFile])
  have a42 : original 42=width := by simp [original,incidenceTableFile]
  have a44 : original 44=[] := by simp [original,incidenceTableFile]
  rw [a42,a44,List.append_nil] at copying
  let copied := Function.update original 44 width
  have extending := pushBit_executes (42:Fin 46) false copied
  have c42 : copied 42=width := by simp [copied,a42]
  rw [c42] at extending
  have prepared : Function.update copied 42 (false::width)=
      incidenceTableFile source [] [] [] [] (accepted::tail) (false::width) [] width := by
    funext r
    fin_cases r <;> simp [copied,original,incidenceTableFile,incidenceFile]
  rw [prepared] at extending
  obtain ⟨rowTime,rowBound,rows⟩ := incidenceRows_executes source [] [] [] tail (false::width) width
    accepted [] nodes suffix (by simpa using input) rfl counted
  simp only [List.append_nil,List.length_cons,counted] at rows rowBound
  let scanned := incidenceTableFile source (List.replicate nodes.length true) []
    (incomingRows nodes (nodes.length+1)).reverse (parentRows nodes (nodes.length+1)).reverse
    (accepted::tail) (false::width) [] []
  have outsideCopy := copy_executes 43 42 43 0 (by decide) (by decide) (by decide) scanned
    (by simp [scanned,incidenceTableFile,incidenceFile])
  have s42 : scanned 42=false::width := by simp [scanned,incidenceTableFile]
  have s43 : scanned 43=[] := by simp [scanned,incidenceTableFile]
  rw [s42,s43,List.append_nil] at outsideCopy
  let ready := Function.update scanned 43 (false::width)
  have outside := incidenceOutside_executes ready (false::width) (by simp [ready])
  let completed := incidenceOutsideStore ready (false::width)
  have inAt : completed 22=(incomingMatrixValues nodes).reverse := by
    simp [completed,incidenceOutsideStore,ready,scanned,incidenceTableFile,incidenceFile,
      incomingMatrixValues,counted]
  have parentAt : completed 37=(parentMatrixValues nodes).reverse := by
    simp [completed,incidenceOutsideStore,ready,scanned,incidenceTableFile,incidenceFile,
      parentMatrixValues,counted]
  have zeroAt : completed 0=[] := by
    simp [completed,incidenceOutsideStore,ready,scanned,incidenceTableFile,incidenceFile]
  have reverseIncoming := reverse_executes 44 22 0 (by decide) completed
  rw [inAt,zeroAt,List.reverse_reverse,List.append_nil,List.length_reverse,incomingMatrixValues_length]
    at reverseIncoming
  let incomingDone := Function.update (Function.update completed 22 []) 0 (incomingMatrixValues nodes)
  have reverseParent := reverse_executes 44 37 1 (by decide) incomingDone
  have ip37 : incomingDone 37=(parentMatrixValues nodes).reverse := by simp [incomingDone,parentAt]
  have ip1 : incomingDone 1=[] := by
    simp [incomingDone,completed,incidenceOutsideStore,ready,scanned,incidenceTableFile,incidenceFile]
  rw [ip37,ip1,List.reverse_reverse,List.append_nil,List.length_reverse,parentMatrixValues_length]
    at reverseParent
  let matrices := Function.update (Function.update incomingDone 37 []) 1 (parentMatrixValues nodes)
  have clearing := clear_executes (36:Fin 46) matrices
  have atIndex : matrices 36=List.replicate nodes.length true := by
    simp [matrices,incomingDone,completed,incidenceOutsideStore,ready,scanned,incidenceTableFile,incidenceFile]
  rw [atIndex,List.length_replicate] at clearing
  have final : Function.update matrices 36 []=
      Function.update (Function.update
        (incidenceTableFile source [] [] [] [] (accepted::tail) (false::width) [] [])
        0 (incomingMatrixValues nodes)) 1 (parentMatrixValues nodes) := by
    funext r
    fin_cases r <;> simp [matrices,incomingDone,completed,incidenceOutsideStore,ready,scanned,
      incidenceTableFile,incidenceFile]
  rw [final] at clearing
  have execution := copying.sequence (extending.sequence (rows.sequence (outsideCopy.sequence
    (outside.sequence (reverseIncoming.sequence (reverseParent.sequence clearing))))))
  let S := source.length+width.length+2
  have nodeBound : nodes.length ≤ S := by dsimp only [S];omega
  have square : (nodes.length+1)^2 ≤ S^8 := by
    exact (Nat.pow_le_pow_left (by dsimp only [S];omega) 2).trans
      (Nat.pow_le_pow_right (by dsimp only [S];omega) (by decide))
  have rowLimit : rowTime ≤ 30000*S^7+2*S+1 := by
    have base : source.length+(nodes.length+1)+1=S := by dsimp only [S];omega
    rw [base] at rowBound
    apply rowBound.trans
    calc nodes.length*(30000*S^6+2)+1 ≤ S*(30000*S^6+2)+1 := by gcongr
         _ = _ := by ring
  have power : S^7 ≤ S^8 := Nat.pow_le_pow_right (by dsimp only [S];omega) (by decide)
  have linear : S ≤ S^8 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^8 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 40000*S^8;simp only [List.length_cons];omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
