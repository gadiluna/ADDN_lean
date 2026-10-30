import Counting.StackAnchorLeaderLoop
import Counting.StackAnchorRowFinish
import Counting.StackRationalBasic

namespace Counting.StackMachine.AnchorLeaderRow
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev appendLeaders : Routine 38 := sequence (RationalArithmetic.castNatural 37 21 22 39) AnchorRow.emit
abbrev row : Routine 38 := sequence loop (sequence appendLeaders AnchorRow.finish)

theorem appendLeaders_executes (input anchor reversed width counter : List Bool) (leaders : Nat) :
    ∃ time ≤ 23*leaders.size+69,
      Executes appendLeaders (file input leaders.bits anchor [] [] reversed width counter []) time
        (file input [] anchor [] []
          ((Encoding.frame (Encoding.rational.encode (leaders:Rat))).reverse++reversed) (true::width) counter []) := by
  let before := file input leaders.bits anchor [] [] reversed width counter []
  have a := RationalArithmetic.castNatural_executes 37 (21:Fin 40) 22 39 (by decide) (by decide) (by decide) before rfl
  let prepared := file input [] anchor (Encoding.rational.encode (leaders:Rat)) [] reversed width counter []
  have as' : Function.update (Function.update before 21 []) 22
      (Encoding.rational.encode (Encoding.value (before 21):Rat)++before 22)=prepared := by
    funext r;fin_cases r <;> simp [before,prepared,AnchorRow.file,Encoding.value_bits]
  rw [as'] at a
  change Executes _ before (Normalize.formatCost leaders.bits+9) prepared at a
  have b := AnchorRow.emit_executes prepared rfl rfl
  have bs : Function.update (Function.update (Function.update prepared 22 []) 35
      ((Encoding.frame (prepared 22)).reverse++prepared 35)) 36 (true::prepared 36)=
      file input [] anchor [] []
        ((Encoding.frame (Encoding.rational.encode (leaders:Rat))).reverse++reversed) (true::width) counter [] := by
    funext r;fin_cases r <;> simp [prepared,file,AnchorRow.file]
  rw [bs] at b
  change Executes _ prepared (9*(Encoding.rational.encode (leaders:Rat)).length+10) _ at b
  have composed := a.sequence b
  refine ⟨_,?_,composed⟩
  have cost := RationalArithmetic.castNatural_cost leaders.bits
  have length : (Encoding.rational.encode (leaders:Rat)).length=2*leaders.size+5 := by
    rw [RationalArithmetic.rational_nat_encode]
    simp only [List.length_cons,List.length_append,Encoding.natural_length]
    rfl
  rw [length,Encoding.bits_length] at *
  omega

def rowBudget (nodes : List Executable.Node) (leaders anchor limit : Nat) : Nat :=
  nodes.length*(200000*(limit+leaders.size+anchor.size+1)^3+2)+1+1+
    (23*leaders.size+69+1+(4*((values nodes leaders anchor).length+1)*((values nodes leaders anchor).length+2)+
      17*((values nodes leaders anchor).length+1)+
      2*(Encoding.sequence (Encoding.framed Encoding.rational) (values nodes leaders anchor++[(leaders:Rat)])).length+20))

/-- The final normalization equation has exactly the selected leader bits
and the supplied binary leader count as its right-hand side. -/
theorem row_executes (nodes : List Executable.Node) (leaders anchor : Nat) (suffix : List Bool)
    (limit : Nat) (inputBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit) :
    ∃ time ≤ rowBudget nodes leaders anchor limit,
      Executes row
        (file (Encoding.sequence Encoding.node nodes++suffix) leaders.bits anchor.bits [] [] [] []
          (List.replicate nodes.length true) []) time
        (file suffix [] anchor.bits
          (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)) [] [] [] [] []) := by
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes nodes leaders anchor suffix [] [] limit inputBound
  simp only [List.append_nil] at loopRun
  let coefficients := values nodes leaders anchor
  let stream := Encoding.sequence (Encoding.framed Encoding.rational) (coefficients++[(leaders:Rat)])
  obtain ⟨appendTime,appendBound,appendRun⟩ := appendLeaders_executes suffix anchor.bits
    (Encoding.sequence (Encoding.framed Encoding.rational) coefficients).reverse
    (List.replicate coefficients.length true) [] leaders
  let finished := file suffix [] anchor.bits [] [] stream.reverse
    (List.replicate (coefficients.length+1) true) [] []
  have appendStore : file suffix [] anchor.bits [] []
      ((Encoding.frame (Encoding.rational.encode (leaders:Rat))).reverse++
        (Encoding.sequence (Encoding.framed Encoding.rational) coefficients).reverse)
      (true::List.replicate coefficients.length true) [] []=finished := by
    have append : Encoding.sequence (Encoding.framed Encoding.rational) (coefficients++[(leaders:Rat)])=
        Encoding.sequence (Encoding.framed Encoding.rational) coefficients++Encoding.frame (Encoding.rational.encode (leaders:Rat)) := by
      induction coefficients with
      | nil => simp [Encoding.sequence,Encoding.framed]
      | cons value values ih => simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]
    simp only [finished,stream,append,List.reverse_append,List.replicate_succ]
  rw [appendStore] at appendRun
  obtain ⟨finishTime,finishBound,finishRun⟩ := AnchorRow.finish_executes finished stream rfl rfl rfl rfl
  have finishStore : Function.update (Function.update (Function.update finished 36 []) 35 []) 22
      (Encoding.natural.encode (finished 36).length++stream)=
      file suffix [] anchor.bits
        (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)) [] [] [] [] [] := by
    have width : (finished 36).length=coefficients.length+1 := by simp [finished,AnchorRow.file]
    rw [width]
    have code : Encoding.natural.encode (coefficients.length+1)++stream=
        Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders) := by
      simp [Encoding.rationalRow,Encoding.list,AnchorCoefficient.leaderRow,coefficients,values,stream]
      rfl
    rw [code]
    funext r;fin_cases r <;> simp [finished,file,AnchorRow.file]
  rw [finishStore] at finishRun
  have composed := loopRun.sequence (appendRun.sequence finishRun)
  refine ⟨loopTime+1+(appendTime+1+finishTime),?_,composed⟩
  change finishTime ≤ 4*(List.replicate (coefficients.length+1) true).length*
    ((List.replicate (coefficients.length+1) true).length+1)+
    17*(List.replicate (coefficients.length+1) true).length+2*stream.length+20 at finishBound
  simp only [List.length_replicate] at finishBound
  dsimp only [rowBudget]
  dsimp only [coefficients,stream] at finishBound
  have assoc : (values nodes leaders anchor).length+1+1=(values nodes leaders anchor).length+2 := by omega
  rw [assoc] at finishBound
  omega

end Counting.StackMachine.AnchorLeaderRow
