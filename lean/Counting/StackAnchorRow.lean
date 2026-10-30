import Counting.StackAnchorRowFinish

namespace Counting.StackMachine.AnchorRow
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev appendZero : Routine 38 := sequence (prepend 22 (Encoding.rational.encode 0)) emit
abbrev row : Routine 38 := sequence loop (sequence appendZero finish)

theorem appendZero_executes (input query anchor reversed width counter : List Bool) :
    Executes appendZero (file input query anchor [] [] reversed width counter []) 66
      (file input query anchor [] []
        ((Encoding.frame (Encoding.rational.encode 0)).reverse++reversed) (true::width) counter []) := by
  have a := prepend_executes (22:Fin 40) (Encoding.rational.encode 0)
    (file input query anchor [] [] reversed width counter [])
  let prepared := file input query anchor (Encoding.rational.encode 0) [] reversed width counter []
  have as' : Function.update (file input query anchor [] [] reversed width counter []) 22
      (Encoding.rational.encode 0++[])=prepared := by funext r;fin_cases r <;> simp [prepared,file]
  change Executes _ _ (2*(Encoding.rational.encode 0).length)
    (Function.update (file input query anchor [] [] reversed width counter []) 22
      (Encoding.rational.encode 0++[])) at a
  have zeroLength : (Encoding.rational.encode 0).length=5 := rfl
  rw [zeroLength] at a
  rw [as'] at a
  have b := emit_executes prepared rfl rfl
  have bs : Function.update (Function.update (Function.update prepared 22 []) 35
      ((Encoding.frame (prepared 22)).reverse++prepared 35)) 36 (true::prepared 36)=
      file input query anchor [] []
        ((Encoding.frame (Encoding.rational.encode 0)).reverse++reversed) (true::width) counter [] := by
    funext r;fin_cases r <;> simp [prepared,file]
  rw [bs] at b
  change Executes _ prepared (9*(Encoding.rational.encode 0).length+10) _ at b
  rw [zeroLength] at b
  exact a.sequence b

def rowBudget (nodes : List Executable.Node) (query anchor limit : Nat) : Nat :=
  nodes.length*(200000*(limit+query.size+anchor.size+1)^3+2)+1+1+
    (66+1+(4*((values nodes query anchor).length+1)*((values nodes query anchor).length+2)+
      17*((values nodes query anchor).length+1)+
      2*(Encoding.sequence (Encoding.framed Encoding.rational) (values nodes query anchor++[0])).length+20))

/-- A complete actual flow row: filter by binary level, compute every
selected coefficient, append its zero right-hand side, and encode the
row length. The only unary input is the explicit stored-node count. -/
theorem row_executes (nodes : List Executable.Node) (query anchor : Nat) (suffix : List Bool)
    (limit : Nat) (inputBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit) :
    ∃ time ≤ rowBudget nodes query anchor limit,
      Executes row
        (file (Encoding.sequence Encoding.node nodes++suffix) query.bits anchor.bits [] [] [] []
          (List.replicate nodes.length true) []) time
        (file suffix query.bits anchor.bits
          (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)) [] [] [] [] []) := by
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes nodes query anchor suffix [] [] limit inputBound
  simp only [List.append_nil] at loopRun
  let coefficients := values nodes query anchor
  let stream := Encoding.sequence (Encoding.framed Encoding.rational) (coefficients++[0])
  have zeroRun := appendZero_executes suffix query.bits anchor.bits
    (Encoding.sequence (Encoding.framed Encoding.rational) coefficients).reverse
    (List.replicate coefficients.length true) []
  let finished := file suffix query.bits anchor.bits [] [] stream.reverse
    (List.replicate (coefficients.length+1) true) [] []
  have zeroStore : file suffix query.bits anchor.bits [] []
      ((Encoding.frame (Encoding.rational.encode 0)).reverse++
        (Encoding.sequence (Encoding.framed Encoding.rational) coefficients).reverse)
      (true::List.replicate coefficients.length true) [] []=finished := by
    have append : Encoding.sequence (Encoding.framed Encoding.rational) (coefficients++[0])=
        Encoding.sequence (Encoding.framed Encoding.rational) coefficients++Encoding.frame (Encoding.rational.encode 0) := by
      induction coefficients with
      | nil => simp [Encoding.sequence,Encoding.framed]
      | cons value values ih => simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]
    simp only [finished,stream,append,List.reverse_append,List.replicate_succ]
  rw [zeroStore] at zeroRun
  obtain ⟨finishTime,finishBound,finishRun⟩ := finish_executes finished stream rfl rfl rfl rfl
  have finishStore : Function.update (Function.update (Function.update finished 36 []) 35 []) 22
      (Encoding.natural.encode (finished 36).length++stream)=
      file suffix query.bits anchor.bits
        (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)) [] [] [] [] [] := by
    have width : (finished 36).length=coefficients.length+1 := by simp [finished,file]
    rw [width]
    have code : Encoding.natural.encode (coefficients.length+1)++stream=
        Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query) := by
      simp [Encoding.rationalRow,Encoding.list,AnchorCoefficient.flowRow,coefficients,values,stream]
    rw [code]
    funext r;fin_cases r <;> simp [finished,file]
  rw [finishStore] at finishRun
  have composed := loopRun.sequence (zeroRun.sequence finishRun)
  refine ⟨loopTime+1+(66+1+finishTime),?_,composed⟩
  change finishTime ≤ 4*(List.replicate (coefficients.length+1) true).length*
    ((List.replicate (coefficients.length+1) true).length+1)+
    17*(List.replicate (coefficients.length+1) true).length+2*stream.length+20 at finishBound
  simp only [List.length_replicate] at finishBound
  dsimp only [rowBudget]
  dsimp only [coefficients,stream] at finishBound
  have assoc : (values nodes query anchor).length+1+1=(values nodes query anchor).length+2 := by omega
  rw [assoc] at finishBound
  omega

end Counting.StackMachine.AnchorRow
