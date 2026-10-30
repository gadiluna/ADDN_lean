import Counting.StackProtocolAuditSpec

namespace Counting.StackMachine.ProtocolAudit

theorem answer_eq_scheduledPlan (vista : Executable.Vista) (leaders : Nat)
    (normal : ((vista.node vista.bottom).level == leaders &&
      !(Executable.levelNodes vista 0).any (fun i=>!(vista.node i).leader))=false) :
    answer vista leaders (vista.node vista.bottom).level=(Executable.scheduledPlan leaders vista).eval := by
  simp only [Executable.scheduledPlan,normal,Bool.false_eq_true,if_false]
  unfold answer
  cases chosen:Executable.candidateAt leaders (vista.node vista.bottom).level with
  | none=>rfl
  | some pair=>
    rcases pair with ⟨candidate,last⟩
    simp only [Option.bind_some,Executable.SolverPlan.eval_map]
    rfl

end Counting.StackMachine.ProtocolAudit
