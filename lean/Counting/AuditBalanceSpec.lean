import Counting.RealizabilityVerifier

namespace Counting.Executable

def auditBalanceAt (vista : Vista) (weights : Array Nat) (round parent : Nat) : Bool :=
  decide (RealizabilityVerifier.demand vista weights round parent=
    RealizabilityVerifier.supply vista weights round parent)

def auditBalanceLevel (vista : Vista) (weights : Array Nat) (round : Nat) : Bool :=
  (List.range vista.nodes.size).all (fun parent=>
    if (vista.node parent).level=round then auditBalanceAt vista weights round parent else true)

def auditBalance (vista : Vista) (weights : Array Nat) (anchor : Nat) : Bool :=
  (List.range anchor).all (fun r=>r==0 || auditBalanceLevel vista weights (r-1))

theorem auditBalanceLevel_eq (vista : Vista) (weights : Array Nat) (round : Nat) :
    auditBalanceLevel vista weights round=
      (levelNodes vista round).all (auditBalanceAt vista weights round) := by
  simp only [auditBalanceLevel,levelNodes,List.all_filter]
  apply congrArg (fun predicate : Nat → Bool=>(List.range vista.nodes.size).all predicate)
  funext parent
  by_cases selected : (vista.node parent).level=round <;> simp [selected]

theorem auditBalanceAt_eq (vista : Vista) (weights : Array Nat) (round parent : Nat) :
    auditBalanceAt vista weights round parent=
      (((levelNodes vista (round+1)).map (fun v=>
        countFrom (vista.node v) parent*(weights[v]?.getD 0))).sum ==
      ((children vista parent (round+1)).map (fun v=>
        (vista.node v).degree*(weights[v]?.getD 0))).sum) := by
  apply Bool.eq_iff_iff.mpr
  simp only [auditBalanceAt,RealizabilityVerifier.demand,RealizabilityVerifier.supply,
    RealizabilityVerifier.weight,Nat.mul_comm,beq_iff_eq,decide_eq_true_eq]

/-- The finite index scans match the literal balance checks in `auditSuffix?`. -/
theorem auditBalance_eq (vista : Vista) (weights : Array Nat) (anchor : Nat) :
    auditBalance vista weights anchor=
      (List.range anchor).all (fun r=>r==0 ||
        (levelNodes vista (r-1)).all (fun parent=>
          ((levelNodes vista r).map (fun v=>
            countFrom (vista.node v) parent*(weights[v]?.getD 0))).sum ==
          ((children vista parent r).map (fun v=>
            (vista.node v).degree*(weights[v]?.getD 0))).sum)) := by
  unfold auditBalance
  apply congrArg (fun predicate : Nat → Bool=>(List.range anchor).all predicate)
  funext r
  by_cases zero : r=0
  · simp [zero]
  · rw [auditBalanceLevel_eq]
    have successor : r-1+1=r := by omega
    apply congrArg (fun predicate : Nat → Bool=>r==0 || (levelNodes vista (r-1)).all predicate)
    funext parent
    rw [auditBalanceAt_eq,successor]

end Counting.Executable
