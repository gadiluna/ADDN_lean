import Counting.StackEncodingCountLoop
import Counting.StackEncodingCountReport

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def boundedCount (extra : Nat) (w : CountWorkspace extra) : Routine (extra+9) :=
  Routine.sequence (countLoop extra w) (countReport extra w)

def boundedCountResult (extra : Nat) (w : CountWorkspace extra)
    (base : Fin (extra+11) → List Bool) (header budget : List Bool) : Fin (extra+11) → List Bool :=
  Function.update (countState extra w base header (countRun header 0 budget.length) []) (w 6)
    (decide (Encoding.frame header=Encoding.natural.encode (countRun header 0 budget.length))::base (w 6))

/-- A concrete, total bounded binary-to-unary conversion. The explicit budget
is consumed, the result has at most its original length, and a status bit
reports whether the header was canonical and its value fitted in the budget.
The cubic bound depends on word lengths, never the encoded numeric value. -/
theorem boundedCount_executes (extra : Nat) (w : CountWorkspace extra)
    (base : Fin (extra+11) → List Bool) (header budget : List Bool)
    (empty : ∀ i : Fin 11, i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → base (w i)=[]) :
    ∃ time ≤ 64*(budget.length+(Encoding.frame header).length+1)^3,
      Routine.Executes (boundedCount extra w) (countState extra w base header 0 budget) time
        (boundedCountResult extra w base header budget) := by
  obtain ⟨loopTime,loopBound,loopRun⟩ := countLoop_executes extra w base header empty budget 0 budget.length (by omega)
  let result := countState extra w base header (countRun header 0 budget.length) []
  have work : ∀ i : Fin 11, i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → result (w i)=[] := by
    intro i member
    have not0 : i≠0 := by intro eq; subst i; exact (by decide : (0:Fin 11)∉({2,3,4,5,7,8,9}:Finset (Fin 11))) member
    have not1 : i≠1 := by intro eq; subst i; exact (by decide : (1:Fin 11)∉({2,3,4,5,7,8,9}:Finset (Fin 11))) member
    have not10 : i≠10 := by intro eq; subst i; exact (by decide : (10:Fin 11)∉({2,3,4,5,7,8,9}:Finset (Fin 11))) member
    simpa only [result,countState,w.injective.eq_iff,if_neg not0,if_neg not1,if_neg not10] using empty i member
  obtain ⟨reportTime,reportBound,reportRun⟩ := countReport_executes extra w result work
  have final : countReportResult extra w result=boundedCountResult extra w base header budget := by
    simp [countReportResult,result,countState,boundedCountResult,w.injective.eq_iff]
  rw [final] at reportRun
  refine ⟨loopTime+1+reportTime,?_,loopRun.sequence reportRun⟩
  have capped : countRun header 0 budget.length≤budget.length := by simpa using countRun_le header 0 budget.length
  have reportLimit : reportTime≤60*(budget.length+(Encoding.frame header).length+1)^2 := by
    have r0 : result (w 0)=Encoding.frame header := by simp [result,countState]
    have r1 : result (w 1)=List.replicate (countRun header 0 budget.length) true := by simp [result,countState,w.injective.eq_iff]
    rw [r0,r1,List.length_replicate] at reportBound
    exact reportBound.trans (by gcongr)
  have main := Nat.mul_le_mul_right (60*(budget.length+(Encoding.frame header).length+1)^2)
    (show budget.length+1≤budget.length+(Encoding.frame header).length+1 by omega)
  nlinarith [Nat.le_self_pow (by decide : 3≠0) (budget.length+(Encoding.frame header).length+1)]

theorem boundedCount_status (extra : Nat) (w : CountWorkspace extra)
    (base : Fin (extra+11) → List Bool) (header budget : List Bool) :
    boundedCountResult extra w base header budget (w 6) =
      decide (∃ value≤budget.length,header=value.bits)::base (w 6) := by
  simp only [boundedCountResult,Function.update_self]
  congr 2
  apply propext
  rw [eq_comm,countLoop_final_accepted]

theorem boundedCount_unary_length (extra : Nat) (w : CountWorkspace extra)
    (base : Fin (extra+11) → List Bool) (header budget : List Bool) :
    (boundedCountResult extra w base header budget (w 1)).length≤budget.length := by
  simp only [boundedCountResult,Function.update_of_ne (fun same => (by decide : (1:Fin 11)≠6) (w.injective same))]
  simp only [countState,w.injective.eq_iff]
  simp only [show (1:Fin 11)≠0 by decide,if_false,ite_true,List.length_replicate]
  simpa using countRun_le header 0 budget.length

end Counting.StackMachine.EncodingPrograms
