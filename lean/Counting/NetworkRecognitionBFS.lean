import Counting.NetworkRecognitionBitGraph
import Counting.StackRealizabilityReachCheck

namespace Counting.StackMachine.NetworkRecognition
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

/-- Materialize the all-active mask by copying the explicit unary width,
run the proved bit-matrix BFS, and erase that temporary mask. -/
def breadthFirst : Routine 22 := sequence (ofProgram (ListPrograms.copyProgram 21 2 18 12))
  (sequence reachCheckRoutine (clear 18))

theorem breadthFirst_executes (store : Store 22) (size : Nat) (value : Bool) (tail : List Bool)
    (width : store 2=List.replicate size true) (status : store 19=value::tail)
    (empty : RowEmpty store) (e17 : store 17=[]) (e18 : store 18=[]) (e23 : store 23=[]) :
    ∃time≤500000000*((store 0).length+size+1)^6,
      Executes breadthFirst store time
        (Function.update store 19
          ((value && DirectedCounting.strongConnectivityCheck
            (RealizabilityVerifier.BitGraph.edge size (store 0)))::tail)) := by
  have copying := copy_executes 21 (2:Fin 24) 18 12 (by decide) (by decide) (by decide) store
    (empty 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [width,e18,List.append_nil,List.length_replicate] at copying
  let ready := Function.update store 18 (List.replicate size true)
  obtain ⟨time,bound,checking⟩ := reachCheck_executes ready value tail
    (by simp [ready,status])
    (by intro r n0 n2 n17 n18 n19 n23;simpa [ready,n18] using empty r n0 n2 n17 n18 n19 n23)
    (by simp [ready,e17]) (by simp [ready,e23])
  have source : ready 0=store 0 := by simp [ready]
  have readyWidth : (ready 2).length=size := by simp [ready,width]
  rw [source,readyWidth,show ready 18=List.replicate size true by simp [ready]] at bound checking
  rw [List.length_replicate] at bound
  rw [bitGraph_all_active] at checking
  let passed := Function.update ready 19
    ((value && DirectedCounting.strongConnectivityCheck (RealizabilityVerifier.BitGraph.edge size (store 0)))::tail)
  have clearing := clear_executes (18:Fin 24) passed
  rw [show passed 18=List.replicate size true by simp [passed,ready],List.length_replicate] at clearing
  have final : Function.update passed 18 []=Function.update store 19
      ((value && DirectedCounting.strongConnectivityCheck (RealizabilityVerifier.BitGraph.edge size (store 0)))::tail) := by
    funext i
    by_cases a:i=18 <;> by_cases b:i=19 <;> simp_all [passed,ready]
  rw [final] at clearing
  let L := (store 0).length+size+1
  have powers : ((store 0).length+size+size+1)^6≤64*L^6 := by
    calc
      _≤(2*L)^6 := Nat.pow_le_pow_left (by dsimp only [L];omega) 6
      _=_ := by ring
  have big := bound.trans (Nat.mul_le_mul_left 7000000 powers)
  have linear : L≤L^6 := Nat.le_self_pow (by decide) _
  refine ⟨5*size+2+1+(time+1+(size+1)),?_,copying.sequence (checking.sequence clearing)⟩
  have base : L=(store 0).length+size+1 := rfl
  change _≤500000000*L^6
  omega

/-- Apply the same actual routine to the row-major matrix of binary arc
positivity. The routine never expands an arc multiplicity into messages. -/
theorem breadthFirst_matrix (store : Store 22) (size : Nat) (graph : Simulation.RoundGraph)
    (arcs : store 0=matrixBits size graph) (width : store 2=List.replicate size true)
    (value : Bool) (tail : List Bool) (status : store 19=value::tail)
    (empty : RowEmpty store) (e17 : store 17=[]) (e18 : store 18=[]) (e23 : store 23=[]) :
    ∃time≤500000000*(size*size+size+1)^6,
      Executes breadthFirst store time
        (Function.update store 19 ((value && DirectedCounting.strongConnectivityCheck
          (fun source target:Fin size=>decide (0<Encoding.matrixEdge graph size source target)))::tail)) := by
  have result := breadthFirst_executes store size value tail width status empty e17 e18 e23
  rw [arcs,matrixBits_length,matrixBits_edge] at result
  exact result

end Counting.StackMachine.NetworkRecognition
