import Counting.StackDagCanonicalInitializeMapping

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def initializeCanonical : Routine 128 := sequence initializeRead (sequence initializeCount initializeMapping)

def initializeData (source : Executable.Vista) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _=>[]) 20 ((Encoding.array Encoding.node).encode source.nodes))
    1 ((Encoding.array Encoding.natural).encode (Array.replicate source.nodes.size 0)))
    2 ((Encoding.array Encoding.node).encode #[]))
    23 (List.replicate source.nodes.size true))
    24 (List.replicate source.nodes.size true))
    25 (Encoding.natural.encode source.bottom)

def initializeCoefficient : Nat := DagParser.nodes.coefficient+2000

/-- Initialize the canonicalizer from the actual vista encoding. Its two
unary counters are bounded by the explicit DAG size, and mappings start at
zero. This initializer is total on typed vistas, including malformed DAGs. -/
theorem initialize_executes (source : Executable.Vista) :
    ∃ time ≤ initializeCoefficient*((Encoding.vista.encode source).length+1)^4,
      Executes initializeCanonical (inputStore 128 (Encoding.vista.encode source)) time (file (initializeData source)) := by
  obtain ⟨tr,br,rr⟩ := initializeRead_executes source
  let a := initializeReadData source
  obtain ⟨tc,bc,rc⟩ := initializeCount_executes a source.nodes
    (by simp [a,initializeReadData]) (by simp [a,initializeReadData])
    (by simp [a,initializeReadData]) (by simp [a,initializeReadData]) (by simp [a,initializeReadData])
  let b := initializeCountData a source.nodes
  obtain ⟨tm,bm,rm⟩ := initializeMapping_executes b source.nodes.size
    (by simp [b,initializeCountData]) (by simp [b,initializeCountData,a,initializeReadData])
    (by simp [b,initializeCountData,a,initializeReadData])
    (by simp [b,initializeCountData,a,initializeReadData])
    (by simp [b,initializeCountData,a,initializeReadData])
  have final : initializeMappingData b source.nodes.size=initializeData source := by
    funext r
    fin_cases r <;> simp [initializeMappingData,b,initializeCountData,a,initializeReadData,initializeData]
  rw [final] at rm
  refine ⟨_,?_,rr.sequence (rc.sequence rm)⟩
  let L := (Encoding.vista.encode source).length
  have a20 : a 20=(Encoding.array Encoding.node).encode source.nodes := by simp [a,initializeReadData]
  rw [a20] at bc
  have poolBound : ((Encoding.array Encoding.node).encode source.nodes).length ≤ L := by
    dsimp only [L]
    simp only [Encoding.vista,Encoding.transport,Encoding.product,List.length_append,
      Encoding.array,Encoding.transport]
    omega
  have nBound : source.nodes.size ≤ L :=
    (Encoding.array_size_le_length Encoding.node source.nodes (fun node _=>Encoding.node_positive_length node)).trans poolBound
  have positive : 1 ≤ L+1 := by omega
  have p3 : (L+1)^3 ≤ (L+1)^4 := Nat.pow_le_pow_right positive (by decide)
  have p2 : (L+1)^2 ≤ (L+1)^4 := Nat.pow_le_pow_right positive (by decide)
  have linear : L+1 ≤ (L+1)^4 := Nat.le_self_pow (by decide) _
  have cb : tc ≤ 1900*(L+1)^4 := bc.trans ((Nat.mul_le_mul_left 1900
    (Nat.pow_le_pow_left (Nat.add_le_add_right poolBound 1) 3)).trans (Nat.mul_le_mul_left 1900 p3))
  have mb : tm ≤ 40*(L+1)^4 := bm.trans ((Nat.mul_le_mul_left 40
    (Nat.pow_le_pow_left (Nat.add_le_add_right nBound 1) 2)).trans (Nat.mul_le_mul_left 40 p2))
  have parser := Nat.mul_le_mul_left DagParser.nodes.coefficient
    (Nat.pow_le_pow_right positive (by decide : DagParser.nodes.exponent ≤ 4))
  change DagParser.nodes.coefficient*(L+1)^DagParser.nodes.exponent ≤ DagParser.nodes.coefficient*(L+1)^4 at parser
  change tr ≤ DagParser.nodes.coefficient*(L+1)^DagParser.nodes.exponent+20*L+20 at br
  change _ ≤ (DagParser.nodes.coefficient+2000)*(L+1)^4
  rw [Nat.add_mul]
  omega

end Counting.StackMachine.DagUpdate.Canonical
