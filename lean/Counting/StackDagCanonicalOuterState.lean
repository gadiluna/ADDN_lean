import Counting.StackDagCanonicalInitialize
import Counting.DagCanonicalPrefixEncodingBounds
import Counting.DagCanonicalBySize

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine RealizabilityCall Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Persistent outer fields. The source array never changes across levels. -/
def canonicalData (source : Vista) (level : Nat) (counter : List Bool) : Fin 30 → List Bool := fun r=>
  match r.val with
  | 1 => (Encoding.array Encoding.natural).encode (canonicalPrefix source level).2
  | 2 => (Encoding.array Encoding.node).encode (canonicalPrefix source level).1
  | 20 => (Encoding.array Encoding.node).encode source.nodes
  | 22 => level.bits
  | 23 => List.replicate source.nodes.size true
  | 24 => counter
  | 25 => Encoding.natural.encode source.bottom
  | _ => []

theorem canonicalData_counter_update (source : Vista) (level : Nat) (counter rest : List Bool) :
    Function.update (canonicalData source level counter) 24 rest=canonicalData source level rest := by
  funext r
  fin_cases r <;> simp [canonicalData]

theorem initializeData_eq_canonicalData (source : Vista) :
    initializeData source=canonicalData source 0 (List.replicate source.nodes.size true) := by
  funext r
  fin_cases r <;> simp [initializeData,canonicalData,canonicalPrefix]

theorem canonicalData_bounded (source : Vista) (level : Nat) (counter : List Bool)
    (levels : level ≤ source.nodes.size) (remaining : counter.length ≤ source.nodes.size) :
    ∀ r,(canonicalData source level counter r).length ≤ 100*((Encoding.vista.encode source).length+1)^5 := by
  obtain ⟨pool,mapping,_⟩ := canonicalPrefix_encoded_polynomial source level levels
  have nBound := canonical_source_count_bound source
  have levelBits : level.bits.length ≤ (Encoding.vista.encode source).length := by
    rw [Encoding.bits_length]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (levels.trans nBound)
  have sourceBound : ((Encoding.array Encoding.node).encode source.nodes).length ≤ (Encoding.vista.encode source).length := by
    simp only [Encoding.vista,Encoding.transport,Encoding.product,Encoding.array,List.length_append]
    omega
  have bottomBound : (Encoding.natural.encode source.bottom).length ≤ (Encoding.vista.encode source).length := by
    simp only [Encoding.vista,Encoding.transport,Encoding.product,List.length_append]
    omega
  have linear : (Encoding.vista.encode source).length+1 ≤ ((Encoding.vista.encode source).length+1)^5 :=
    Nat.le_self_pow (by decide) _
  intro r
  fin_cases r <;> simp only [canonicalData,List.length_nil,List.length_replicate] <;> omega

theorem initialize_canonicalData_executes (source : Vista) :
    ∃ time ≤ initializeCoefficient*((Encoding.vista.encode source).length+1)^4,
      Executes initializeCanonical (inputStore 128 (Encoding.vista.encode source)) time
        (file (canonicalData source 0 (List.replicate source.nodes.size true))) := by
  simpa only [initializeData_eq_canonicalData] using initialize_executes source

theorem canonicalData_next (source : Vista) (level : Nat) (counter : List Bool) :
    Function.update (Function.update (Function.update (canonicalData source level counter)
      1 ((Encoding.array Encoding.natural).encode (canonicalLevel source (canonicalPrefix source level) level).2))
      2 ((Encoding.array Encoding.node).encode (canonicalLevel source (canonicalPrefix source level) level).1))
      22 (level+1).bits=canonicalData source (level+1) counter := by
  have next : canonicalPrefix source (level+1)=canonicalLevel source (canonicalPrefix source level) level := by
    simp [canonicalPrefix,List.range_succ]
  funext r
  fin_cases r <;> simp [canonicalData,next]

theorem canonicalPrefix_final (source : Vista) (valid : NodesValid source) (nonempty : 0 < source.nodes.size) :
    canonicalPrefix source source.nodes.size=canonicalState source :=
  canonicalState_by_size source valid nonempty

end Counting.StackMachine.DagUpdate.Canonical
