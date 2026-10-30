import Counting.StackDagCanonicalCollectHeader

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine
set_option maxHeartbeats 2000000

private theorem step_cap (mapping : Array Nat) (node : Executable.Node) (source index level cap : Nat)
    (positive : 1 ≤ cap) (sourceBound : source ≤ cap)
    (nodeBound : (Encoding.node.encode node).length ≤ cap)
    (mapBound : ((Encoding.array Encoding.natural).encode mapping).length ≤ cap)
    (indexBound : index ≤ cap) (levelBound : level.bits.length ≤ cap) :
    30000000000*(source+((Encoding.array Encoding.natural).encode mapping).length+1)^7+
      30*((Encoding.node.encode (Executable.referenceMap mapping node)).length+level.bits.length+1)+
      101*(index+(Encoding.node.encode (Executable.referenceMap mapping node)).length+1)^2 ≤
        100000000000000*cap^7 := by
  have remapped := Executable.referenceMap_encoded_polynomial mapping node
  have base : (Encoding.node.encode node).length+((Encoding.array Encoding.natural).encode mapping).length+1 ≤ 3*cap := by omega
  have output : (Encoding.node.encode (Executable.referenceMap mapping node)).length ≤ 45*cap^2 := by
    have p := Nat.pow_le_pow_left base 2
    nlinarith only [remapped,p]
  have linear : cap ≤ cap^2 := Nat.le_self_pow (by decide) _
  have one2 : 1 ≤ cap^2 := one_le_pow₀ positive
  have source : source+((Encoding.array Encoding.natural).encode mapping).length+1 ≤ 3*cap := by omega
  have chosen : index+(Encoding.node.encode (Executable.referenceMap mapping node)).length+1 ≤ 47*cap^2 := by omega
  have p7 := Nat.pow_le_pow_left source 7
  have p2 := Nat.pow_le_pow_left chosen 2
  rw [Nat.mul_pow] at p7 p2
  rw [←Nat.pow_mul] at p2
  norm_num only [Nat.reducePow,Nat.reduceMul] at p7 p2
  have lift2 : cap^2 ≤ cap^7 := Nat.pow_le_pow_right positive (by decide)
  have lift4 : cap^4 ≤ cap^7 := Nat.pow_le_pow_right positive (by decide)
  nlinarith only [p7,p2,output,levelBound,linear,one2,lift2,lift4]

theorem collectLoopBudget_cap (mapping : Array Nat) (level index : Nat)
    (nodes : List Executable.Node) (suffix : List Bool) (cap : Nat)
    (positive : 1 ≤ cap)
    (sourceBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ cap)
    (mapBound : ((Encoding.array Encoding.natural).encode mapping).length ≤ cap)
    (indexBound : index+nodes.length ≤ cap) (levelBound : level.bits.length ≤ cap) :
    collectLoopBudget mapping level index nodes suffix ≤
      nodes.length*(100000000000000*cap^7+6)+1 := by
  induction nodes generalizing index with
  | nil => simp [collectLoopBudget]
  | cons node nodes ih =>
    have lengths : (Encoding.sequence Encoding.node (node::nodes)++suffix).length=
        (Encoding.node.encode node).length+(Encoding.sequence Encoding.node nodes++suffix).length := by
      simp [Encoding.sequence,List.length_append]
    have nodeBound : (Encoding.node.encode node).length ≤ cap := by omega
    have sourceTail : (Encoding.sequence Encoding.node nodes++suffix).length ≤ cap := by omega
    have nextIndex : index+1+nodes.length ≤ cap := by simp only [List.length_cons] at indexBound;omega
    have first := step_cap mapping node (Encoding.sequence Encoding.node (node::nodes)++suffix).length
      index level cap positive sourceBound nodeBound mapBound (by omega) levelBound
    have last := ih (index+1) sourceTail nextIndex
    simp only [collectLoopBudget,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem collectEntries_length_le (mapping : Array Nat) (level index : Nat) (nodes : List Executable.Node) :
    (collectEntries mapping level index nodes).length ≤ nodes.length := by
  induction nodes generalizing index with
  | nil => rfl
  | cons node nodes ih =>
    have tail := ih (index+1)
    by_cases same : node.level=level <;> simp [collectEntries,same] <;> omega

def collectInputSize (mapping : Array Nat) (nodes : List Executable.Node) (level : Nat) : Nat :=
  ((Encoding.list Encoding.node).encode nodes).length+
    ((Encoding.array Encoding.natural).encode mapping).length+level.bits.length+1

def collectCoefficient : Nat := 100000000002000

/-- Polynomial time in the compact source, frozen map and binary level;
no graph-validity or bounded-multiplicity premise is needed. -/
theorem collectRecords_polynomial (store : Store 94) (mapping : Array Nat) (nodes : List Executable.Node)
    (level : Nat) (source : store 0=(Encoding.list Encoding.node).encode nodes)
    (mapAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (levelAt : store 82=level.bits) (status : store 81=[true])
    (index : store 83=[]) (counter : store 84=[]) (records : store 85=[]) (count : store 86=[])
    (empty : CollectScratch store) :
    ∃ time ≤ collectCoefficient*((store 0).length+(store 1).length+(store 82).length+1)^8,
      Routine.Executes collectRecords store time (collectedStore store mapping nodes level) := by
  obtain ⟨time,bound,run⟩ := collectRecords_executes store mapping nodes level source mapAt levelAt status index counter records count empty
  let K := collectInputSize mapping nodes level
  have positive : 1 ≤ K := by dsimp [K,collectInputSize];omega
  have sourceCap : ((Encoding.list Encoding.node).encode nodes).length ≤ K := by dsimp [K,collectInputSize];omega
  have sequenceCap : (Encoding.sequence Encoding.node nodes++[]).length ≤ K := by
    simp only [Encoding.list,List.length_append] at sourceCap
    simpa only [List.append_nil] using (show (Encoding.sequence Encoding.node nodes).length ≤ K by omega)
  have nodeCount : nodes.length ≤ ((Encoding.list Encoding.node).encode nodes).length := by
    simpa only [Encoding.array,Encoding.transport,List.toList_toArray,List.size_toArray] using
      Encoding.array_size_le_length Encoding.node nodes.toArray (fun n _=>Encoding.node_positive_length n)
  have countCap : nodes.length ≤ K := nodeCount.trans sourceCap
  have entriesCap := (collectEntries_length_le mapping level 0 nodes).trans countCap
  have loop := collectLoopBudget_cap mapping level 0 nodes [] K positive sequenceCap
    (by dsimp [K,collectInputSize];omega) (by omega) (by dsimp [K,collectInputSize];omega)
  have scaled := Nat.mul_le_mul_right (100000000000000*K^7+6) countCap
  have power : K*K^7=K^8 := by ring
  have loopBound : collectLoopBudget mapping level 0 nodes [] ≤ 100000000000000*K^8+6*K+1 := by
    nlinarith only [loop,scaled,power]
  have header : (store 0).length+1 ≤ K := by rw [source];dsimp [K,collectInputSize];omega
  have headerPow := Nat.pow_le_pow_left header 3
  have finishBase : (collectEntries mapping level 0 nodes).length+1 ≤ 2*K := by omega
  have finishPow := Nat.pow_le_pow_left finishBase 2
  have p1 : K ≤ K^8 := Nat.le_self_pow (by decide) _
  have p2 : K^2 ≤ K^8 := Nat.pow_le_pow_right positive (by decide)
  have p3 : K^3 ≤ K^8 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ K^8 := one_le_pow₀ positive
  refine ⟨time,?_,run⟩
  have size : (store 0).length+(store 1).length+(store 82).length+1=K := by rw [source,mapAt,levelAt];rfl
  rw [size]
  unfold collectCoefficient
  nlinarith only [bound,loopBound,headerPow,finishPow,countCap,entriesCap,p1,p2,p3,one]

end Counting.StackMachine.DagUpdate.Canonical
