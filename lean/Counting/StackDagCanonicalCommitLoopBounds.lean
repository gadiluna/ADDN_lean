import Counting.StackDagCanonicalCommitLoopSize

namespace Counting.StackMachine.DagUpdate.Canonical
open Executable

theorem commitStepBudget_cap (state : CanonicalState) (record : Sort.Record) (sourceLength cap : Nat)
    (positive : 1 ≤ cap) (inside : record.1 < state.2.size)
    (mappingBound : ((Encoding.array Encoding.natural).encode state.2).length ≤ cap)
    (poolBound : ((Encoding.array Encoding.node).encode state.1).length ≤ cap)
    (recordBound : (Sort.recordCodec.encode record).length ≤ cap)
    (nextPoolBound : ((Encoding.array Encoding.node).encode (commitRecord state record).1).length ≤ cap)
    (sourceBound : sourceLength ≤ cap) :
    commitStepBudget state record sourceLength ≤ 1000000*cap^4 := by
  let P := ((Encoding.array Encoding.node).encode state.1).length
  let M := ((Encoding.array Encoding.natural).encode state.2).length
  let Q := (Encoding.node.encode record.2).length
  let R := ((Encoding.array Encoding.node).encode (intern state.1 record.2).1).length
  let I := (intern state.1 record.2).2.size
  have queryBound : Q ≤ cap := by
    simp only [Sort.recordCodec,Encoding.product,List.length_append] at recordBound
    dsimp [Q];omega
  have count := Encoding.array_size_le_length Encoding.natural state.2
    (by intro n _;rw [Encoding.natural_length];omega)
  have slot : record.1+1 ≤ cap := by omega
  have resultIndex := intern_index_lt state.1 record.2
  have resultCount := Encoding.array_size_le_length Encoding.node (intern state.1 record.2).1
    (fun node _=>Encoding.node_positive_length node)
  have indexBound : I ≤ cap := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
    change R ≤ cap at nextPoolBound
    dsimp only [R] at nextPoolBound
    omega)
  have p1 := Nat.pow_le_pow_left (show sourceLength+1 ≤ 2*cap by omega) 3
  have p2 := Nat.pow_le_pow_left (show (Sort.recordCodec.encode record).length+M+1 ≤ 3*cap by dsimp [M];omega) 3
  have p3 := Nat.pow_le_pow_left (show P+Q+1 ≤ 3*cap by dsimp [P];omega) 4
  have cube : cap^3 ≤ cap^4 := Nat.pow_le_pow_right positive (by decide)
  have linear : cap ≤ cap^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ cap^4 := one_le_pow₀ positive
  change P ≤ cap at poolBound
  change M ≤ cap at mappingBound
  change R ≤ cap at nextPoolBound
  change 2100*(sourceLength+1)^3+100*((Sort.recordCodec.encode record).length+M+1)^3+
    (8000*(P+Q+1)^4+17*M+7*Q+7*P+6*R+3*(record.1+1)+17*I+100)+2 ≤ _
  nlinarith only [p1,p2,p3,cube,linear,one,mappingBound,poolBound,queryBound,nextPoolBound,slot,indexBound]

end Counting.StackMachine.DagUpdate.Canonical
