import Counting.StackVistaMessageStep
import Counting.DagMessageEncodingBounds

namespace Counting.StackMachine.DagUpdate.Receive
set_option backward.isDefEq.respectTransparency false

theorem mergeTailBudget_cap (mapping : Array Nat) (bottom count : Nat) (edges : List (Nat×Nat))
    (cap : Nat) (positive : 1≤cap)
    (mapBound : ((Encoding.array Encoding.natural).encode mapping).length≤cap)
    (bottomBound : bottom.bits.length≤cap) (countBound : count.bits.length≤cap)
    (edgeBound : ((Encoding.list edgeCodec).encode edges).length≤cap)
    (outputBound : ((Encoding.list edgeCodec).encode
      (Executable.addCount (mapping[bottom]?.getD 0) count edges)).length≤cap) :
    mergeTailBudget mapping bottom count edges≤1000000*cap^3 := by
  have indexBound : (mapping[bottom]?.getD 0).bits.length≤cap := by
    rw [Encoding.bits_length]
    exact (Encoding.naturalArray_entry_size_le mapping bottom).trans mapBound
  have queryLength : (Encoding.natural.encode bottom).length=2*bottom.bits.length+1 := by
    simp only [Encoding.natural_length,Encoding.bits_length]
  have readBase : ((Encoding.array Encoding.natural).encode mapping).length+
      (Encoding.natural.encode bottom).length+1≤5*cap := by rw [queryLength];omega
  have addBase : ((Encoding.list edgeCodec).encode edges).length+
      (mapping[bottom]?.getD 0).bits.length+count.bits.length+1≤4*cap := by omega
  have readPower := Nat.pow_le_pow_left readBase 3
  have addPower := Nat.pow_le_pow_left addBase 3
  have linear : cap≤cap^3 := Nat.le_self_pow (by decide) _
  dsimp only [mergeTailBudget]
  rw [queryLength] at readPower ⊢
  nlinarith only [readPower,addPower,linear,mapBound,bottomBound,countBound,indexBound,
    edgeBound,outputBound,positive]

def messageStepCoefficient : Nat := Import.importCoefficient*4^15+1000001

theorem messageStepBudget_cap (state : Executable.MergeState) (message : Executable.Vista×Nat)
    (sourceLength cap : Nat) (positive : 1≤cap)
    (poolBound : ((Encoding.array Encoding.node).encode state.1).length≤cap)
    (messageBound : (messageCodec.encode message).length≤cap)
    (sourceBound : sourceLength≤cap)
    (edgeBound : ((Encoding.list edgeCodec).encode state.2).length≤cap)
    (mappingBound : ((Encoding.array Encoding.natural).encode (Executable.importVista state.1 message.1).2).length≤cap)
    (nextEdgeBound : ((Encoding.list edgeCodec).encode (Executable.mergeMessage state message).2).length≤cap) :
    messageStepBudget state.1 message state.2 sourceLength ≤ messageStepCoefficient*cap^15 := by
  have nodeBound := (Executable.message_fields_length message).trans messageBound
  have bottomBound : message.1.bottom.bits.length≤cap := by
    simp only [messageCodec,Encoding.product,Encoding.vista,Encoding.transport,
      List.length_append,Encoding.natural_length] at messageBound
    rw [Encoding.bits_length]
    omega
  have countBound : message.2.bits.length≤cap := by
    rw [Encoding.bits_length]
    exact (Executable.message_count_bits message).trans messageBound
  have tailBound := mergeTailBudget_cap (Executable.importVista state.1 message.1).2
    message.1.bottom message.2 state.2 cap positive mappingBound bottomBound countBound edgeBound nextEdgeBound
  have importBound := Import.importNodesBudget_polynomial state.1 message.1.nodes.toList sourceLength
  have inputBound : ((Encoding.array Encoding.node).encode state.1).length+
      ((Encoding.list Encoding.node).encode message.1.nodes.toList).length+sourceLength+1≤4*cap := by
    change ((Encoding.list Encoding.node).encode message.1.nodes.toList).length≤cap at nodeBound
    omega
  have importPower := Nat.pow_le_pow_left inputBound 15
  have degree : cap^3≤cap^15 := Nat.pow_le_pow_right positive (by decide)
  have one : 1≤cap^15 := one_le_pow₀ positive
  have bodyLimit : Import.importNodesBudget state.1 message.1.nodes.toList sourceLength ≤
      (Import.importCoefficient*4^15)*cap^15 := by
    calc
      _ ≤ Import.importCoefficient*(4*cap)^15 :=
        importBound.trans (Nat.mul_le_mul_left _ importPower)
      _ = _ := by ring
  have tailLimit := tailBound.trans (Nat.mul_le_mul_left 1000000 degree)
  dsimp only [messageStepBudget,messageStepCoefficient]
  nlinarith only [bodyLimit,tailLimit,one]

end Counting.StackMachine.DagUpdate.Receive
