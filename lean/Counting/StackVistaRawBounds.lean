import Counting.StackVistaRawPrepare
import Counting.StackVistaRawAssemble
import Counting.StackVistaRawFinish
import Counting.StackVistaMessagesBounds

namespace Counting.StackMachine.DagUpdate.Raw
open EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem inputWord_length (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    (inputWord round leader degree old messages).length =
      2*round.size+2*degree.size+2*old.bottom.size+4+
      ((Encoding.array Encoding.node).encode old.nodes).length+
      ((Encoding.list Receive.messageCodec).encode messages).length := by
  simp only [inputWord, inputCodec, Encoding.product, Encoding.boolean, Encoding.vista,
    Encoding.transport, Encoding.array, List.length_append, List.length_cons,
    List.length_nil, Encoding.natural_length]
  omega

theorem natural_successor_size (value : Nat) : (value+1).size ≤ value.size+1 := by
  apply Nat.size_le.mpr
  have bound := Nat.lt_size_self value
  have positive : 0 < 2^value.size := Nat.two_pow_pos _
  rw [pow_succ]
  omega

theorem input_messagesBase (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    Receive.messagesBase (old.nodes,[]) messages [] ≤
      (inputWord round leader degree old messages).length+1 := by
  rw [inputWord_length]
  simp only [Receive.messagesBase, edgeCodec, Encoding.list, Encoding.natural_length,
    Encoding.sequence, List.length_nil, Nat.size_zero, Nat.mul_zero, Nat.zero_add,
    Nat.add_zero, List.length_append]
  omega

theorem merged_encoded_bound (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    let K := (inputWord round leader degree old messages).length+1
    let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
    ((Encoding.array Encoding.node).encode merged.1).length ≤ 20*K^2 ∧
      ((Encoding.list edgeCodec).encode merged.2).length ≤ 20*K^2 := by
  have bounds := Executable.mergeMessages_encoded_polynomial (old.nodes,[]) messages
  have base := input_messagesBase round leader degree old messages
  have scaling := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
  exact ⟨bounds.1.trans scaling, bounds.2.trans scaling⟩

theorem newNode_encoded_length (round bottom : Nat) (leader : Bool) (degree : Nat)
    (edges : List (Nat×Nat)) :
    (Encoding.node.encode (newNode round bottom leader degree edges)).length =
      2*(round+1).size+2*(bottom+1).size+2*degree.size+4+
      ((Encoding.list edgeCodec).encode edges).length := by
  simp only [edgeCodec, newNode, Encoding.node, Encoding.transport, Encoding.nodeFields, Encoding.product,
    Encoding.optionalNatural, Option.map_some, Option.getD_some, Encoding.boolean,
    List.length_append, List.length_cons, List.length_nil, Encoding.natural_length]
  omega

theorem newNode_encoded_bound (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    let K := (inputWord round leader degree old messages).length+1
    let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
    (Encoding.node.encode (newNode round old.bottom leader degree merged.2)).length ≤ 40*K^2 := by
  let K := (inputWord round leader degree old messages).length+1
  have edges := (merged_encoded_bound round leader degree old messages).2
  have length := inputWord_length round leader degree old messages
  have nextRound := natural_successor_size round
  have nextBottom := natural_successor_size old.bottom
  have positive : 1 ≤ K := by dsimp [K]; omega
  have square : K ≤ K^2 := Nat.le_self_pow (by decide) _
  change _ ≤ 40*K^2
  rw [newNode_encoded_length]
  change _ ≤ 20*K^2 at edges
  have metadata : 2*round.size+2*old.bottom.size+2*degree.size+4 ≤ K := by dsimp [K]; omega
  omega

theorem prepareBudget_polynomial (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    prepareBudget round degree old messages ≤
      (DagParser.nodes.coefficient+100)*((inputWord round leader degree old messages).length+1)^4 := by
  let K := (inputWord round leader degree old messages).length+1
  let P := ((Encoding.array Encoding.node).encode old.nodes).length
  let R := ((Encoding.list Receive.messageCodec).encode messages).length
  have length := inputWord_length round leader degree old messages
  have tailLength : (Encoding.vista.encode old++(Encoding.list Receive.messageCodec).encode messages).length =
      P+2*old.bottom.size+1+R := by
    simp only [P, R, Encoding.vista, Encoding.transport, Encoding.product, Encoding.array,
      List.length_append, Encoding.natural_length]
    omega
  have tailBound : P+2*old.bottom.size+1+R+1 ≤ K := by dsimp [P,R,K] at *; omega
  have parser : Complexity.polynomial DagParser.nodes.coefficient DagParser.nodes.exponent
      (Encoding.vista.encode old++(Encoding.list Receive.messageCodec).encode messages).length ≤
      DagParser.nodes.coefficient*K^4 := by
    change DagParser.nodes.coefficient*(_+1)^4 ≤ _
    rw [tailLength]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left tailBound 4)
  have linear : K ≤ K^4 := Nat.le_self_pow (by decide) _
  have overhead : 5*round.size+5*degree.size+2*P+5*old.bottom.size+6*R+23 ≤ 100*K := by
    dsimp [P,R,K] at *
    omega
  change _ ≤ (DagParser.nodes.coefficient+100)*K^4
  unfold prepareBudget
  simp only [Encoding.bits_length]
  dsimp only [P,R] at overhead
  nlinarith only [parser,overhead,linear]

theorem assembleBudget_polynomial (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
    assembleBudget round old.bottom leader degree merged.2 ≤
      300*((inputWord round leader degree old messages).length+1)^2 := by
  let K := (inputWord round leader degree old messages).length+1
  have length := inputWord_length round leader degree old messages
  have edges := (merged_encoded_bound round leader degree old messages).2
  have node := newNode_encoded_bound round leader degree old messages
  have nextRound := natural_successor_size round
  have nextBottom := natural_successor_size old.bottom
  have positive : 1 ≤ K := by dsimp [K]; omega
  have square : K ≤ K^2 := Nat.le_self_pow (by decide) _
  have metadata : round.size+old.bottom.size+degree.size ≤ K := by dsimp [K]; omega
  change _ ≤ 300*K^2
  change _ ≤ 20*K^2 at edges
  change _ ≤ 40*K^2 at node
  unfold assembleBudget
  simp only [edgeCodec,newNode,NodeMap.parentNumber,Option.map_some,Option.getD_some,Encoding.bits_length] at *
  omega

theorem intern_encoded_length (pool : Array Executable.Node) (node : Executable.Node) :
    ((Encoding.array Encoding.node).encode (Executable.intern pool node).1).length ≤
      ((Encoding.array Encoding.node).encode pool).length+(Encoding.node.encode node).length+2 := by
  unfold Executable.intern
  split
  · dsimp only
    omega
  · have next := natural_successor_size pool.size
    simp only [Encoding.array_length,Array.size_push,Array.toList_push,List.map_append,
      List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega

def finishCoefficient : Nat := 8000*61^4+1000

theorem finishBudget_cap (pool : Array Executable.Node) (node : Executable.Node) (K : Nat)
    (positive : 1 ≤ K)
    (poolBound : ((Encoding.array Encoding.node).encode pool).length ≤ 20*K^2)
    (nodeBound : (Encoding.node.encode node).length ≤ 40*K^2) :
    finishBudget pool node ≤ finishCoefficient*K^8 := by
  let P := ((Encoding.array Encoding.node).encode pool).length
  let Q := (Encoding.node.encode node).length
  have result := intern_encoded_length pool node
  have index : (Executable.intern pool node).2.size ≤ P+1 := by
    have bound := Executable.intern_index_lt pool node
    have capacity := Executable.intern_size_le_succ pool node
    have count := Encoding.array_size_le_length Encoding.node pool
      (fun node _ => Encoding.node_positive_length node)
    have size : (Executable.intern pool node).2.size ≤ (Executable.intern pool node).2 :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    dsimp [P]
    omega
  have one : 1 ≤ K^2 := one_le_pow₀ positive
  have scale : P+Q+1 ≤ 61*K^2 := by dsimp [P,Q]; omega
  have fourth := Nat.mul_le_mul_left 8000 (Nat.pow_le_pow_left scale 4)
  have fourthEq : 8000*(61*K^2)^4 = 8000*61^4*K^8 := by ring
  rw [fourthEq] at fourth
  have square : K^2 ≤ K^8 := Nat.pow_le_pow_right positive (by decide)
  unfold finishBudget
  simp only [Encoding.bits_length]
  change 8000*(P+Q+1)^4+7*P+Q+5*(Executable.intern pool node).2.size+
    6*((Encoding.array Encoding.node).encode (Executable.intern pool node).1).length+22 ≤ _
  change P ≤ 20*K^2 at poolBound
  change Q ≤ 40*K^2 at nodeBound
  change _ ≤ P+Q+2 at result
  unfold finishCoefficient
  nlinarith only [fourth,square,poolBound,nodeBound,result,index,one]

end Counting.StackMachine.DagUpdate.Raw
