import Counting.NetworkVistaReceiverAssemble
import Counting.NetworkVistaReceiverBounds

namespace Counting.StackMachine.NetworkVista.Receiver
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 200000

def receiverMessages (n : Nat) (graph : Simulation.RoundGraph) (views : Fin n→Executable.Vista) (receiver : Fin n) :=
  Executable.senderBundles (List.finRange n) (Encoding.matrixEdge graph n) views receiver

def receiverRow {n : Nat} (graph : Simulation.RoundGraph) (receiver : Fin n) := graph[receiver.val]?.getD #[]
def receiverDegree {n : Nat} (graph : Simulation.RoundGraph) (receiver : Fin n) := (receiverRow graph receiver).toList.sum

def readyWord (n depth : Nat) (leaders : Fin n→Bool) (views : Fin n→Executable.Vista)
    (graph : Simulation.RoundGraph) (receiver : Fin n) :=
  DagUpdate.Raw.inputWord depth (leaders receiver) (receiverDegree graph receiver) (views receiver)
    (receiverMessages n graph views receiver)

def prepare : Routine 128 := sequence (pushBit (context 15) true)
  (sequence readFields (sequence ownDegree (sequence incoming assemble)))

theorem prepare_executes (data : Fin 30→List Bool) (n depth : Nat)
    (leaders : Fin n→Bool) (views : Fin n→Executable.Vista) (graph : Simulation.RoundGraph) (receiver : Fin n)
    (shape : Encoding.matrixShape n graph=true)
    (depthAt : data 0=Encoding.natural.encode depth)
    (leadersAt : data 1=(Encoding.array Encoding.boolean).encode (Array.ofFn leaders))
    (viewsAt : data 2=(Encoding.array Encoding.vista).encode (Array.ofFn views))
    (graphAt : data 3=(Encoding.array (Encoding.array Encoding.natural)).encode graph)
    (position : (data 4).length=receiver.val)
    (empty : ∀r:Fin 30,7≤r.val → r.val≤15 → data r=[])
    (B : Nat) (positive : 1≤B) (population : n≤B) (bounded : ∀r,(data r).length≤B) :
    ∃ time ≤ 1000000000*(B+1)^6,
      Executes prepare (file data) time
        (file (Function.update data 13 (readyWord n depth leaders views graph receiver))) ∧
      (readyWord n depth leaders views graph receiver).length≤8*B+3 := by
  have e (r:Fin 30) (low:7≤r.val) (high:r.val≤15) := empty r low high
  have graphSize : graph.size=n := by
    simp only [Encoding.matrixShape,Bool.and_eq_true,beq_iff_eq] at shape
    exact shape.1
  let rows : Fin n→Array Nat := fun r=>receiverRow graph r
  have rowsEq : Array.ofFn rows=graph := by
    subst n
    simp [rows,receiverRow]
  have rowBound : ((Encoding.array Encoding.natural).encode (receiverRow graph receiver)).length≤B := by
    have inside : receiver.val<graph.size := by have := receiver.isLt;omega
    have member : receiverRow graph receiver∈graph.toList := by
      simp [receiverRow,Array.getElem?_eq_getElem inside]
    have bound := Encoding.array_member_length_le (Encoding.array Encoding.natural) graph _ member
    rw [←graphAt] at bound
    exact bound.trans (bounded 3)
  have viewBound : (Encoding.vista.encode (views receiver)).length≤B := by
    have bound := Encoding.array_member_length_le Encoding.vista (Array.ofFn views) (views receiver) (by simp)
    rw [←viewsAt] at bound
    exact bound.trans (bounded 2)
  have degreeBound : (receiverDegree graph receiver).bits.length≤B := (row_sum_bits_le _).trans rowBound
  have messageBound : ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
      (receiverMessages n graph views receiver)).length≤4*B+1 := by
    have bound := messages_length_bound n graph views receiver shape
    rw [←viewsAt,←graphAt] at bound
    have := bounded 2;have := bounded 3
    change ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
      (receiverMessages n graph views receiver)).length≤2*n+1+(data 2).length+(data 3).length at bound
    omega
  let a := Function.update data 15 [true]
  have start := pushBit_executes (context 15) true (file data)
  rw [file_context,e 15 (by decide) (by decide),file_update] at start
  obtain ⟨t0,b0,r0⟩ := readFields_executes a n leaders views rows receiver (by simp [a])
    (by simp [a,e 8 (by decide) (by decide)]) (by simp [a,e 9 (by decide) (by decide)])
    (by simp [a,e 10 (by decide) (by decide)]) (by simp [a,leadersAt]) (by simp [a,viewsAt])
    (by simp [a,rowsEq,graphAt]) (by simpa [a] using position)
  let b := fieldsData a (leaders receiver) (views receiver) (rows receiver)
  obtain ⟨t1,b1,r1⟩ := ownDegree_executes b (receiverRow graph receiver)
    (by simp [b,fieldsData,rows]) (by simp [b,fieldsData,a,e 11 (by decide) (by decide)])
  let c := Function.update b 11 (receiverDegree graph receiver).bits
  obtain ⟨t2,b2,r2⟩ := incoming_executes c n graph views receiver
    (by simp [c,b,fieldsData,a]) (by simp [c,b,fieldsData,a,e 12 (by decide) (by decide)])
    shape (by simp [c,b,fieldsData,a,viewsAt]) (by simp [c,b,fieldsData,a,graphAt])
    (by simpa [c,b,fieldsData,a] using position)
  let d := Function.update c 12 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
    (receiverMessages n graph views receiver))
  have dBound : ∀r,(d r).length≤4*B+1 := by
    intro r
    by_cases r8:r=8
    · subst r;simp [d,c,b,fieldsData,a,Encoding.boolean]
    by_cases r9:r=9
    · subst r;simpa [d,c,b,fieldsData,rows] using rowBound.trans (by omega : B≤4*B+1)
    by_cases r10:r=10
    · subst r;simpa only [d,c,b,fieldsData,Function.update_of_ne (by decide : (10:Fin 30)≠12),Function.update_of_ne (by decide : (10:Fin 30)≠11),Function.update_of_ne (by decide : (10:Fin 30)≠9),Function.update_self] using viewBound.trans (by omega : B≤4*B+1)
    by_cases r11:r=11
    · subst r;simpa [d,c] using degreeBound.trans (by omega : B≤4*B+1)
    by_cases r12:r=12
    · subst r;simpa [d] using messageBound
    by_cases r15:r=15
    · subst r;simp [d,c,b,fieldsData,a]
    simpa [d,c,b,fieldsData,a,r8,r9,r10,r11,r12,r15] using (bounded r).trans (by omega : B≤4*B+1)
  obtain ⟨t3,b3,r3⟩ := assemble_executes d depth (receiverDegree graph receiver) (leaders receiver) (views receiver)
    (receiverMessages n graph views receiver) (by simp [d,c,b,fieldsData,a,depthAt])
    (by simp [d,c,b,fieldsData]) (by simp [d,c,b,fieldsData]) (by simp [d,c]) (by simp [d])
    (by simp [d,c,b,fieldsData,a,e 13 (by decide) (by decide)])
    (by simp [d,c,b,fieldsData,a,e 14 (by decide) (by decide)]) (4*B+1) dBound
  have final : assembledData d (readyWord n depth leaders views graph receiver)=
      Function.update data 13 (readyWord n depth leaders views graph receiver) := by
    funext r
    fin_cases r <;> simp [assembledData,NetworkCertificate.erased,assembleFields,d,c,b,fieldsData,a,e]
  change Executes assemble (file d) t3 (file (assembledData d (readyWord n depth leaders views graph receiver))) at r3
  rw [final] at r3
  have time0 : t0≤100000*(4*(B+1))^6 := by
    apply b0.trans
    have := bounded 1;have := bounded 2;have := bounded 3;have := bounded 4
    simp only [a,Function.update_of_ne (by decide : (1:Fin 30)≠15),Function.update_of_ne (by decide : (2:Fin 30)≠15),Function.update_of_ne (by decide : (3:Fin 30)≠15),Function.update_of_ne (by decide : (4:Fin 30)≠15)]
    gcongr;omega
  have time1 : t1≤2100*(B+1)^3 := by
    apply b1.trans
    simp only [b,fieldsData,Function.update_self]
    gcongr
  have time2 : t2≤26000*(4*(B+1))^5 := by
    apply b2.trans
    have := bounded 2;have := bounded 3;have := bounded 4
    simp only [Complexity.polynomial,c,b,fieldsData,a]
    simp only [Function.update_of_ne (by decide : (2:Fin 30)≠11),Function.update_of_ne (by decide : (3:Fin 30)≠11),Function.update_of_ne (by decide : (4:Fin 30)≠11)]
    simp
    gcongr;omega
  have p3 : (B+1)^3≤(B+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have p5 : (B+1)^5≤(B+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have linear : B+1≤(B+1)^6 := Nat.le_self_pow (by decide) _
  refine ⟨1+1+(t0+1+(t1+1+(t2+1+t3))),?_,start.sequence (r0.sequence (r1.sequence (r2.sequence r3))),?_⟩
  · simp only [Nat.mul_pow] at time0 time2
    nlinarith only [time0,time1,time2,b3,p3,p5,linear]
  · have leaderLength : (Encoding.boolean.encode (leaders receiver)).length=1 := rfl
    have depthBound := bounded 0
    rw [depthAt] at depthBound
    change (Encoding.natural.encode depth++(Encoding.boolean.encode (leaders receiver)++
      (Encoding.natural.encode (receiverDegree graph receiver)++(Encoding.vista.encode (views receiver)++
        (Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
          (receiverMessages n graph views receiver))))).length≤8*B+3
    simp only [List.length_append,leaderLength,Encoding.natural_length]
    rw [Encoding.bits_length] at degreeBound
    rw [Encoding.natural_length] at depthBound
    omega

end Counting.StackMachine.NetworkVista.Receiver
