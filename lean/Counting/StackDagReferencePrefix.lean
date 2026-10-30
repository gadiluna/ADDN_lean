import Counting.StackDagReferenceEdges
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def referenceHeaderRoles : FullListWorkspace 18:=⟨![28,1,0,2,30,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩
def referenceIncoming : Routine 33:=sequence (readListHeader 18 referenceHeaderRoles) (forEach 30 referenceItem)

def referencePrefixStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (target : Nat) (edges : List (Nat×Nat)) (suffix : List Bool) : Store 33:=
  Function.update (Function.update store 28 suffix) 1 ((accepted && noIncomingReference target edges)::tail)

theorem referenceIncoming_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (e22 : store 22=[]) (e30 : store 30=[]) (e31 : store 31=[])
    (target : Nat) (targetCode : store 26=target.bits)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 28=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix) :
    ∃ time ≤ 2000*((store 28).length+target.size+1)^3,
      Executes referenceIncoming store time (referencePrefixStore store accepted tail target edges suffix) := by
  let codec:=Encoding.product Encoding.natural Encoding.natural
  have positive (edge : Nat×Nat) : 0<(codec.encode edge).length:=by simp [codec,Encoding.product,Encoding.natural_length]
  have headerWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (referenceHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [referenceHeaderRoles,work,e30]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 18 referenceHeaderRoles store accepted tail
    status headerWork codec positive edges suffix input
  let ready:=Function.update (Function.update store 28 (Encoding.sequence codec edges++suffix)) 30 (List.replicate edges.length true)
  obtain ⟨loopTime,loopBound,loopRun⟩:=referenceEdges_executes ready accepted tail
    (by simp [ready,status]) (by simp [ready,work]) (by simp [ready,work]) (by simp [ready,work])
    (by simp [ready,e22]) (by simp [ready,e31]) target (by simp [ready,targetCode]) edges suffix
    (by simp [ready,codec]) (List.replicate edges.length true) (by simp [ready]) (by simp)
  have final : referenceEdgesStore ready accepted tail target edges suffix=referencePrefixStore store accepted tail target edges suffix:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r28 : r=28 <;> by_cases r30 : r=30 <;>
      simp [referenceEdgesStore,referencePrefixStore,ready,r1,r28,r30,e30]
  rw [final] at loopRun
  have shorter : (ready 28).length≤(store 28).length:=by
    rw [input]
    change (Encoding.sequence codec edges++suffix).length≤
      ((Encoding.natural.encode edges.length++Encoding.sequence codec edges)++suffix).length
    simp only [List.length_append]
    omega
  have countBound : edges.length≤(store 28).length:=by
    have count:=VerifiedParser.sequence_count_le positive edges
    rw [input]
    change edges.length≤((Encoding.natural.encode edges.length++Encoding.sequence codec edges)++suffix).length
    simp only [List.length_append]
    omega
  let S:=(store 28).length+target.size+1
  have spos : 1≤S:=by dsimp only [S];omega
  have countS : edges.length≤S:=by dsimp only [S];omega
  have inputS : (ready 28).length+target.size+1≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤50*S^2+2*S+1:=by
    have bounded : loopTime≤S*(50*S+2)+1:=loopBound.trans (by gcongr)
    nlinarith
  change headerTime≤1820*((store 28).length+1)^3 at headerBound
  have headerLimit : headerTime≤1820*S^3:=by apply headerBound.trans;gcongr;dsimp only [S];omega
  have square : S^2≤S^3:=Nat.pow_le_pow_right spos (by decide)
  have linear : S≤S^3:=Nat.le_self_pow (by decide) _
  have one : 1≤S^3:=Nat.one_le_pow _ _ spos
  exact ⟨headerTime+1+loopTime,by change _≤2000*S^3;omega,headerRun.sequence loopRun⟩

end Counting.StackMachine.DagValidation
