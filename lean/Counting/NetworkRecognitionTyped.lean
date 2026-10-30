import Counting.NetworkRecognitionInputSpec

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def semanticCheck : Routine 24 := sequence (relocate leaderCheck matrixRoles)
  (sequence roundsPrefix (clear 0))

def semanticCheckStore (store:Store 24) (accepted:Bool) (tail:List Bool)
    (input:Simulation.Input) (suffix:List Bool) : Store 24 :=
  Function.update (Function.update store 17 suffix) 1 ((accepted && Encoding.networkValid input)::tail)

/-- Full physical network validity on canonical serialized inputs. Every
matrix is read, its shape checked, its positive-arc graph constructed, and
BFS executed. No semantic admissibility premise is required. -/
theorem semanticCheck_executes (store:Store 24) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (empty:∀r:Fin 26,r≠1 → r≠17 → store r=[])
    (input:Simulation.Input) (suffix:List Bool)
    (encoded:store 17=Encoding.networkInput.encode input++suffix) :
    ∃time ≤ 70000000000*((store 17).length+1)^7,
      Executes semanticCheck store time (semanticCheckStore store accepted tail input suffix) := by
  let remaining:=(Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode (networkGraphs input)++suffix
  let localStore:=store ∘ matrixRoles
  have localWork (r:Fin 21) (small:r.val<17) (n1:r≠1):localStore r=[]:=by
    apply empty
    · intro same;apply n1;apply Fin.ext;exact congrArg (fun i:Fin 26=>i.val) same
    · intro same;have:=congrArg (fun i:Fin 26=>i.val) same;change r.val=17 at this;omega
  obtain ⟨leaderTime,leaderBound,leaderRun⟩:=leaderCheck_executes localStore accepted tail status localWork
    (empty 18 (by decide) (by decide)) (empty 19 (by decide) (by decide)) (empty 20 (by decide) (by decide))
    input.leaders.toList remaining
    (by change store 17=(Encoding.list Encoding.boolean).encode input.leaders.toList++remaining
        rw [encoded,networkInput_encoded,List.append_assoc])
  let prepared:=Function.update (Function.update (Function.update store 17 remaining)
    0 (List.replicate input.leaders.size true)) 1 ((accepted && leadersAccepted input.leaders.toList)::tail)
  have preparing:Executes (relocate leaderCheck matrixRoles) store leaderTime prepared:=by
    apply relocate_executes_frame leaderCheck matrixRoles store prepared localStore
      (leaderCheckStore localStore accepted tail input.leaders.toList remaining) leaderTime rfl
    · intro i
      fin_cases i <;> simp [prepared,localStore,matrixRoles,leaderCheckStore]
    · intro r outside
      have n0:r≠0:=by simpa [matrixRoles] using (outside 0).symm
      have n1:r≠1:=by simpa [matrixRoles] using (outside 1).symm
      have n17:r≠17:=by simpa [matrixRoles] using (outside 17).symm
      simp [prepared,n0,n1,n17]
    · exact leaderRun
  obtain ⟨roundTime,roundBound,roundRun⟩:=roundsPrefix_executes prepared
    (accepted && leadersAccepted input.leaders.toList) tail (by simp [prepared])
    (by intro r n0 n1 n17;simpa [prepared,n0,n1,n17] using empty r n1 n17)
    (by simp [prepared]) (networkGraphs input) suffix (by simp [prepared,remaining])
  let checked:=roundsPrefixStore prepared (accepted && leadersAccepted input.leaders.toList) tail (networkGraphs input) suffix
  have clearing:=clear_executes (0:Fin 26) checked
  rw [show checked 0=List.replicate input.leaders.size true by simp [checked,roundsPrefixStore,prepared],List.length_replicate] at clearing
  have actual:(leadersAccepted input.leaders.toList && roundDecisions input.leaders.size (networkGraphs input))=Encoding.networkValid input:=by
    simpa only [Array.length_toList] using network_decisions_actual input
  have final:Function.update checked 0 []=semanticCheckStore store accepted tail input suffix:=by
    funext r
    by_cases n0:r=0 <;> by_cases n1:r=1 <;> by_cases n17:r=17 <;>
      simp [checked,roundsPrefixStore,prepared,semanticCheckStore,n0,n1,n17,empty,Bool.and_assoc,actual]
  rw [final] at clearing
  have shorter:(prepared 17).length ≤ (store 17).length:=by
    rw [encoded,networkInput_encoded]
    change remaining.length ≤ ((Encoding.list Encoding.boolean).encode input.leaders.toList++
      (Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode (networkGraphs input)++suffix).length
    simp only [remaining,List.length_append];omega
  have population:input.leaders.size ≤ (store 17).length:=by
    have bounded:=Encoding.network_agents_le_length input
    rw [encoded,List.length_append];omega
  let S:=(store 17).length+1
  have base:S=(store 17).length+1:=rfl
  have positive:1≤S:=by omega
  change leaderTime ≤ 2000*S^3 at leaderBound
  rw [show (prepared 0).length=input.leaders.size by simp [prepared]] at roundBound
  have roundLimit:roundTime ≤ 500020000*(2*S)^7:=by apply roundBound.trans;gcongr;omega
  have expanded:500020000*(2*S)^7=64002560000*S^7:=by ring
  rw [expanded] at roundLimit
  have lower:S^3≤S^7:=Nat.pow_le_pow_right positive (by decide)
  have linear:S≤S^7:=Nat.le_self_pow (by decide) _
  refine ⟨leaderTime+1+(roundTime+1+(input.leaders.size+1)),?_,preparing.sequence (roundRun.sequence clearing)⟩
  change _ ≤ 70000000000*S^7
  omega

end Counting.StackMachine.NetworkRecognition
