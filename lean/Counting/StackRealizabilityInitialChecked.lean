import Counting.StackRealizabilityInitialPrefix
import Counting.StackRealizabilityInitialGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem initialRangeSum_size (nodes : List Executable.Node) (start : Nat) (values : List Nat)
    (leaders nonleaders : Nat) :
    (leaders+initialRangeSum nodes true start values).size+
      (nonleaders+initialRangeSum nodes false start values).size ≤
        leaders.size+nonleaders.size+(Encoding.sequence Encoding.natural values).length:=by
  induction values generalizing start leaders nonleaders with
  | nil=>simp [initialRangeSum,Encoding.sequence]
  | cons value values ih=>
    have next:=ih (start+1)
      (leaders+initialContribution (nodes[start]?.getD default) true value)
      (nonleaders+initialContribution (nodes[start]?.getD default) false value)
    have entry:=initial_totals_size (nodes[start]?.getD default) leaders nonleaders value
    simp only [initialRangeSum,Encoding.sequence,List.length_append,Encoding.natural_length]
    simp only [Nat.add_assoc] at next
    omega

def initialPrefixRoles : Fin 26 ↪ Fin 28 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 28=>r.val) same

def initialGuardRoles : Fin 10 ↪ Fin 28:=⟨![21,22,26,27,1,0,2,3,4,5],by decide⟩

def initialCheck : Routine 26:=sequence (mapRegisters initialPrefixRoles initialPrefix)
  (mapRegisters initialGuardRoles initialBoundsGuard)

def initialScanCheck (nodes : List Executable.Node) (values : List Nat) (ell order : Nat) : Bool:=
  initialBoundsCheck (initialRangeSum nodes true 0 values) (initialRangeSum nodes false 0 values) ell order

def initialCheckStore (store : Store 26) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (values : List Nat) (ell order : Nat)
    (nodeSuffix weightSuffix : List Bool) : Store 26:=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    17 (Encoding.sequence Encoding.node nodes++nodeSuffix)) 20 weightSuffix)
      21 (initialRangeSum nodes true 0 values).bits) 22 (initialRangeSum nodes false 0 values).bits)
        1 ((accepted&&initialScanCheck nodes values ell order)::tail)

/-- A complete charged pass for all four initial capacity conditions of
the actual verifier. Parsing/canonicality and equal list lengths are checked
by the preceding guards; no numeric population is expanded. -/
theorem initialCheck_executes (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e21 : store 21=[]) (e22 : store 22=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (nodes : List Executable.Node) (values : List Nat) (length : values.length=nodes.length)
    (nodeSuffix weightSuffix : List Bool)
    (nodeInput : store 17=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : store 20=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (ell order : Nat) (leaderInput : store 26=ell.bits) (orderInput : store 27=order.bits) :
    ∃ time ≤ 13200*((store 17).length+(store 20).length+ell.size+order.size+1)^5,
      Executes initialCheck store time
        (initialCheckStore store accepted tail nodes values ell order nodeSuffix weightSuffix):=by
  let original : Store 24:=store ∘ initialPrefixRoles
  have originalWork (r : Fin 26) (small : r.val<17) (different : r≠1) : original r=[]:=by
    apply work (initialPrefixRoles r) small
    intro same
    exact different (initialPrefixRoles.injective (same.trans (show 1=initialPrefixRoles 1 from rfl)))
  obtain ⟨scanTime,scanBound,scanRun⟩:=initialPrefix_executes original accepted tail status originalWork
    e18 e19 e23 e24 e25 nodes values length nodeSuffix weightSuffix nodeInput weightInput
    0 0 e21 e22
  let scanned:=Function.update (Function.update (Function.update (Function.update store
    17 (Encoding.sequence Encoding.node nodes++nodeSuffix)) 20 weightSuffix)
      21 (initialRangeSum nodes true 0 values).bits) 22 (initialRangeSum nodes false 0 values).bits
  have scanning : Executes (mapRegisters initialPrefixRoles initialPrefix) store scanTime scanned:=by
    apply relocate_executes_frame initialPrefix initialPrefixRoles store scanned original
      (initialPrefixStore original nodes values 0 0 nodeSuffix weightSuffix) scanTime rfl _ _ scanRun
    · intro r
      fin_cases r <;> simp [scanned,initialPrefixStore,original,initialPrefixRoles]
    · intro r outside
      have n17 : r≠17:=by intro same;subst r;exact outside 17 rfl
      have n20 : r≠20:=by intro same;subst r;exact outside 20 rfl
      have n21 : r≠21:=by intro same;subst r;exact outside 21 rfl
      have n22 : r≠22:=by intro same;subst r;exact outside 22 rfl
      simp [scanned,n17,n20,n21,n22]
  let guardInput : Store 8:=scanned ∘ initialGuardRoles
  have guardEmpty (r : Fin 10) (large : 5 ≤ r.val) : guardInput r=[]:=by
    fin_cases r
    all_goals try norm_num at large
    all_goals simp [guardInput,initialGuardRoles,scanned,work]
  obtain ⟨guardTime,guardBound,guardRun⟩:=initialBoundsGuard_executes guardInput
    (initialRangeSum nodes true 0 values) (initialRangeSum nodes false 0 values) ell order
    (by simp [guardInput,initialGuardRoles,scanned]) (by simp [guardInput,initialGuardRoles,scanned])
    (by simp [guardInput,initialGuardRoles,scanned,leaderInput])
    (by simp [guardInput,initialGuardRoles,scanned,orderInput]) accepted tail
    (by simp [guardInput,initialGuardRoles,scanned,status]) guardEmpty
  have checking : Executes (mapRegisters initialGuardRoles initialBoundsGuard) scanned guardTime
      (initialCheckStore store accepted tail nodes values ell order nodeSuffix weightSuffix):=by
    apply relocate_executes_frame initialBoundsGuard initialGuardRoles scanned _ guardInput
      (Function.update guardInput 4 ((accepted&&initialScanCheck nodes values ell order)::tail))
      guardTime rfl _ _ guardRun
    · intro r
      fin_cases r <;> simp [guardInput,initialGuardRoles,initialCheckStore,scanned]
    · intro r outside
      have n1 : r≠1:=by intro same;subst r;exact outside 4 rfl
      simp [initialCheckStore,scanned,n1]
  have countSize:=initialRangeSum_size nodes 0 values 0 0
  simp only [Nat.zero_add,Nat.size_zero,Nat.add_zero] at countSize
  have weightLength : (Encoding.sequence Encoding.natural values).length ≤ (store 20).length:=by
    rw [weightInput]
    change _ ≤ ((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++weightSuffix).length
    simp only [List.length_append];omega
  let S:=(store 17).length+(store 20).length+ell.size+order.size+1
  change scanTime ≤ 13000*((store 17).length+(store 20).length+0+0+1)^5 at scanBound
  simp only [Nat.add_zero] at scanBound
  have scanLimit : scanTime ≤ 13000*S^5:=by
    apply scanBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 5)
  have guardLimit : guardTime ≤ 100*S:=by
    apply guardBound.trans
    exact Nat.mul_le_mul_left _ (by dsimp only [S];omega)
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 13200*S^5;omega,scanning.sequence checking⟩

theorem initialScanCheck_verifier_component (vista : Executable.Vista) (weights : Array Nat)
    (ell order : Nat) (length : weights.size=vista.nodes.size) :
    initialScanCheck vista.nodes.toList weights.toList ell order=
      decide (0<ell ∧ ell ≤ order ∧ RealizabilityVerifier.initialCount vista weights true ≤ ell ∧
        RealizabilityVerifier.initialCount vista weights false ≤ order-ell):=by
  simp only [initialScanCheck,initialBoundsCheck,initialRangeSum_vista vista weights true length,
    initialRangeSum_vista vista weights false length]

end Counting.StackMachine.RealizabilityCheck
