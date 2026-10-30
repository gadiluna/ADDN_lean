import Counting.StackAuditPrefixCountPositive

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev classifyCount : Routine 34 := sequence (DagValidation.emptyFlag 29 31)
  (sequence (negateFlag 34 31)
    (sequence (ofProgram (ListPrograms.copyProgram 33 31 33 4))
      (sequence (discardBit 29)
        (sequence (DagValidation.emptyFlag 29 33)
          (sequence (ofProgram (combineFlagsProgram 34 33)) (clear 29))))))

/-- Classify a physical unary tally as nonempty and singleton. Only one
bit is popped before the second test; the remaining tally is erased. -/
theorem classifyCount_executes (store : Store 34) (amount : Nat)
    (tally : store 29=List.replicate amount true)
    (e4 : store 4=[]) (e31 : store 31=[]) (e33 : store 33=[]) :
    ∃ time ≤ amount+30,Executes classifyCount store time
      (Function.update (Function.update (Function.update store 29 []) 31 [decide (0<amount)])
        33 [decide (amount=1)]) := by
  have a:=DagValidation.emptyFlag_executes (29:Fin 36) 31 store
  rw [tally,e31] at a
  simp only [List.replicate_eq_nil_iff] at a
  let tested:=Function.update store 31 [decide (amount=0)]
  have b:=negateFlag_executes 34 (31:Fin 36) tested (decide (amount=0)) [] (by simp [tested])
  have positive : (!decide (amount=0))=decide (0<amount) := by simp [Nat.pos_iff_ne_zero]
  rw [positive] at b
  let marked:=Function.update store 31 [decide (0<amount)]
  have bResult : Function.update tested 31 [decide (0<amount)]=marked := by simp [tested,marked]
  rw [bResult] at b
  have c:=copy_executes 33 (31:Fin 36) 33 4 (by decide) (by decide) (by decide) marked
    (by simp [marked,e4])
  have marker : marked 31=[decide (0<amount)] := by simp [marked]
  have empty33 : marked 33=[] := by simp [marked,e33]
  rw [marker,empty33,List.append_nil] at c
  let copied:=Function.update marked 33 [decide (0<amount)]
  have d:=discardBit_executes (29:Fin 36) copied
  have beforeTail : copied 29=List.replicate amount true := by simp [copied,marked,tally]
  rw [beforeTail] at d
  let rest:=(List.replicate amount true).tail
  let shortened:=Function.update copied 29 rest
  have e:=DagValidation.emptyFlag_executes (29:Fin 36) 33 shortened
  have remaining : shortened 29=rest := by simp [shortened]
  have firstFlag : shortened 33=[decide (0<amount)] := by simp [shortened,copied]
  rw [remaining,firstFlag] at e
  let second:=Function.update shortened 33 [decide (rest=[]),decide (0<amount)]
  have f:=combineFlags_executes 34 (33:Fin 36) second (decide (0<amount)) (decide (rest=[])) []
    (by simp [second])
  have classification : (decide (0<amount) && decide (rest=[]))=decide (amount=1) := by
    cases amount with
    | zero=>simp [rest]
    | succ amount=>cases amount <;> simp [rest,List.replicate_succ]
  rw [classification] at f
  let classified:=Function.update shortened 33 [decide (amount=1)]
  have fResult : Function.update second 33 [decide (amount=1)]=classified := by simp [second,classified]
  rw [fResult] at f
  have g:=clear_executes (29:Fin 36) classified
  have restAt : classified 29=rest := by simp [classified,shortened]
  rw [restAt] at g
  have final : Function.update classified 29 []=
      Function.update (Function.update (Function.update store 29 []) 31 [decide (0<amount)])
        33 [decide (amount=1)] := by
    funext r
    by_cases a:r=29 <;> by_cases b:r=31 <;> by_cases c:r=33 <;>
      simp [classified,shortened,copied,marked,a,b,c]
  rw [final] at g
  have firstCost : DagValidation.emptyFlagCost (List.replicate amount true)≤3 := by
    unfold DagValidation.emptyFlagCost;split <;> omega
  have secondCost : DagValidation.emptyFlagCost rest≤3 := by
    unfold DagValidation.emptyFlagCost;split <;> omega
  have restLength : rest.length≤amount := by
    dsimp only [rest]
    simp only [List.length_tail,List.length_replicate]
    omega
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence g)))))⟩
  simp only [List.length_cons,List.length_nil]
  omega

abbrev countClassify (mode : HeaderMode) : Routine 34 := sequence (countAll mode) classifyCount

theorem countClassify_executes (mode : HeaderMode) (vista : Executable.Vista)
    (store : Store 34) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (level parent : Nat) (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ 21000*((store 17).length+level.size+parent.size+1)^5,
      Executes (countClassify mode) store time
        (Function.update (Function.update store 31
          [decide (0<countRange vista mode level parent 0 vista.nodes.size)])
          33 [decide (countRange vista mode level parent 0 vista.nodes.size=1)]) := by
  obtain ⟨countTime,countBound,a⟩:=countAll_executes mode vista store accepted tail status work
    e18 e19 e28 e31 e33 e34 e35 suffix input nodeCount level parent levelAt parentAt
  rw [e29,List.append_nil] at a
  let amount:=countRange vista mode level parent 0 vista.nodes.size
  let counted:=Function.update store 29 (List.replicate amount true)
  obtain ⟨classifyTime,classifyBound,b⟩:=classifyCount_executes counted amount (by simp [counted])
    (by simp [counted,work]) (by simp [counted,e31]) (by simp [counted,e33])
  have final : Function.update (Function.update (Function.update counted 29 []) 31 [decide (0<amount)])
      33 [decide (amount=1)]=Function.update (Function.update store 31 [decide (0<amount)])
      33 [decide (amount=1)] := by
    simp only [counted,Function.update_idem]
    rw [←e29,Function.update_eq_self]
  rw [final] at b
  have amountBound : amount≤vista.nodes.size:=countRange_le vista mode level parent 0 vista.nodes.size
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  have countSize : vista.nodes.size≤(store 17).length := by
    rw [input,List.length_append];simp only [Array.length_toList] at nodes;omega
  let S:=(store 17).length+level.size+parent.size+1
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have one : 1≤S^5:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  refine ⟨_,?_,a.sequence b⟩
  change countTime+1+classifyTime≤21000*S^5
  dsimp only [S] at linear one ⊢
  omega

end Counting.StackMachine.AuditPrefix
