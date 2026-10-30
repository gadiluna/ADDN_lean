import Counting.StackAuditPrefixHeader

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

inductive HeaderMode where
  | level
  | child
  | leader
  deriving DecidableEq,Repr

def headerPredicate : HeaderMode → Bool → Bool → Bool → Bool
  | .level,atLevel,_,_=>atLevel
  | .child,atLevel,parent,_=>atLevel && parent
  | .leader,atLevel,_,leader=>atLevel && leader

/-- A four-transition Boolean decision, consuming all three temporary
header flags and retaining the destination's existing suffix. -/
def headerDecisionProgram (mode : HeaderMode) : Program where
  extraRegisters:=34
  states:=8
  code control:=match control.val with
    | 0=>.pop 31 1 1 2
    | 1=>.pop 33 3 3 3
    | 2=>match mode with
      | .level=>.pop 33 4 4 4
      | .child=>.pop 33 3 3 4
      | .leader=>.pop 33 7 7 7
    | 3=>.pop 34 5 5 5
    | 4=>.pop 34 6 6 6
    | 5=>.push 35 false 8
    | 6=>.push 35 true 8
    | 7=>.pop 34 5 5 6
    | _=>.halt

def decisionStore (store : Store 34) (mode : HeaderMode) (level parent leader : Bool) : Store 34 :=
  Function.update (Function.update (Function.update (Function.update store 31 []) 33 []) 34 [])
    35 (headerPredicate mode level parent leader::store 35)

theorem headerDecision_executes (mode : HeaderMode) (store : Store 34)
    (level parent leader : Bool) (l : store 31=[level]) (p : store 33=[parent])
    (h : store 34=[leader]) :
    Executes (ofProgram (headerDecisionProgram mode)) store 4
      (decisionStore store mode level parent leader) := by
  refine ⟨⟨8,decisionStore store mode level parent leader⟩,?_,rfl,rfl⟩
  cases mode <;> cases level <;> cases parent <;> cases leader <;>
    simp [Machine.run,step,headerDecisionProgram,decisionStore,headerPredicate,l,p,h]

def nodeMatches (mode : HeaderMode) (node : Executable.Node) (level parent : Nat) : Bool :=
  headerPredicate mode (decide (node.level=level))
    (decide (DagValidation.parentCode node=parent)) node.leader

abbrev selectNode (mode : HeaderMode) : Routine 34 :=
  sequence headerTests (ofProgram (headerDecisionProgram mode))

/-- Exact level, child, or leader selection of the actual indexed node.
No validity hypothesis on the DAG is needed to inspect these fields. -/
theorem selectNode_executes (mode : HeaderMode) (store : Store 34)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[])
    (nodes : List Executable.Node) (index : Fin nodes.length) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : (store 18).length=index.val) (level parent : Nat)
    (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ 10010*((store 17).length+level.size+parent.size+1)^4,
      Executes (selectNode mode) store time
        (Function.update store 35 (nodeMatches mode nodes[index] level parent::store 35)) := by
  obtain ⟨time,bound,a⟩:=headerTests_executes store accepted tail status work e19 nodes index suffix
    input counter level parent levelAt parentAt
  let node:=nodes[index]
  let tested:=Function.update (Function.update (Function.update store 31
    (decide (node.level=level)::store 31)) 33
    (decide (DagValidation.parentCode node=parent)::store 33)) 34 (node.leader::store 34)
  have b:=headerDecision_executes mode tested (decide (node.level=level))
    (decide (DagValidation.parentCode node=parent)) node.leader
    (by simp [tested,e31]) (by simp [tested,e33]) (by simp [tested,e34])
  have final : decisionStore tested mode (decide (node.level=level))
      (decide (DagValidation.parentCode node=parent)) node.leader=
      Function.update store 35 (nodeMatches mode node level parent::store 35) := by
    funext r
    fin_cases r <;> simp [decisionStore,tested,nodeMatches,e31,e33,e34]
  rw [final] at b
  refine ⟨time+1+4,?_,a.sequence b⟩
  have positive : 1 ≤ ((store 17).length+level.size+parent.size+1)^4 :=
    Nat.one_le_pow _ _ (by omega)
  omega

end Counting.StackMachine.AuditPrefix
