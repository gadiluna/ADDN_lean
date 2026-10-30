import Counting.StackDagInternSelect
import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRelabel
import Counting.StackComparePreserving

namespace Counting.StackMachine.DagUpdate.Intern
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def parserRoles : Fin 17 ↪ Fin 32 := ⟨fun r=>⟨r.val,by have:=r.isLt;omega⟩,by
  intro a b equal
  apply Fin.ext
  exact congrArg (fun r : Fin 32=>r.val) equal⟩

def nodeParser : VerifiedParser 30 0 1 2 Executable.Node Encoding.node :=
  DagParser.node.relabel parserRoles

def equalityRoles : Fin 6 ↪ Fin 32 := ⟨![17,2,20,21,22,23],by decide⟩

def step : Routine 30 := sequence nodeParser.routine
  (sequence (Compare.preservingEquality 26 equalityRoles)
    (sequence selectMatch (clear 2)))

def stepped (store : Store 30) (query node : Executable.Node) (found : Bool)
    (suffix : List Bool) : Store 30 :=
  Function.update (Function.update (Function.update store 0 suffix) 19 [found || decide (query=node)]) 18
    (if found || decide (query=node) then store 18 else true::store 18)

theorem step_executes (store : Store 30) (query node : Executable.Node) (found : Bool)
    (suffix : List Bool)
    (source : store 0=Encoding.node.encode node++suffix)
    (queryAt : store 17=(Encoding.node.encode query).reverse)
    (status : store 1=[true]) (foundAt : store 19=[found])
    (empty : ∀ r : Fin 32,(2 ≤ r.val ∧ r.val ≤ 16) ∨ (20 ≤ r.val ∧ r.val ≤ 23) → store r=[]) :
    ∃ time ≤ 3000*((store 0).length+(store 17).length+1)^3,
      Executes step store time (stepped store query node found suffix) := by
  have work (r : Fin 32) (member : r∈nodeParser.work) : store r=[] := by
    change r∈DagParser.node.work.map parserRoles at member
    obtain ⟨small,inside,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨n0,n1,_⟩ := DagParser.node.separate small inside
    apply empty
    left
    dsimp only [parserRoles,Function.Embedding.coeFn_mk]
    have := small.isLt
    have zero : small.val≠0 := by intro eq;apply n0;exact Fin.ext eq
    have one : small.val≠1 := by intro eq;apply n1;exact Fin.ext eq
    omega
  obtain ⟨readTime,readBound,reading⟩ := nodeParser.executes store true [] status work
  rw [source,nodeParser.roundtrip] at reading
  let read := Function.update (Function.update store 0 suffix) 2 (Encoding.node.encode node).reverse
  have readAs : parseStore 0 1 2 store true [] ⟨suffix,Encoding.node.encode node,true⟩=read := by
    funext r
    by_cases r0 : r=0 <;> by_cases r1 : r=1 <;> by_cases r2 : r=2 <;>
      simp_all [parseStore,read]
  rw [readAs] at reading
  have compared := Compare.preservingEquality_executes 26 equalityRoles read
    (by simp [read,equalityRoles,empty]) (by simp [read,equalityRoles,empty])
    (by simp [read,equalityRoles,empty])
  have queryRead : read (equalityRoles 0)=(Encoding.node.encode query).reverse := by
    simp [read,equalityRoles,queryAt]
  have nodeRead : read (equalityRoles 1)=(Encoding.node.encode node).reverse := by
    simp [read,equalityRoles]
  have outputRead : read (equalityRoles 2)=[] := by simp [read,equalityRoles,empty]
  rw [queryRead,nodeRead,outputRead] at compared
  have equal : decide ((Encoding.node.encode query).reverse=(Encoding.node.encode node).reverse)=
      decide (query=node) := by simp [Encoding.node.injective.eq_iff]
  rw [equal] at compared
  let checked := Function.update read 20 [decide (query=node)]
  obtain ⟨selectTime,selectBound,selectedRun⟩ := selectMatch_executes checked found (decide (query=node))
    (by simp [checked,read,foundAt]) (by simp [checked])
  let picked := selected checked found (decide (query=node))
  have cleared := clear_executes (2:Fin 32) picked
  have pickedCode : picked 2=(Encoding.node.encode node).reverse := by
    simp [picked,selected,checked,read]
  rw [pickedCode,List.length_reverse] at cleared
  have final : Function.update picked 2 []=stepped store query node found suffix := by
    funext r
    fin_cases r <;> simp [picked,selected,checked,read,stepped,empty]
  rw [final] at cleared
  refine ⟨_,?_,reading.sequence (compared.sequence (selectedRun.sequence cleared))⟩
  have compareBound := Compare.preservingCost_le (Encoding.node.encode query).reverse
    (Encoding.node.encode node).reverse
  simp only [List.length_reverse] at compareBound
  change readTime ≤ 2029*((store 0).length+1)^3 at readBound
  have nodeSize : (Encoding.node.encode node).length ≤ (store 0).length := by
    rw [source,List.length_append]
    omega
  have querySize : (Encoding.node.encode query).length=(store 17).length := by
    rw [queryAt,List.length_reverse]
  let K := (store 0).length+(store 17).length+1
  have positive : 1 ≤ K := by omega
  have fieldsBound : (Encoding.node.encode node).length+(Encoding.node.encode query).length ≤ K := by omega
  have cube : K ≤ K^3 := Nat.le_self_pow (by decide) _
  have parserPower := Nat.pow_le_pow_left (show (store 0).length+1 ≤ K by omega) 3
  have one : 1 ≤ K^3 := one_le_pow₀ positive
  change _ ≤ 3000*K^3
  nlinarith only [readBound,parserPower,compareBound,selectBound,fieldsBound,positive,cube,one]

end Counting.StackMachine.DagUpdate.Intern
