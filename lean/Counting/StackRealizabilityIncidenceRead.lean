import Counting.StackRealizabilityNodeIncidence
import Counting.StackEncodingDagReadPreserving
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def incidenceFile (source index query incoming parent status : List Bool) : Store 40:=
  fun r=>if r=21 then query else if r=22 then incoming else if r=34 then status
    else if r=35 then source else if r=36 then index else if r=37 then parent else []

def incidenceReadRoles : Fin 20 ↪ Fin 42:=⟨![1,34,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,35,36,0],by decide⟩
def incidenceBodyRoles : Fin 34 ↪ Fin 42 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r : Fin 42=>r.val) same

def incidenceRead : Routine 40:=mapRegisters incidenceReadRoles DagParser.preservingNodeRead
def incidenceBody : Routine 40:=mapRegisters incidenceBodyRoles nodeIncidence

theorem incidenceRead_executes (source index query incoming parent : List Bool)
    (accepted : Bool) (tail : List Bool) (nodes : List Executable.Node) (position : Fin nodes.length)
    (suffix : List Bool) (input : source=Encoding.sequence Encoding.node nodes++suffix)
    (indexAt : index.length=position.val) :
    ∃ time ≤ 7000*(source.length+1)^4,
      Executes incidenceRead (incidenceFile source index query incoming parent (accepted::tail)) time
        (Function.update (incidenceFile source index query incoming parent (accepted::tail)) 0
          (Encoding.node.encode nodes[position])):=by
  let original : Store 18:=incidenceFile source index query incoming parent (accepted::tail) ∘ incidenceReadRoles
  have workspace (r : Fin 17) (different : r≠1) : original (DagParser.nodeRoles r)=[]:=by
    fin_cases r <;> simp_all [original,incidenceFile,incidenceReadRoles,DagParser.nodeRoles]
  obtain ⟨time,bound,run⟩:=DagParser.preservingNodeRead_get original accepted tail
    (by simp [original,incidenceFile,incidenceReadRoles]) workspace
    (by simp [original,incidenceFile,incidenceReadRoles]) nodes position suffix
    (by simpa [original,incidenceFile,incidenceReadRoles] using input)
    (by simpa [original,incidenceFile,incidenceReadRoles] using indexAt)
  have execution : Executes incidenceRead (incidenceFile source index query incoming parent (accepted::tail)) time
      (Function.update (incidenceFile source index query incoming parent (accepted::tail)) 0
        (Encoding.node.encode nodes[position])):=by
    apply relocate_executes_frame DagParser.preservingNodeRead incidenceReadRoles _ _ original _ time rfl _ _ run
    · intro r;fin_cases r <;> simp [original,incidenceReadRoles]
    · intro r outside
      have different : r≠0:=by intro same;subst r;exact outside 19 rfl
      simp [different]
  change time≤(2*index.length+3)*2029*(source.length+1)^3+6*source.length+7*index.length+14 at bound
  have count:=DagValidation.node_sequence_count_le nodes
  have indexBound : index.length ≤ source.length:=by
    rw [input,List.length_append,indexAt]
    have inside:=position.isLt
    omega
  let S:=source.length+1
  have factor : 2*index.length+3≤3*S:=by dsimp only [S];omega
  have leading : (2*index.length+3)*2029*(source.length+1)^3≤6087*S^4:=by
    calc _≤(3*S)*2029*S^3:=by gcongr
         _=_:=by ring
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  have one : 1≤S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨time,by change time≤7000*S^4;dsimp only [S] at leading linear one ⊢;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
