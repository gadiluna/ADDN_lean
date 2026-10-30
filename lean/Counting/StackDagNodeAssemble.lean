import Counting.StackDagNodeLabels
import Counting.StackEmitBinary

namespace Counting.StackMachine.DagUpdate.NodeMap
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def levelEmitter : BinaryEmitterWorkspace 60 := ⟨![40,46,47,48],by decide⟩
def parentEmitter : BinaryEmitterWorkspace 60 := ⟨![45,46,47,48],by decide⟩
def degreeEmitter : BinaryEmitterWorkspace 60 := ⟨![43,46,47,48],by decide⟩

def assemble : Routine 62 := sequence (emitBinary 60 levelEmitter)
  (sequence (emitBinary 60 parentEmitter)
    (sequence (readBit 42 46) (sequence (emitBinary 60 degreeEmitter)
      (sequence (ofProgram (ListPrograms.reverseProgram 62 2 46))
        (sequence (ofProgram (ListPrograms.reverseProgram 62 46 3)) (clear 41))))))

def assembledResult (store : Store 62) (node : Executable.Node) : Store 62 :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update store 2 []) 40 []) 41 []) 42 []) 43 []) 45 []) 3 (Encoding.node.encode node)

/-- Canonical node serialization is emitted from the actual binary labels
and compact incoming list. Reversals, framing and clearing are all charged. -/
theorem assemble_executes (store : Store 62) (node : Executable.Node)
    (levelAt : store 40=node.level.bits) (parentAt : store 45=(parentNumber node).bits)
    (leaderAt : store 42=[node.leader]) (degreeAt : store 43=node.degree.bits)
    (incomingAt : store 2=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming)
    (outputEmpty : store 3=[]) (e46 : store 46=[]) (e47 : store 47=[]) (e48 : store 48=[]) :
    Executes assemble store
      (9*(node.level.bits.length+(parentNumber node).bits.length+node.degree.bits.length)+
        2*((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming).length+
        2*(Encoding.node.encode node).length+(store 41).length+35)
      (assembledResult store node) := by
  have first:=emitBinary_executes 60 levelEmitter store e47 e48
  have lv : store (levelEmitter 0)=node.level.bits := levelAt
  have le : store (levelEmitter 1)=[] := e46
  rw [lv,le,List.append_nil] at first
  let level:=Function.update (Function.update store 40 []) 46 (Encoding.frame node.level.bits).reverse
  have second:=emitBinary_executes 60 parentEmitter level (by simp [parentEmitter,level,e47]) (by simp [parentEmitter,level,e48])
  have pv : level (parentEmitter 0)=(parentNumber node).bits := by simp [level,parentEmitter,parentAt]
  have pl : level (parentEmitter 1)=(Encoding.frame node.level.bits).reverse := by simp [level,parentEmitter]
  rw [pv,pl] at second
  let parent:=Function.update (Function.update level 45 []) 46
    ((Encoding.frame (parentNumber node).bits).reverse++(Encoding.frame node.level.bits).reverse)
  have leader:=readBit_executes (42:Fin 64) 46 (by decide) parent node.leader []
    (by simp [parent,level,leaderAt])
  let led:=Function.update (Function.update parent 42 []) 46 (node.leader::parent 46)
  have fourth:=emitBinary_executes 60 degreeEmitter led
    (by simp [degreeEmitter,led,parent,level,e47]) (by simp [degreeEmitter,led,parent,level,e48])
  have dv : led (degreeEmitter 0)=node.degree.bits := by simp [degreeEmitter,led,parent,level,degreeAt]
  rw [dv] at fourth
  let degree:=Function.update (Function.update led 43 []) 46
    ((Encoding.frame node.degree.bits).reverse++led 46)
  have incoming:=reverse_executes 62 (2:Fin 64) 46 (by decide) degree
  have inputAt : degree 2=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming := by
    simp [degree,led,parent,level,incomingAt]
  rw [inputAt] at incoming
  let reversed:=Function.update (Function.update degree 2 []) 46
    (((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming).reverse++degree 46)
  have fullAt : reversed 46=(Encoding.node.encode node).reverse := by
    simp [reversed,degree,led,parent,Encoding.node,Encoding.transport,Encoding.nodeFields,Encoding.product,
      Encoding.natural,Encoding.optionalNatural,Encoding.boolean,parentNumber,List.reverse_append,List.append_assoc]
  have finish:=reverse_executes 62 (46:Fin 64) 3 (by decide) reversed
  have outAt : reversed 3=[] := by simp [reversed,degree,led,parent,level,outputEmpty]
  rw [fullAt,outAt,List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  let forward:=Function.update (Function.update reversed 46 []) 3 (Encoding.node.encode node)
  have clearing:=clear_executes (41:Fin 64) forward
  have oldAt : forward 41=store 41 := by simp [forward,reversed,degree,led,parent,level]
  rw [oldAt] at clearing
  have final : Function.update forward 41 []=assembledResult store node := by
    funext r
    fin_cases r <;> simp [forward,reversed,degree,led,parent,level,assembledResult,e46]
  rw [final] at clearing
  have ran:=first.sequence (second.sequence (leader.sequence (fourth.sequence (incoming.sequence (finish.sequence clearing)))))
  convert ran using 1 <;> first | rfl | omega

end Counting.StackMachine.DagUpdate.NodeMap
