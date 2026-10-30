import Counting.StackVistaRawRead
import Counting.StackVistaMessages
import Counting.StackDagNodeLabels
import Counting.StackRoutineClean

namespace Counting.StackMachine.DagUpdate.Raw
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev Input := Nat × Bool × Nat × Executable.Vista × List (Executable.Vista×Nat)

def inputCodec : Encoding.Codec Input := Encoding.product Encoding.natural
  (Encoding.product Encoding.boolean (Encoding.product Encoding.natural
    (Encoding.product Encoding.vista (Encoding.list Receive.messageCodec))))

def inputWord (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) : List Bool :=
  inputCodec.encode (round,leader,degree,old,messages)

def prepareLabels : Routine 94 := sequence (ofProgram (unframeProgram 93 0 80 69))
  (sequence (readBit 0 82) (sequence (ofProgram (unframeProgram 93 0 83 69)) (pushBit 71 true)))

def labelsStore (round : Nat) (leader : Bool) (degree : Nat) (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _=>[]) 0 suffix) 80 round.bits) 82 [leader]) 83 degree.bits) 71 [true]

theorem prepareLabels_executes (round : Nat) (leader : Bool) (degree : Nat) (suffix : List Bool) :
    Executes prepareLabels (inputStore 94 (Encoding.natural.encode round++
        Encoding.boolean.encode leader++Encoding.natural.encode degree++suffix))
      (5*round.bits.length+5*degree.bits.length+10)
      (labelsStore round leader degree suffix) := by
  let initial := inputStore 94 (Encoding.natural.encode round++
    Encoding.boolean.encode leader++Encoding.natural.encode degree++suffix)
  let tail := leader::(Encoding.frame degree.bits++suffix)
  have first := unframe_canonical_executes 93 (0:Fin 96) 80 69 (by decide) (by decide) (by decide)
    initial round.bits tail (by simp [initial,inputStore,tail,Encoding.natural,Encoding.boolean,List.append_assoc]) rfl
  rw [show initial 80=[] by rfl,List.append_nil] at first
  let a := Function.update (Function.update initial 0 tail) 80 round.bits
  have second := readBit_executes (0:Fin 96) 82 (by decide) a leader (Encoding.frame degree.bits++suffix)
    (by simp [a,tail])
  rw [show a 82=[] by simp [a,initial,inputStore]] at second
  let b := Function.update (Function.update a 0 (Encoding.frame degree.bits++suffix)) 82 [leader]
  have third := unframe_canonical_executes 93 (0:Fin 96) 83 69 (by decide) (by decide) (by decide)
    b degree.bits suffix (by simp [b]) (by simp [b,a,initial,inputStore])
  rw [show b 83=[] by simp [b,a,initial,inputStore],List.append_nil] at third
  let c := Function.update (Function.update b 0 suffix) 83 degree.bits
  have fourth := pushBit_executes (71:Fin 96) true c
  rw [show c 71=[] by simp [c,b,a,initial,inputStore]] at fourth
  have final : Function.update c 71 [true]=labelsStore round leader degree suffix := by
    funext r
    by_cases r0:r=0 <;> by_cases r71:r=71 <;> by_cases r80:r=80 <;>
      by_cases r82:r=82 <;> by_cases r83:r=83 <;>
      simp [labelsStore,c,b,a,initial,inputStore,r0,r71,r80,r82,r83]
  rw [final] at fourth
  convert first.sequence (second.sequence (third.sequence fourth)) using 1 <;> first | rfl | omega

def prepareNodes : Routine 94 := sequence readNodes
  (sequence (ofProgram (unframeProgram 93 0 81 69))
    (sequence (move 93 0 70 69) (pushBit 75 false)))

def preparedStore (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update
    (labelsStore round leader degree []) 64 ((Encoding.array Encoding.node).encode old.nodes))
    81 old.bottom.bits) 70 ((Encoding.list Receive.messageCodec).encode messages)) 75 [false]

def prepareBudget (round degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) : Nat :=
  let tail := Encoding.vista.encode old++(Encoding.list Receive.messageCodec).encode messages
  5*round.bits.length+5*degree.bits.length+
    Complexity.polynomial DagParser.nodes.coefficient DagParser.nodes.exponent tail.length+
    2*((Encoding.array Encoding.node).encode old.nodes).length+5*old.bottom.bits.length+
    6*((Encoding.list Receive.messageCodec).encode messages).length+23

def prepare : Routine 94 := sequence prepareLabels prepareNodes

theorem prepare_executes (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    ∃ time ≤ prepareBudget round degree old messages,
      Executes prepare (inputStore 94 (inputWord round leader degree old messages)) time
        (preparedStore round leader degree old messages) := by
  let R := (Encoding.list Receive.messageCodec).encode messages
  let tail := Encoding.vista.encode old++R
  have first := prepareLabels_executes round leader degree tail
  have inputEq : Encoding.natural.encode round++Encoding.boolean.encode leader++
      Encoding.natural.encode degree++tail=inputWord round leader degree old messages := by
    simp [inputWord,inputCodec,Encoding.product,tail,R,List.append_assoc]
  rw [inputEq] at first
  let a := labelsStore round leader degree tail
  obtain ⟨nodesTime,nodesBound,nodesRun⟩ := readNodes_executes a old.nodes
    (Encoding.natural.encode old.bottom++R)
    (by simp [a,labelsStore,tail,Encoding.vista,Encoding.transport,Encoding.product,List.append_assoc])
    (by simp [a,labelsStore]) (by simp [a,labelsStore]) (by
      intro r lo hi
      have r0:r≠0 := by intro eq;subst r;norm_num at lo
      have r71:r≠71 := by intro eq;subst r;norm_num at hi
      have r80:r≠80 := by intro eq;subst r;norm_num at hi
      have r82:r≠82 := by intro eq;subst r;norm_num at hi
      have r83:r≠83 := by intro eq;subst r;norm_num at hi
      simp [a,labelsStore,r0,r71,r80,r82,r83])
  let b := Function.update (Function.update a 0 (Encoding.natural.encode old.bottom++R))
    64 ((Encoding.array Encoding.node).encode old.nodes)
  have bottom := unframe_canonical_executes 93 (0:Fin 96) 81 69 (by decide) (by decide) (by decide)
    b old.bottom.bits R (by simp [b,Encoding.natural]) (by simp [b,a,labelsStore])
  rw [show b 81=[] by simp [b,a,labelsStore],List.append_nil] at bottom
  let c := Function.update (Function.update b 0 R) 81 old.bottom.bits
  have moved := move_executes 93 (0:Fin 96) 70 69 (by decide) (by decide) (by decide)
    c (by simp [c,b,a,labelsStore])
  rw [show c 0=R by simp [c],show c 70=[] by simp [c,b,a,labelsStore],List.append_nil] at moved
  let d := Function.update (Function.update c 70 R) 0 []
  have edge := pushBit_executes (75:Fin 96) false d
  rw [show d 75=[] by simp [d,c,b,a,labelsStore]] at edge
  have final : Function.update d 75 [false]=preparedStore round leader degree old messages := by
    funext r
    fin_cases r <;> simp [preparedStore,d,c,b,a,labelsStore,R]
  rw [final] at edge
  refine ⟨_,?_,first.sequence (nodesRun.sequence (bottom.sequence (moved.sequence edge)))⟩
  have source : a 0=tail := by simp [a,labelsStore]
  rw [source] at nodesBound
  dsimp only [prepareBudget]
  change nodesTime ≤ Complexity.polynomial DagParser.nodes.coefficient DagParser.nodes.exponent tail.length+
    2*((Encoding.array Encoding.node).encode old.nodes).length+2 at nodesBound
  dsimp only [tail,R] at *
  omega

end Counting.StackMachine.DagUpdate.Raw
