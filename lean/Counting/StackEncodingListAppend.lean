import Counting.StackRoutineUnary
import Counting.StackRoutineCopyReverse
import Counting.StackUnframeCanonical
import Counting.StackEmitBinary
import Counting.StackRoutineBasic

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def appendEmitter : BinaryEmitterWorkspace 6 := ⟨![7,8,6,9],by decide⟩
def appendItemRoles : Fin 4 ↪ Fin 10 := ⟨![1,8,4,9],by decide⟩

/-- Append a serialized item to a serialized list, with an explicit unary
count. The list, item and count remain available to the caller. -/
def appendCanonical : Routine 8 :=
  sequence (ofProgram (ListPrograms.copyProgram 7 2 6 9))
    (sequence (pushBit 6 true)
      (sequence (ofProgram (Unary.toBinaryProgram 7 6 7 9))
        (sequence (ofProgram (ListPrograms.copyProgram 7 0 4 9))
          (sequence (ofProgram (unframeProgram 7 4 5 9))
            (sequence (clear 5) (sequence (emitBinary 6 appendEmitter)
              (sequence (ofProgram (ListPrograms.reverseProgram 8 4 8))
                (sequence (copyReverse 6 appendItemRoles)
                  (ofProgram (ListPrograms.reverseProgram 8 8 3))))))))))

def appendCanonicalBudget {α : Type} (codec : Encoding.Codec α) (values : List α) (value : α) : Nat :=
  4*(values.length+1)*(values.length+2)+5*values.length+
  5*((Encoding.list codec).encode values).length+6*values.length.bits.length+
  9*(values.length+1).bits.length+2*(Encoding.sequence codec values).length+
  7*(codec.encode value).length+2*((Encoding.list codec).encode (values++[value])).length+32

theorem sequence_append_one {α : Type} (codec : Encoding.Codec α) (values : List α) (value : α) :
    Encoding.sequence codec (values++[value])=Encoding.sequence codec values++codec.encode value := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons head tail ih => simp [Encoding.sequence,ih,List.append_assoc]

theorem appendCanonical_executes {α : Type} (codec : Encoding.Codec α)
    (values : List α) (value : α) (store : Store 8)
    (source : store 0=(Encoding.list codec).encode values) (item : store 1=codec.encode value)
    (count : store 2=List.replicate values.length true)
    (empty : ∀ r : Fin 10,3 ≤ r.val → store r=[]) :
    ∃ time ≤ appendCanonicalBudget codec values value,
      Executes appendCanonical store time
        (Function.update store 3 ((Encoding.list codec).encode (values++[value]))) := by
  have copyingCount := copy_executes 7 (2:Fin 10) 6 9 (by decide) (by decide) (by decide)
    store (empty 9 (by decide))
  rw [count,empty 6 (by decide),List.append_nil,List.length_replicate] at copyingCount
  let copiedCount := Function.update store 6 (List.replicate values.length true)
  have pushed := pushBit_executes (6:Fin 10) true copiedCount
  let increased := Function.update store 6 (List.replicate (values.length+1) true)
  have pushedResult : Function.update copiedCount 6 (true::copiedCount 6)=increased := by
    simp [copiedCount,increased,List.replicate_succ]
  rw [pushedResult] at pushed
  obtain ⟨binaryTime,binaryBound,binaryRun⟩ := toBinary_executes 7 (6:Fin 10) 7 9
    (by decide) (by decide) (by decide) increased 0
    (by simp [increased,empty]) (by simp [increased,empty])
  have counterAt : increased 6=List.replicate (values.length+1) true := by simp [increased]
  rw [counterAt,List.length_replicate,Nat.zero_add] at binaryRun binaryBound
  let binary := Function.update store 7 (values.length+1).bits
  have binaryResult : Function.update (Function.update increased 6 []) 7 (values.length+1).bits=binary := by
    simp [increased,binary,←empty 6 (by decide)]
  rw [binaryResult] at binaryRun
  have copyingInput := copy_executes 7 (0:Fin 10) 4 9 (by decide) (by decide) (by decide)
    binary (by simp [binary,empty])
  have original : binary 0=(Encoding.list codec).encode values := by simp [binary,source]
  have bufferEmpty : binary 4=[] := by simp [binary,empty]
  rw [original,bufferEmpty,List.append_nil] at copyingInput
  let copiedInput := Function.update binary 4 ((Encoding.list codec).encode values)
  have unframed := unframe_canonical_executes 7 (4:Fin 10) 5 9 (by decide) (by decide) (by decide)
    copiedInput values.length.bits (Encoding.sequence codec values)
    (by rfl) (by simp [copiedInput,binary,empty])
  have oldHeaderEmpty : copiedInput 5=[] := by simp [copiedInput,binary,empty]
  rw [oldHeaderEmpty,List.append_nil] at unframed
  let parsed := Function.update (Function.update copiedInput 4 (Encoding.sequence codec values)) 5 values.length.bits
  have clearing := clear_executes (5:Fin 10) parsed
  have headerAt : parsed 5=values.length.bits := by simp [parsed]
  rw [headerAt] at clearing
  let cleaned := Function.update parsed 5 []
  have emitted := emitBinary_executes 6 appendEmitter cleaned
    (by simp [appendEmitter,cleaned,parsed,copiedInput,binary,empty])
    (by simp [appendEmitter,cleaned,parsed,copiedInput,binary,empty])
  have newHeader : cleaned (appendEmitter 0)=(values.length+1).bits := by
    simp [appendEmitter,cleaned,parsed,copiedInput,binary]
  have reversedEmpty : cleaned (appendEmitter 1)=[] := by
    simp [appendEmitter,cleaned,parsed,copiedInput,binary,empty]
  rw [newHeader,reversedEmpty,List.append_nil] at emitted
  let header := Function.update (Function.update cleaned 7 []) 8 (Encoding.frame (values.length+1).bits).reverse
  have stream := reverse_executes 8 (4:Fin 10) 8 (by decide) header
  have streamAt : header 4=Encoding.sequence codec values := by
    simp [header,cleaned,parsed]
  rw [streamAt] at stream
  let streamed := Function.update (Function.update header 4 []) 8
    ((Encoding.sequence codec values).reverse++header 8)
  have appending := copyReverse_executes 6 appendItemRoles streamed
    (by simp [appendItemRoles,streamed])
    (by simp [appendItemRoles,streamed,header,cleaned,parsed,copiedInput,binary,empty])
  have itemAt : streamed (appendItemRoles 0)=codec.encode value := by
    simp [appendItemRoles,streamed,header,cleaned,parsed,copiedInput,binary,item]
  rw [itemAt] at appending
  let appended := Function.update streamed 8 ((codec.encode value).reverse++streamed 8)
  have appendedStream : Encoding.sequence codec (values++[value])=
      Encoding.sequence codec values++codec.encode value := sequence_append_one codec values value
  have complete : appended 8=((Encoding.list codec).encode (values++[value])).reverse := by
    simp [appended,streamed,header,Encoding.list,Encoding.natural,appendedStream,
      List.reverse_append,List.append_assoc]
  have finishing := reverse_executes 8 (8:Fin 10) 3 (by decide) appended
  have outputEmpty : appended 3=[] := by
    simp [appended,streamed,header,cleaned,parsed,copiedInput,binary,empty]
  rw [complete,outputEmpty,List.length_reverse,List.reverse_reverse,List.append_nil] at finishing
  have final : Function.update (Function.update appended 8 []) 3
      ((Encoding.list codec).encode (values++[value]))=
      Function.update store 3 ((Encoding.list codec).encode (values++[value])) := by
    funext r
    fin_cases r <;> simp [appended,streamed,header,cleaned,parsed,copiedInput,binary,empty]
  rw [final] at finishing
  refine ⟨_,?_,copyingCount.sequence (pushed.sequence (binaryRun.sequence
    (copyingInput.sequence (unframed.sequence (clearing.sequence (emitted.sequence
      (stream.sequence (appending.sequence finishing))))))))⟩
  dsimp only [appendCanonicalBudget]
  simp only [Nat.add_assoc,Nat.reduceAdd] at binaryBound
  omega

end Counting.StackMachine.EncodingPrograms
