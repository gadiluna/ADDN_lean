import Counting.StackVistaMessages
import Counting.StackRoutineClean

namespace Counting.StackMachine.DagUpdate.Receive
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def messagesInput (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) : List Bool :=
  Encoding.frame ((Encoding.array Encoding.node).encode state.1)++
    Encoding.frame ((Encoding.list edgeCodec).encode state.2)++(Encoding.list messageCodec).encode messages

def messagesOutput (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) : List Bool :=
  let next := messages.foldl Executable.mergeMessage state
  (Encoding.product (Encoding.array Encoding.node) (Encoding.list edgeCodec)).encode next

def prepareMessages : Routine 94 := sequence (ofProgram (unframeProgram 93 0 64 69))
  (sequence (ofProgram (unframeProgram 93 0 75 69))
    (sequence (move 93 0 70 69) (pushBit 71 true)))

def preparedMessages (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update (fun _=>[])
    64 ((Encoding.array Encoding.node).encode state.1))
    75 ((Encoding.list edgeCodec).encode state.2))
    70 ((Encoding.list messageCodec).encode messages)) 71 [true]

theorem prepareMessages_executes (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) :
    Executes prepareMessages (inputStore 94 (messagesInput state messages))
      (5*((Encoding.array Encoding.node).encode state.1).length+
        5*((Encoding.list edgeCodec).encode state.2).length+
        6*((Encoding.list messageCodec).encode messages).length+12)
      (preparedMessages state messages) := by
  let pool := (Encoding.array Encoding.node).encode state.1
  let edges := (Encoding.list edgeCodec).encode state.2
  let source := (Encoding.list messageCodec).encode messages
  let initial := inputStore 94 (messagesInput state messages)
  have first := unframe_canonical_executes 93 (0:Fin 96) 64 69
    (by decide) (by decide) (by decide) initial pool (Encoding.frame edges++source)
    (by simp [initial,inputStore,messagesInput,pool,edges,source,List.append_assoc]) rfl
  rw [show initial 64=[] by rfl,List.append_nil] at first
  let pooled := Function.update (Function.update initial 0 (Encoding.frame edges++source)) 64 pool
  have second := unframe_canonical_executes 93 (0:Fin 96) 75 69
    (by decide) (by decide) (by decide) pooled edges source (by simp [pooled])
    (by simp [pooled,initial,inputStore])
  rw [show pooled 75=[] by simp [pooled,initial,inputStore],List.append_nil] at second
  let parsed := Function.update (Function.update pooled 0 source) 75 edges
  have moving := move_executes 93 (0:Fin 96) 70 69 (by decide) (by decide) (by decide)
    parsed (by simp [parsed,pooled,initial,inputStore])
  rw [show parsed 0=source by simp [parsed],
    show parsed 70=[] by simp [parsed,pooled,initial,inputStore],List.append_nil] at moving
  let moved := Function.update (Function.update parsed 70 source) 0 []
  have flag := pushBit_executes (71:Fin 96) true moved
  rw [show moved 71=[] by simp [moved,parsed,pooled,initial,inputStore]] at flag
  have final : Function.update moved 71 [true]=preparedMessages state messages := by
    funext r
    by_cases r0 : r=0 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;>
      by_cases r71 : r=71 <;> by_cases r75 : r=75 <;>
      simp [preparedMessages,moved,parsed,pooled,initial,inputStore,
        r0,r64,r70,r71,r75,pool,edges,source]
  rw [final] at flag
  convert first.sequence (second.sequence (moving.sequence flag)) using 1 <;>
    first | rfl | (dsimp only [pool,edges,source];omega)

def finishMessages : Routine 94 := sequence (move 93 75 1 69)
  (sequence (move 93 64 1 69) (clear 71))

theorem finishMessages_executes (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) :
    let next := messages.foldl Executable.mergeMessage state
    Executes finishMessages (messagesResult (preparedMessages state messages) state messages [])
      (6*((Encoding.array Encoding.node).encode next.1).length+
        6*((Encoding.list edgeCodec).encode next.2).length+12)
      (outputStore 94 (messagesOutput state messages)) := by
  let next := messages.foldl Executable.mergeMessage state
  let after := messagesResult (preparedMessages state messages) state messages []
  let pool := (Encoding.array Encoding.node).encode next.1
  let edges := (Encoding.list edgeCodec).encode next.2
  have first := move_executes 93 (75:Fin 96) 1 69 (by decide) (by decide) (by decide)
    after (by simp [after,messagesResult,preparedMessages])
  rw [show after 75=edges by simp [after,messagesResult,edges,next],
    show after 1=[] by simp [after,messagesResult,preparedMessages],List.append_nil] at first
  let edged := Function.update (Function.update after 1 edges) 75 []
  have second := move_executes 93 (64:Fin 96) 1 69 (by decide) (by decide) (by decide)
    edged (by simp [edged,after,messagesResult,preparedMessages])
  rw [show edged 64=pool by simp [edged,after,messagesResult,pool,next],
    show edged 1=edges by simp [edged]] at second
  let pooled := Function.update (Function.update edged 1 (pool++edges)) 64 []
  have clearFlag := clear_executes (71:Fin 96) pooled
  rw [show pooled 71=[true] by simp [pooled,edged,after,messagesResult,preparedMessages],
    List.length_singleton] at clearFlag
  have final : Function.update pooled 71 []=outputStore 94 (messagesOutput state messages) := by
    funext r
    by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;>
      by_cases r71 : r=71 <;> by_cases r75 : r=75 <;> by_cases r76 : r=76 <;>
      simp [pooled,edged,after,messagesResult,preparedMessages,outputStore,messagesOutput,
        Encoding.product,r1,r64,r70,r71,r75,r76,pool,edges,next]
  rw [final] at clearFlag
  convert first.sequence (second.sequence clearFlag) using 1 <;>
    first | rfl | (dsimp only [pool,edges,next];omega)

def completeMessages : Routine 94 := sequence prepareMessages (sequence mergeMessages finishMessages)

def completeMessagesBudget (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) : Nat :=
  let next := messages.foldl Executable.mergeMessage state
  5*((Encoding.array Encoding.node).encode state.1).length+
    5*((Encoding.list edgeCodec).encode state.2).length+
    6*((Encoding.list messageCodec).encode messages).length+
    1820*(((Encoding.list messageCodec).encode messages).length+1)^3+
    messageLoopBudget state messages []+
    6*((Encoding.array Encoding.node).encode next.1).length+
    6*((Encoding.list edgeCodec).encode next.2).length+27

/-- Closed program for the complete compact message-import fold. Its input
is read from one binary word, and all 96 stack registers are restored empty
except for the exact output encoding in register 1. -/
theorem completeMessages_executes (state : Executable.MergeState) (messages : List (Executable.Vista×Nat)) :
    ∃ time ≤ completeMessagesBudget state messages,
      Executes completeMessages (inputStore 94 (messagesInput state messages)) time
        (outputStore 94 (messagesOutput state messages)) := by
  have prepare := prepareMessages_executes state messages
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := mergeMessages_executes (preparedMessages state messages)
    state messages [] (by simp [preparedMessages]) (by simp [preparedMessages])
    (by simp [preparedMessages]) (by simp [preparedMessages]) (by simp [preparedMessages]) (by
      intro r small n64 n70 n71
      have n75 : r≠75 := by intro eq;subst r;norm_num at small
      simp [preparedMessages,n64,n70,n71,n75])
  have finish := finishMessages_executes state messages
  refine ⟨_,?_,prepare.sequence (bodyRun.sequence finish)⟩
  simp only [preparedMessages,Function.update_of_ne (show (70:Fin 96)≠71 by decide),
    Function.update_self] at bodyBound
  dsimp only [completeMessagesBudget]
  omega

end Counting.StackMachine.DagUpdate.Receive
