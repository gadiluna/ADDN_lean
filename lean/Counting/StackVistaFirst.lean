import Counting.NetworkVistaParse
import Counting.StackEncodingDagParser
import Counting.StackUnframeCanonical
import Counting.StackRoutineClean
import Counting.StackRoutineMove
import Counting.EncodingRecognitionBounds

namespace Counting.StackMachine.VistaFirst
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def inputWord (first : Executable.Vista) (rest : List Executable.Vista) : List Bool :=
  (Encoding.list Encoding.vista).encode (first::rest)

def outputWord (first : Executable.Vista) : List Bool :=
  Encoding.vistaInput.encode (first, 1)

def prepared (first : Executable.Vista) (rest : List Executable.Vista) : Store 18 :=
  Function.update (Function.update (fun _ => []) 1 [true]) 17
    (Encoding.vista.encode first++Encoding.sequence Encoding.vista rest)

def prepare : Routine 18 := sequence (ofProgram (unframeProgram 17 0 16 3))
  (sequence (clear 16) (sequence (move 17 0 17 3) (pushBit 1 true)))

theorem prepare_executes (first : Executable.Vista) (rest : List Executable.Vista) :
    ∃ time ≤ 20*((inputWord first rest).length+1),
      Executes prepare (inputStore 18 (inputWord first rest)) time (prepared first rest) := by
  let start := inputStore 18 (inputWord first rest)
  let count := (first::rest).length.bits
  let payload := Encoding.vista.encode first++Encoding.sequence Encoding.vista rest
  have reading := unframe_canonical_executes 17 (0 : Fin 20) 16 3
    (by decide) (by decide) (by decide) start count payload rfl rfl
  rw [show start 16=[] by rfl, List.append_nil] at reading
  let parsed := Function.update (Function.update start 0 payload) 16 count
  have clearing := clear_executes (16 : Fin 20) parsed
  rw [show parsed 16=count by simp [parsed]] at clearing
  let cleaned := Function.update parsed 16 []
  have moving := move_executes 17 (0 : Fin 20) 17 3
    (by decide) (by decide) (by decide) cleaned (by simp [cleaned, parsed, start, inputStore])
  rw [show cleaned 0=payload by simp [cleaned, parsed],
    show cleaned 17=[] by simp [cleaned, parsed, start, inputStore], List.append_nil] at moving
  let moved := Function.update (Function.update cleaned 17 payload) 0 []
  have flag := pushBit_executes (1 : Fin 20) true moved
  rw [show moved 1=[] by simp [moved, cleaned, parsed, start, inputStore]] at flag
  have final : Function.update moved 1 [true] = prepared first rest := by
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> by_cases r16:r=16 <;> by_cases r17:r=17 <;>
      simp [moved, cleaned, parsed, start, inputStore, prepared, payload, r0, r1, r16, r17]
  rw [final] at flag
  refine ⟨_, ?_, reading.sequence (clearing.sequence (moving.sequence flag))⟩
  have length : (inputWord first rest).length=2*count.length+1+payload.length := by
    simp only [inputWord, Encoding.list, Encoding.natural, List.length_append,
      Encoding.frame_length, Encoding.sequence, count, payload]
  omega

def afterParse (first : Executable.Vista) (rest : List Executable.Vista) : Store 18 :=
  Function.update (Function.update (prepared first rest) 17 (Encoding.sequence Encoding.vista rest))
    19 (Encoding.vista.encode first)

theorem parse_executes (first : Executable.Vista) (rest : List Executable.Vista) :
    ∃ time ≤ 11670*((inputWord first rest).length+1)^4+2,
      Executes (NetworkVista.Forward.parseForward DagParser.vista) (prepared first rest) time
        (afterParse first rest) := by
  obtain ⟨time, bound, run⟩ := NetworkVista.Forward.parseForward_canonical DagParser.vista
    (prepared first rest) true [] (by simp [prepared])
    (by
      intro r member
      have separate := (NetworkVista.Forward.wideParser DagParser.vista).separate r member
      simp only [prepared, Function.update_of_ne separate.1, Function.update_of_ne separate.2.1])
    (by simp [prepared]) (by simp [prepared]) first (Encoding.sequence Encoding.vista rest)
    (by simp [prepared])
  refine ⟨time, ?_, run⟩
  change time ≤ 3*(3890*((prepared first rest 17).length+1)^4)+2 at bound
  have size : (prepared first rest 17).length ≤ (inputWord first rest).length := by
    simp only [prepared, Function.update_self, inputWord, Encoding.list, Encoding.sequence,
      List.length_append]
    omega
  calc
    time ≤ 3*(3890*((prepared first rest 17).length+1)^4)+2 := bound
    _ = 11670*((prepared first rest 17).length+1)^4+2 := by ring
    _ ≤ _ := by gcongr

def finish : Routine 18 := sequence (clear 17) (sequence (clear 1)
  (sequence (prepend 1 (Encoding.natural.encode 1)) (move 17 19 1 3)))

theorem finish_executes (first : Executable.Vista) (rest : List Executable.Vista) :
    ∃ time ≤ 10*((inputWord first rest).length+1)+20,
      Executes finish (afterParse first rest) time (outputStore 18 (outputWord first)) := by
  let start := afterParse first rest
  have clearTail := clear_executes (17 : Fin 20) start
  rw [show start 17=Encoding.sequence Encoding.vista rest by simp [start, afterParse]] at clearTail
  let noTail := Function.update start 17 []
  have clearFlag := clear_executes (1 : Fin 20) noTail
  rw [show noTail 1=[true] by simp [noTail, start, afterParse, prepared], List.length_singleton] at clearFlag
  let cleaned := Function.update noTail 1 []
  have leader := prepend_executes (1 : Fin 20) (Encoding.natural.encode 1) cleaned
  rw [show cleaned 1=[] by simp [cleaned], List.append_nil] at leader
  let marked := Function.update cleaned 1 (Encoding.natural.encode 1)
  have moving := move_executes 17 (19 : Fin 20) 1 3
    (by decide) (by decide) (by decide) marked
    (by simp [marked, cleaned, noTail, start, afterParse, prepared])
  rw [show marked 19=Encoding.vista.encode first by simp [marked, cleaned, noTail, start, afterParse],
    show marked 1=Encoding.natural.encode 1 by simp [marked]] at moving
  have final : Function.update (Function.update marked 1
      (Encoding.vista.encode first++Encoding.natural.encode 1)) 19 [] =
      outputStore 18 (outputWord first) := by
    funext r
    by_cases r1:r=1 <;> by_cases r17:r=17 <;> by_cases r19:r=19 <;>
      simp [marked, cleaned, noTail, start, afterParse, prepared, outputStore,
        outputWord, Encoding.vistaInput, Encoding.product, r1, r17, r19]
  rw [final] at moving
  refine ⟨_, ?_, clearTail.sequence (clearFlag.sequence (leader.sequence moving))⟩
  have size : (Encoding.vista.encode first).length+(Encoding.sequence Encoding.vista rest).length ≤
      (inputWord first rest).length := by
    simp only [inputWord, Encoding.list, Encoding.sequence, List.length_append]
    omega
  rw [Encoding.natural_length, Nat.size_one]
  omega

/-- A closed finite routine selects observer zero from a nonempty compact
configuration and emits the exact one-leader vista input. All work is erased. -/
def complete : Routine 18 := sequence prepare
  (sequence (NetworkVista.Forward.parseForward DagParser.vista) finish)

theorem complete_executes (first : Executable.Vista) (rest : List Executable.Vista) :
    ∃ time ≤ 12000*((inputWord first rest).length+1)^4,
      Executes complete (inputStore 18 (inputWord first rest)) time
        (outputStore 18 (outputWord first)) := by
  obtain ⟨prepareTime, prepareBound, prepareRun⟩ := prepare_executes first rest
  obtain ⟨parseTime, parseBound, parseRun⟩ := parse_executes first rest
  obtain ⟨finishTime, finishBound, finishRun⟩ := finish_executes first rest
  refine ⟨_, ?_, prepareRun.sequence (parseRun.sequence finishRun)⟩
  have power : (inputWord first rest).length+1 ≤ ((inputWord first rest).length+1)^4 :=
    Nat.le_self_pow (by decide) _
  omega

end Counting.StackMachine.VistaFirst
