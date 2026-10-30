import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Read one binary multiplicity and emit exactly its positivity bit. The
binary payload is consumed once, with no unary arc expansion. -/
def arcBit : Routine 2 := sequence (ofProgram (unframeProgram 1 0 2 3))
  (sequence (DagValidation.emptyFlag 2 1) (sequence (negateFlag 2 1) (clear 2)))

def arcBitStore (store : Store 2) (value : Nat) (suffix : List Bool) : Store 2 :=
  Function.update (Function.update store 0 suffix) 1 (decide (0<value)::store 1)

theorem arcBit_executes (store : Store 2) (value : Nat) (suffix : List Bool)
    (input : store 0=Encoding.natural.encode value++suffix) (e2 : store 2=[]) (e3 : store 3=[]) :
    ∃time ≤ 6*value.size+11, Executes arcBit store time (arcBitStore store value suffix) := by
  have parsing := unframe_canonical_executes 1 (0:Fin 4) 2 3
    (by decide) (by decide) (by decide) store value.bits suffix input e3
  rw [e2,List.append_nil] at parsing
  let parsed := Function.update (Function.update store 0 suffix) 2 value.bits
  have checking := DagValidation.emptyFlag_executes (2:Fin 4) 1 parsed
  rw [show parsed 2=value.bits by simp [parsed],show parsed 1=store 1 by simp [parsed]] at checking
  let flagged := Function.update parsed 1 (decide (value.bits=[])::store 1)
  have negating := negateFlag_executes 2 1 flagged (decide (value.bits=[])) (store 1) (by simp [flagged])
  have zero : value.bits=[] ↔ value=0 := by
    constructor
    · intro empty
      have evaluated := congrArg Encoding.value empty
      simpa only [Encoding.value_bits,Encoding.value] using evaluated
    · intro equal;subst value;rfl
  have positive : (!decide (value.bits=[]))=decide (0<value) := by simp [zero,Nat.pos_iff_ne_zero]
  simp only [flagged,Function.update_idem,positive] at negating
  let checked := Function.update parsed 1 (decide (0<value)::store 1)
  have clearing := clear_executes (2:Fin 4) checked
  rw [show checked 2=value.bits by simp [checked,parsed],Encoding.bits_length] at clearing
  have final : Function.update checked 2 []=arcBitStore store value suffix := by
    funext i
    fin_cases i <;> simp [checked,parsed,arcBitStore,e2]
  rw [final] at clearing
  have small : DagValidation.emptyFlagCost value.bits ≤ 3 := by
    unfold DagValidation.emptyFlagCost
    split_ifs <;> omega
  refine ⟨_,?_,parsing.sequence (checking.sequence (negating.sequence clearing))⟩
  rw [Encoding.bits_length]
  omega

end Counting.StackMachine.NetworkRecognition
