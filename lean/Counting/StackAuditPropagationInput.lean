import Counting.StackAuditPropagationInputRead
import Counting.StackAuditPropagationZero
import Counting.StackEncodingListReadHeader
import Counting.StackRegisterFrames
import Counting.EncodingVerifier

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def propagationZeroRoles : Fin 6 ↪ Fin 44 := ⟨![40,35,2,3,4,5],by decide⟩
abbrev allocatePropagationZeros : Routine 42 := relocate zeroArray propagationZeroRoles

theorem allocatePropagationZeros_executes (store : Store 42) (n : Nat)
    (source : store 40=List.replicate n true)
    (empty : ∀ i : Fin 6,i≠0 → store (propagationZeroRoles i)=[]) :
    ∃ time ≤ 80*(n+1)^2,
      Executes allocatePropagationZeros store time
        (Function.update store 35 ((Encoding.array Encoding.natural).encode (Array.replicate n 0))) := by
  let localStore:Store 4:=store ∘ propagationZeroRoles
  obtain ⟨time,bound,run⟩:=zeroArray_executes localStore n source empty
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame zeroArray propagationZeroRoles _ _ _ _ time rfl _ _ run
  · intro i;fin_cases i <;> simp [localStore,propagationZeroRoles]
  · intro r outside
    have different : r≠35 := by intro equal;subst r;exact outside 1 rfl
    simp [different]

def propagationHeaderRoles : FullListWorkspace 27 :=
  ⟨![17,1,2,3,40,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

def propagationSetupFile (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : Store 42 :=
  let parsed:=propagationInputFile [] anchor.bits (Encoding.vista.encode vista)
    (Encoding.sequence Encoding.natural values.toList) []
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update parsed 1 [true]) 17
      (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom))
    40 (List.replicate vista.nodes.size true)) 30 anchor.bits) 32 (List.replicate vista.nodes.size true))
    35 ((Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0))

abbrev setupPropagationInput : Routine 42 := sequence (pushBit 1 true)
  (sequence (ofProgram (ListPrograms.copyProgram 41 34 17 43))
    (sequence (readListHeader 27 propagationHeaderRoles)
      (sequence (ofProgram (ListPrograms.copyProgram 41 42 30 43))
        (sequence (ofProgram (ListPrograms.copyProgram 41 40 32 43)) allocatePropagationZeros))))

/-- Materialize both bounded node counters, the untouched full vista,
its scan table and the actual zero-weight array, with full-store cleanup. -/
theorem setupPropagationInput_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) :
    ∃ time ≤ 4000*((Encoding.vista.encode vista).length+anchor.size+1)^3,
      Executes setupPropagationInput
        (propagationInputFile [] anchor.bits (Encoding.vista.encode vista)
          (Encoding.sequence Encoding.natural values.toList) []) time
        (propagationSetupFile anchor vista values) := by
  let parsed:=propagationInputFile [] anchor.bits (Encoding.vista.encode vista)
    (Encoding.sequence Encoding.natural values.toList) []
  let flagged:=Function.update parsed 1 [true]
  have a:=pushBit_executes (1:Fin 44) true parsed
  change Executes _ parsed 1 flagged at a
  have b:=copy_executes 41 (34:Fin 44) 17 43 (by decide) (by decide) (by decide) flagged
    (by simp [flagged,parsed,propagationInputFile])
  have source : flagged 34=Encoding.vista.encode vista := by simp [flagged,parsed,propagationInputFile]
  have target : flagged 17=[] := by simp [flagged,parsed,propagationInputFile]
  rw [source,target,List.append_nil] at b
  let copied:=Function.update flagged 17 (Encoding.vista.encode vista)
  obtain ⟨headerTime,headerBound,c⟩:=readListHeader_canonical 27 propagationHeaderRoles copied true []
    (by simp [copied,flagged,propagationHeaderRoles])
    (by intro i member;fin_cases i <;> simp_all [copied,flagged,parsed,propagationInputFile,propagationHeaderRoles])
    Encoding.node (by intro node;have positive:=Encoding.node_positive_length node;omega)
    vista.nodes.toList (Encoding.natural.encode vista.bottom)
    (by simp only [copied,propagationHeaderRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,
      Function.update_self];rfl)
  let table:=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  let counted:=Function.update (Function.update flagged 17 table) 40 (List.replicate vista.nodes.size true)
  have cResult : Function.update (Function.update copied (propagationHeaderRoles 0) table)
      (propagationHeaderRoles 4) (List.replicate vista.nodes.toList.length true)=counted := by
    simp [copied,counted,propagationHeaderRoles]
  rw [cResult] at c
  have d:=copy_executes 41 (42:Fin 44) 30 43 (by decide) (by decide) (by decide) counted
    (by simp [counted,flagged,parsed,propagationInputFile])
  have anchorSource : counted 42=anchor.bits := by simp [counted,flagged,parsed,propagationInputFile]
  have anchorTarget : counted 30=[] := by simp [counted,flagged,parsed,propagationInputFile]
  rw [anchorSource,anchorTarget,List.append_nil] at d
  let queried:=Function.update counted 30 anchor.bits
  have e:=copy_executes 41 (40:Fin 44) 32 43 (by decide) (by decide) (by decide) queried
    (by simp [queried,counted,flagged,parsed,propagationInputFile])
  have countSource : queried 40=List.replicate vista.nodes.size true := by simp [queried,counted]
  have countTarget : queried 32=[] := by simp [queried,counted,flagged,parsed,propagationInputFile]
  rw [countSource,countTarget,List.append_nil,List.length_replicate] at e
  let ready:=Function.update queried 32 (List.replicate vista.nodes.size true)
  obtain ⟨zeroTime,zeroBound,f⟩:=allocatePropagationZeros_executes ready vista.nodes.size
    (by simp [ready,queried,counted]) (by
      intro i different;fin_cases i <;>
        simp_all [ready,queried,counted,flagged,parsed,propagationInputFile,propagationZeroRoles])
  change Executes _ ready zeroTime (propagationSetupFile anchor vista values) at f
  have nodes:=Encoding.vista_nodes_le_length vista
  change headerTime ≤ 1820*((Encoding.vista.encode vista).length+1)^3 at headerBound
  have headerRaised:=headerBound.trans (Nat.mul_le_mul_left 1820
    (Nat.pow_le_pow_left (by omega : (Encoding.vista.encode vista).length+1 ≤
      (Encoding.vista.encode vista).length+anchor.size+1) 3))
  have zeroRaised:=zeroBound.trans (Nat.mul_le_mul_left 80
    ((Nat.pow_le_pow_left (by omega : vista.nodes.size+1 ≤
      (Encoding.vista.encode vista).length+anchor.size+1) 2).trans
        (Nat.pow_le_pow_right (by omega) (by decide : 2≤3))))
  have linear : (Encoding.vista.encode vista).length+anchor.size+1 ≤
      ((Encoding.vista.encode vista).length+anchor.size+1)^3 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))⟩
  simp only [Encoding.bits_length]
  omega

abbrev preparePropagationInput : Routine 42 := sequence readPropagationInput setupPropagationInput

theorem preparePropagationInput_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) :
    ∃ time ≤ 5000*((propagationInputWord anchor vista values).length+1)^3,
      Executes preparePropagationInput
        (propagationInputFile (propagationInputWord anchor vista values) [] [] [] []) time
        (propagationSetupFile anchor vista values) := by
  obtain ⟨readTime,readBound,reading⟩:=readPropagationInput_executes anchor vista values
  obtain ⟨setupTime,setupBound,setup⟩:=setupPropagationInput_executes anchor vista values
  have inputSize : (Encoding.vista.encode vista).length+anchor.size+1 ≤
      (propagationInputWord anchor vista values).length+1 := by
    simp only [propagationInputWord,propagationInputCodec,Encoding.product,
      Encoding.framed,List.length_append,Encoding.natural_length,Encoding.frame_length]
    omega
  have setupRaised:=setupBound.trans (Nat.mul_le_mul_left 4000 (Nat.pow_le_pow_left inputSize 3))
  have readRaised:=readBound.trans (Nat.mul_le_mul_left 100
    (Nat.pow_le_pow_right (by omega) (by decide : 2≤3)))
  have positive : 1 ≤ ((propagationInputWord anchor vista values).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,reading.sequence setup⟩

end Counting.StackMachine.AuditPropagation
