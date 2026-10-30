import Counting.StackUnframeCanonical
import Counting.StackEncodingFrame
import Counting.StackDagReferenceLookup
import Counting.EncodingNetwork

/-! Read the binary bottom index and multiplicity of an imported message.
The reference lookup scans the actual encoded import map; neither a decoded
reference nor a unary multiplicity is supplied to the program. -/
namespace Counting.StackMachine.DagUpdate.Receive
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def readTail : Routine 94 :=
  sequence (ofProgram (unframeProgram 93 70 2 0))
    (sequence (frameRoutine 93 2 3 0)
      (ofProgram (unframeProgram 93 70 17 0)))

def tailResult (store : Store 94) (bottom count : Nat) (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update store 70 suffix)
    3 (Encoding.natural.encode bottom)) 17 count.bits

theorem readTail_executes (store : Store 94) (bottom count : Nat) (suffix : List Bool)
    (source : store 70=Encoding.natural.encode bottom++Encoding.natural.encode count++suffix)
    (empty : ∀ r : Fin 96,r∈([0,2,3,17]:List (Fin 96)) → store r=[]) :
    Executes readTail store (10*bottom.bits.length+5*count.bits.length+10)
      (tailResult store bottom count suffix) := by
  let rest := Encoding.natural.encode count++suffix
  have first := unframe_canonical_executes 93 (70:Fin 96) 2 0
    (by decide) (by decide) (by decide) store bottom.bits rest
    (by simpa only [Encoding.natural,List.append_assoc,rest] using source)
    (empty 0 (by simp))
  rw [empty 2 (by simp),List.append_nil] at first
  let parsed := Function.update (Function.update store 70 rest) 2 bottom.bits
  have frame := frame_executes 93 (2:Fin 96) 3 0 (by decide) (by decide) (by decide)
    parsed (by simp [parsed,empty])
  have parsedAt : parsed 2=bottom.bits := by simp [parsed]
  rw [parsedAt] at frame
  let framed := Function.update (Function.update store 70 rest) 3 (Encoding.natural.encode bottom)
  have frameStore : frameResult 93 2 3 0 parsed=framed := by
    funext r
    by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> by_cases r3 : r=3 <;>
      simp [frameResult,parsed,framed,r0,r2,r3,empty,Encoding.natural]
  rw [frameStore] at frame
  have last := unframe_canonical_executes 93 (70:Fin 96) 17 0
    (by decide) (by decide) (by decide) framed count.bits suffix
    (by simp [framed,rest,Encoding.natural]) (by simp [framed,empty])
  have targetEmpty : framed 17=[] := by simp [framed,empty]
  rw [targetEmpty,List.append_nil] at last
  have final : Function.update (Function.update framed 70 suffix) 17 count.bits=
      tailResult store bottom count suffix := by
    funext r
    by_cases r70 : r=70 <;> by_cases r3 : r=3 <;> by_cases r17 : r=17 <;>
      simp [framed,tailResult,r70,r3,r17]
  rw [final] at last
  convert first.sequence (frame.sequence last) using 1 <;> first | rfl | omega

def bottomRoles : ReferenceWorkspace 82 :=
  ⟨![1,3,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

def readBottom : Routine 94 := referenceLookup 82 bottomRoles

theorem readBottom_executes (store : Store 94) (mapping : Array Nat) (bottom : Nat)
    (mapAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (query : store 3=Encoding.natural.encode bottom)
    (empty : ∀ r : Fin 96,4 ≤ r.val → r.val ≤ 15 → store r=[]) :
    ∃ time ≤ 200*((store 1).length+(store 3).length+1)^3,
      Executes readBottom store time
        (Function.update store 4 (mapping[bottom]?.getD 0).bits) := by
  obtain ⟨time,bound,ran⟩ := referenceLookup_executes 82 bottomRoles store mapping.toList bottom
    mapAt query (by
      intro r n0 n1 n2
      fin_cases r <;> simp_all [bottomRoles])
  have targetEmpty : store (bottomRoles 2)=[] := empty 4 (by decide) (by decide)
  rw [targetEmpty,List.append_nil] at ran
  exact ⟨time,bound,by simpa [readBottom,bottomRoles] using ran⟩

end Counting.StackMachine.DagUpdate.Receive
