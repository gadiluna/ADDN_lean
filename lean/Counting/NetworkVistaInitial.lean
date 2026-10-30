import Counting.NetworkVistaInitialHeader

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def initialPrefix : Routine 19 := sequence initialHeader
  (sequence (ofProgram (ListPrograms.reverseProgram 19 4 19))
    (sequence (ofProgram (ListPrograms.copyProgram 18 18 0 4))
      (sequence (relocate (forEach 2 initialItem) initialLoopRoles)
        (ofProgram (ListPrograms.reverseProgram 19 19 20)))))

def initialPrefixStore (store:Store 19) (leaders suffix:List Bool) : Store 19 :=
  Function.update (Function.update (Function.update store 17 suffix) 0 (List.replicate leaders.length true))
    20 ((Encoding.list Encoding.vista).encode (leaders.map Executable.initialVista))

theorem initialSequence_length (leaders:List Bool) :
    (Encoding.sequence Encoding.vista (leaders.map Executable.initialVista)).length=9*leaders.length := by
  induction leaders with
  | nil=>rfl
  | cons leader leaders ih=>
    simp only [List.map_cons,Encoding.sequence,List.length_append,List.length_cons,ih]
    change (initialCode leader).length+9*leaders.length=_
    rw [initialCode_length]
    omega

theorem initialPrefix_executes (store:Store 19) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (work:∀r:Fin 21,r.val<17 → r≠1 → store r=[])
    (e18:store 18=[]) (e19:store 19=[]) (e20:store 20=[])
    (leaders suffix:List Bool) (input:store 17=(Encoding.list Encoding.boolean).encode leaders++suffix) :
    ∃time ≤ 2000*((store 17).length+1)^3,
      Executes initialPrefix store time (initialPrefixStore store leaders suffix) := by
  obtain ⟨headerTime,headerBound,headerRun⟩:=initialHeader_executes store accepted tail status work e18 leaders suffix input
  let parsed:=initialHeaderStore store leaders suffix
  have headerReverse:=reverse_executes 19 (4:Fin 21) 19 (by decide) parsed
  rw [show parsed 4=Encoding.natural.encode leaders.length by simp [parsed,initialHeaderStore],
    show parsed 19=[] by simp [parsed,initialHeaderStore,e19],List.append_nil] at headerReverse
  let reversed:=Function.update (Function.update parsed 4 []) 19 (Encoding.natural.encode leaders.length).reverse
  have copying:=copy_executes 18 (18:Fin 21) 0 4 (by decide) (by decide) (by decide) reversed (by simp [reversed])
  rw [show reversed 18=List.replicate leaders.length true by simp [reversed,parsed,initialHeaderStore],
    show reversed 0=[] by simp [reversed,parsed,initialHeaderStore,work],List.append_nil,List.length_replicate] at copying
  let copied:=Function.update reversed 0 (List.replicate leaders.length true)
  let scanned:=Function.update (Function.update (Function.update copied 17 suffix) 18 [])
    19 ((Encoding.sequence Encoding.vista (leaders.map Executable.initialVista)).reverse++
      (Encoding.natural.encode leaders.length).reverse)
  have localRun:=initialValues_executes leaders suffix (copied ∘ initialLoopRoles)
    (by simp [copied,reversed,parsed,initialHeaderStore,initialLoopRoles])
    (by simp [copied,reversed,parsed,initialHeaderStore,initialLoopRoles])
  have scanning:Executes (relocate (forEach 2 initialItem) initialLoopRoles) copied (21*leaders.length+1) scanned:=by
    apply relocate_executes_frame (forEach 2 initialItem) initialLoopRoles copied scanned
      (copied ∘ initialLoopRoles) (initialValuesStore (copied ∘ initialLoopRoles) leaders suffix) _ rfl
    · intro i
      fin_cases i <;> simp [scanned,copied,reversed,parsed,initialHeaderStore,initialLoopRoles,initialValuesStore]
    · intro r outside
      have n17:r≠17:=by simpa [initialLoopRoles] using (outside 0).symm
      have n19:r≠19:=by simpa [initialLoopRoles] using (outside 1).symm
      have n18:r≠18:=by simpa [initialLoopRoles] using (outside 2).symm
      simp [scanned,n17,n19,n18]
    · exact localRun
  have finishing:=reverse_executes 19 (19:Fin 21) 20 (by decide) scanned
  have output:scanned 19=((Encoding.list Encoding.vista).encode (leaders.map Executable.initialVista)).reverse:=by
    simp only [scanned,Function.update_self,Encoding.list,List.length_map,List.reverse_append]
  have vacant:scanned 20=[]:=by simp [scanned,copied,reversed,parsed,initialHeaderStore,e20]
  rw [output,vacant,List.append_nil,List.reverse_reverse,List.length_reverse] at finishing
  have final:Function.update (Function.update scanned 19 []) 20
      ((Encoding.list Encoding.vista).encode (leaders.map Executable.initialVista))=initialPrefixStore store leaders suffix:=by
    funext r
    fin_cases r <;> simp [scanned,copied,reversed,parsed,initialHeaderStore,initialPrefixStore,work,e18,e19]
  rw [final] at finishing
  have countBound:leaders.length ≤ (store 17).length:=by
    rw [input]
    change leaders.length ≤ ((Encoding.natural.encode leaders.length++Encoding.sequence Encoding.boolean leaders)++suffix).length
    rw [NetworkRecognition.boolean_sequence]
    simp only [List.length_append];omega
  have sizeBound:leaders.length.size ≤ leaders.length:=Nat.size_le.mpr Nat.lt_two_pow_self
  have totalLength:((Encoding.list Encoding.vista).encode (leaders.map Executable.initialVista)).length=
      (Encoding.natural.encode leaders.length).length+9*leaders.length:=by
    change (Encoding.natural.encode (leaders.map Executable.initialVista).length++Encoding.sequence Encoding.vista _).length=_
    rw [List.length_map,List.length_append,initialSequence_length]
  have linear:(store 17).length+1 ≤ ((store 17).length+1)^3:=Nat.le_self_pow (by decide) _
  refine ⟨_,?_,headerRun.sequence (headerReverse.sequence (copying.sequence (scanning.sequence finishing)))⟩
  rw [totalLength,Encoding.natural_length]
  omega

end Counting.StackMachine.NetworkVista
