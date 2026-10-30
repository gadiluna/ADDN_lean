import Counting.StackAnchorMatrixBank
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def widthRoles : FullListWorkspace 33 :=
  ⟨![0,1,2,3,42,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

abbrev popWidth : Routine 48 := ⟨1,fun control=>if control=0 then .pop 42 1 1 1 else .halt⟩

private theorem popWidth_executes (store : Store 48) (bits : List Bool) (content : store 42=true::bits) :
    Executes popWidth store 1 (Function.update store 42 bits) := by
  refine ⟨⟨1,_⟩,?_,?_,rfl⟩
  · simp [Machine.run,step,popWidth,content]
    funext r
    cases decision : instDecidableEqFin 50 r 42 with
    | isTrue same => simp [Function.update,same]
    | isFalse different => simp [Function.update,different]
  · simp [step,popWidth]

/-- Read the real row header and remove its right-hand-side column. -/
abbrev measureWidth : Routine 48 := sequence (ofProgram (ListPrograms.copyProgram 47 22 0 39))
  (sequence (pushBit 1 true) (sequence (readListHeader 33 widthRoles)
    (sequence popWidth (sequence (clear 0) (clear 1)))))

theorem measureWidth_executes (store : Store 48) (coefficients : List Rat) (rhs : Rat)
    (encoded : store 22=Encoding.rationalRow.encode (coefficients++[rhs]))
    (sourceEmpty : store 0=[]) (flagEmpty : store 1=[]) (copyEmpty : store 39=[])
    (empty : ∀ i : Fin 17,i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17)) → store (widthRoles i)=[]) :
    ∃ time ≤ 2000*((store 22).length+1)^3,
      Executes measureWidth store time (Function.update store 42 (List.replicate coefficients.length true)) := by
  let copied := Function.update store 0 (store 22)
  have a := copy_executes 47 (22:Fin 50) 0 39 (by decide) (by decide) (by decide) store copyEmpty
  simp only [sourceEmpty,List.append_nil] at a
  change Executes _ store (5*(store 22).length+2) copied at a
  let ready := Function.update copied 1 [true]
  have b := pushBit_executes (1:Fin 50) true copied
  have bs : Function.update copied 1 (true::copied 1)=ready := by simp [copied,ready,flagEmpty]
  rw [bs] at b
  obtain ⟨headerTime,headerBound,c⟩ := readListHeader_canonical 33 widthRoles ready true [] rfl
    (by
      intro i member
      have e:=empty i member
      fin_cases i <;> simp_all [ready,copied,widthRoles])
    (Encoding.framed Encoding.rational) (by intro value;rw [Encoding.framed_length];omega)
    (coefficients++[rhs]) [] (by simpa [ready,copied,widthRoles,Encoding.rationalRow] using encoded)
  let stream := Encoding.sequence (Encoding.framed Encoding.rational) (coefficients++[rhs])
  let parsed := Function.update (Function.update ready 0 stream) 42 (List.replicate (coefficients.length+1) true)
  have cs : Function.update (Function.update ready (widthRoles 0)
      (Encoding.sequence (Encoding.framed Encoding.rational) (coefficients++[rhs])++[]))
      (widthRoles 4) (List.replicate (coefficients++[rhs]).length true)=parsed := by
    simp [parsed,stream,widthRoles]
  rw [cs] at c
  have d := popWidth_executes parsed (List.replicate coefficients.length true)
    (by simp [parsed,List.replicate_succ])
  let counted := Function.update (Function.update ready 0 stream) 42 (List.replicate coefficients.length true)
  have ds : Function.update parsed 42 (List.replicate coefficients.length true)=counted := by
    simp [parsed,counted]
  rw [ds] at d
  have e := clear_executes (0:Fin 50) counted
  let cleared := Function.update (Function.update ready 0 []) 42 (List.replicate coefficients.length true)
  have es : Function.update counted 0 []=cleared := by
    funext r;by_cases r0:r=0 <;> by_cases r42:r=42 <;> simp_all [counted,cleared]
  rw [es] at e
  change Executes _ counted (stream.length+1) cleared at e
  have f := clear_executes (1:Fin 50) cleared
  have fs : Function.update cleared 1 []=Function.update store 42 (List.replicate coefficients.length true) := by
    funext r;by_cases r0:r=0 <;> by_cases r1:r=1 <;> by_cases r42:r=42 <;>
      simp_all [cleared,ready,copied]
  rw [fs] at f
  change Executes _ cleared 2 _ at f
  have composed := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))
  refine ⟨_,?_,composed⟩
  have streamBound : stream.length ≤ (store 22).length := by
    rw [encoded]
    change stream.length ≤ (Encoding.natural.encode (coefficients++[rhs]).length++stream).length
    simp only [List.length_append];omega
  have linear : (store 22).length+1 ≤ ((store 22).length+1)^3 := Nat.le_self_pow (by decide) _
  change headerTime ≤ 1820*((store 22).length+1)^3 at headerBound
  omega

end Counting.StackMachine.AnchorMatrix
