import Counting.NetworkVistaRead
import Counting.StackEncodingDagParser

namespace Counting.StackMachine.NetworkVista.Reader
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {α : Type} {codec : Encoding.Codec α}
  (parser : VerifiedParser 15 0 1 2 α codec)

/-- Preserving indexed access to a fully serialized list, including its
binary length header. The index counts listed entries, not a binary value. -/
def arrayRead : Routine 19 :=
  sequence (ofProgram (ListPrograms.copyProgram 18 17 0 3))
    (sequence (wideParser DagParser.natural).routine
      (sequence (clear 2)
        (sequence (ofProgram (ListPrograms.copyProgram 18 18 20 3))
          (sequence ((wideParser parser).read 20)
            (sequence (clear 0) (ofProgram (ListPrograms.reverseProgram 19 2 19)))))))

theorem arrayRead_get (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 17,r≠1 → store (parserRoles r)=[])
    (e19 : store 19=[]) (e20 : store 20=[])
    (values : List α) (index : Fin values.length) (suffix : List Bool)
    (source : store 17=(Encoding.list codec).encode values++suffix)
    (position : (store 18).length=index.val) :
    ∃ time ≤ (2*(store 18).length+3)*Complexity.polynomial parser.coefficient parser.exponent (store 17).length+
        200*((store 17).length+1)^2+8*(store 18).length+30,
      Executes (arrayRead parser) store time (Function.update store 19 (codec.encode values[index])) := by
  have empty (r:Fin 17) (different:r≠1) : store (parserRoles r)=[] := work r different
  have e0 : store 0=[] := empty 0 (by decide)
  have e2 : store 2=[] := empty 2 (by decide)
  have e3 : store 3=[] := empty 3 (by decide)
  have copy := copy_executes 18 (17:Fin 21) 0 3 (by decide) (by decide) (by decide) store e3
  rw [e0,List.append_nil] at copy
  let copied := Function.update store 0 (store 17)
  have parserWork : ∀r∈(wideParser DagParser.natural).work,copied r=[] := by
    intro r member
    obtain ⟨i,present,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨n0,n1,_⟩ := DagParser.natural.separate i present
    have mapped : parserRoles i≠0 := by intro eq;exact n0 (parserRoles.injective eq)
    simpa [copied,mapped] using empty i n1
  obtain ⟨t0,b0,r0⟩ := (wideParser DagParser.natural).executes copied accepted tail
    (by simp [copied,status]) parserWork
  have parsed : (wideParser DagParser.natural).effect (copied 0)=
      ⟨Encoding.sequence codec values++suffix,Encoding.natural.encode values.length,true⟩ := by
    rw [show copied 0=store 17 by simp [copied],source]
    change DagParser.natural.effect ((Encoding.natural.encode values.length++Encoding.sequence codec values)++suffix)=_
    rw [List.append_assoc,DagParser.natural.roundtrip]
  rw [parsed] at r0
  let header := parseStore 0 1 2 copied accepted tail
    ⟨Encoding.sequence codec values++suffix,Encoding.natural.encode values.length,true⟩
  have clearHeader := clear_executes (2:Fin 21) header
  have headerAt : header 2=(Encoding.natural.encode values.length).reverse := by simp [header,parseStore,copied,e2]
  rw [headerAt,List.length_reverse] at clearHeader
  let ready := Function.update header 2 []
  have copyIndex := copy_executes 18 (18:Fin 21) 20 3 (by decide) (by decide) (by decide) ready
    (by simp [ready,header,parseStore,copied,e3])
  have sameIndex : ready 18=store 18 := by simp [ready,header,parseStore,copied]
  rw [sameIndex,show ready 20=[] by simp [ready,header,parseStore,copied,e20],List.append_nil] at copyIndex
  let indexed := Function.update ready 20 (store 18)
  have indexedSource : indexed 0=Encoding.sequence codec values++suffix := by simp [indexed,ready,header,parseStore]
  have indexedWork : ∀r∈(wideParser parser).work,indexed r=[] := by
    intro r member
    obtain ⟨i,present,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨n0,n1,n2⟩ := parser.separate i present
    have no0:parserRoles i≠0 := by intro eq;exact n0 (parserRoles.injective eq)
    have no1:parserRoles i≠1 := by intro eq;exact n1 (parserRoles.injective eq)
    have no2:parserRoles i≠2 := by intro eq;exact n2 (parserRoles.injective eq)
    have no20:parserRoles i≠20 := by
      intro eq
      have value := congrArg (fun r:Fin 21=>r.val) eq
      change i.val=20 at value
      have := i.isLt
      omega
    simpa [indexed,ready,header,parseStore,copied,no0,no1,no2,no20] using empty i n1
  obtain ⟨t1,b1,r1⟩ := (wideParser parser).read_executes (by decide) (by decide) (by decide)
    20 (by decide) (by decide) (by decide) (by
      intro member
      obtain ⟨i,_,same⟩ := Finset.mem_map.mp member
      have value := congrArg (fun r:Fin 21=>r.val) same
      change i.val=20 at value
      have := i.isLt
      omega) (store 18) indexed accepted tail
    (by simp [indexed,ready,header,parseStore,Bool.and_true]) indexedWork
    (by simp [indexed,ready]) (by simp [indexed]) (store 17).length
    (by rw [indexedSource,source];simp only [Encoding.list,List.length_append];omega)
  rw [indexedSource,position,(wideParser parser).read_get] at r1
  let selected := parseStore 0 1 2 (Function.update indexed 20 []) accepted tail
    ⟨Encoding.sequence codec (values.drop (index.val+1))++suffix,codec.encode values[index],true⟩
  have clearSource := clear_executes (0:Fin 21) selected
  rw [show selected 0=Encoding.sequence codec (values.drop (index.val+1))++suffix by simp [selected,parseStore]] at clearSource
  have reverse := reverse_executes 19 (2:Fin 21) 19 (by decide) (Function.update selected 0 [])
  rw [show Function.update selected 0 [] 2=(codec.encode values[index]).reverse by simp [selected,parseStore,indexed,ready],
    show Function.update selected 0 [] 19=[] by simp [selected,parseStore,indexed,ready,header,copied,e19],
    List.length_reverse,List.reverse_reverse,List.append_nil] at reverse
  have final : Function.update (Function.update (Function.update selected 0 []) 2 []) 19 (codec.encode values[index])=
      Function.update store 19 (codec.encode values[index]) := by
    funext r
    fin_cases r <;> simp [selected,parseStore,indexed,ready,header,copied,status,e0,e2,e20]
  rw [final] at reverse
  have inputLength : (copied 0).length=(store 17).length := by simp [copied]
  rw [inputLength] at b0
  have headerSize : (Encoding.natural.encode values.length).length≤(store 17).length := by
    rw [source];simp only [Encoding.list,List.length_append];omega
  have remainingSize : (Encoding.sequence codec (values.drop (index.val+1))++suffix).length≤(store 17).length := by
    have remaining := parser.read_suffix_le index.val (Encoding.sequence codec values++suffix)
    rw [parser.read_get] at remaining
    change (Encoding.sequence codec (values.drop (index.val+1))++suffix).length≤_ at remaining
    rw [source];simp only [Encoding.list,List.length_append] at *;omega
  have outputSize := parser.read_code_le index.val (Encoding.sequence codec values++suffix)
  rw [parser.read_get] at outputSize
  change (codec.encode values[index]).length≤Complexity.polynomial parser.coefficient parser.exponent
    (Encoding.sequence codec values++suffix).length at outputSize
  have sourceSize : (Encoding.sequence codec values++suffix).length≤(store 17).length := by
    rw [source];simp only [Encoding.list,List.length_append];omega
  have codeBound : (codec.encode values[index]).length≤Complexity.polynomial parser.coefficient parser.exponent (store 17).length := by
    apply outputSize.trans
    unfold Complexity.polynomial
    gcongr
  change t0≤Complexity.polynomial 40 1 (store 17).length at b0
  change t1 ≤ (store 18).length*(2*Complexity.polynomial parser.coefficient parser.exponent (store 17).length+2)+
    Complexity.polynomial parser.coefficient parser.exponent (store 17).length+4 at b1
  have linear : (store 17).length+1≤((store 17).length+1)^2 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,copy.sequence (r0.sequence (clearHeader.sequence (copyIndex.sequence (r1.sequence (clearSource.sequence reverse)))))⟩
  unfold Complexity.polynomial at b0 b1 codeBound ⊢
  simp only [pow_one] at b0
  nlinarith only [b0,b1,codeBound,remainingSize,headerSize,linear]

end Counting.StackMachine.NetworkVista.Reader
