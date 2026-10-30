import Counting.ExternalCNFAtom
import Counting.ExternalCNFGate
import Counting.StackEncodingBranch
import Counting.StackEmitSyntax

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

/-- The literal parser workspace, plus both signs of the terminal variable. -/
abbrev OptionalWorkspace (extra : Nat) := Fin 34 ↪ Fin (extra+34)

def optionalParserRoles (extra : Nat) (w : OptionalWorkspace extra) : SATWorkspace (extra+2) :=
  (Fin.castLEEmb (by decide : 32≤34)).trans w

def terminalAtom (extra : Nat) (w : OptionalWorkspace extra) : Routine (extra+32) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+31) (w 32) (w 30) (w 3)))
    (ofProgram (ListPrograms.copyProgram (extra+31) (w 33) (w 31) (w 3)))

def optionalAtom (extra : Nat) (w : OptionalWorkspace extra) : Routine (extra+32) :=
  branchRoutine (w 24) (atomRead (extra+2) (optionalParserRoles extra w)) (terminalAtom extra w)

def optionalScratch : List (Fin 34) := [2,3,4,5,6,9,10,18,21,30,31]

theorem optionalAtom_executes (extra : Nat) (w : OptionalWorkspace extra)
    (store : Fin (extra+34) → List Bool) (literals : List (Nat×Bool)) (terminal : Nat)
    (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence literalCodec literals++suffix)
    (counter : store (w 24)=List.replicate literals.length true)
    (status : store (w 1)=accepted::tail)
    (positive : store (w 32)=literalCodec.encode (terminal,true))
    (negative : store (w 33)=literalCodec.encode (terminal,false))
    (empty : ∀ i∈optionalScratch,store (w i)=[]) :
    ∃ time ≤ 200*((store (w 0)).length+(store (w 32)).length+(store (w 33)).length+1),
      Executes (optionalAtom extra w) store time
        (Function.update (Function.update (Function.update (Function.update store
          (w 24) (List.replicate literals.tail.length true))
          (w 0) (Encoding.sequence literalCodec literals.tail++suffix))
          (w 30) (literalCodec.encode (literals.headD (terminal,true))))
          (w 31) (literalCodec.encode ((literals.headD (terminal,true)).1,!(literals.headD (terminal,true)).2))) := by
  have ne (i j : Fin 34) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  cases literals with
  | nil =>
    have first := copy_executes (extra+31) (w 32) (w 30) (w 3)
      (ne 32 30 (by decide)) (ne 32 3 (by decide)) (ne 30 3 (by decide)) store (empty 3 (by decide))
    rw [positive,empty 30 (by decide),List.append_nil] at first
    let next := Function.update store (w 30) (literalCodec.encode (terminal,true))
    have second := copy_executes (extra+31) (w 33) (w 31) (w 3)
      (ne 33 31 (by decide)) (ne 33 3 (by decide)) (ne 31 3 (by decide)) next
      (by simp [next,w.injective.eq_iff,empty 3 (by decide)])
    have nextNeg : next (w 33)=literalCodec.encode (terminal,false) := by simp [next,w.injective.eq_iff,negative]
    have nextOut : next (w 31)=[] := by simp [next,w.injective.eq_iff,empty 31 (by decide)]
    rw [nextNeg,nextOut,List.append_nil] at second
    have body : Executes (terminalAtom extra w) store
        (5*(literalCodec.encode (terminal,true)).length+2+1+(5*(literalCodec.encode (terminal,false)).length+2))
        (Function.update next (w 31) (literalCodec.encode (terminal,false))) := first.sequence second
    have run := branch_executes_empty (w 24) (atomRead (extra+2) (optionalParserRoles extra w))
      (terminalAtom extra w) store _ _ counter body
    have zero : store (w 24)=[] := counter
    have sourceEq : store (w 0)=suffix := source
    have finalEq : Function.update (Function.update (Function.update (Function.update store
        (w 24) (List.replicate (([] : List (Nat×Bool)).tail.length) true)) (w 0) (Encoding.sequence literalCodec [].tail++suffix))
        (w 30) (literalCodec.encode ([].headD (terminal,true))))
        (w 31) (literalCodec.encode (([].headD (terminal,true)).1,!([].headD (terminal,true)).2))=
        Function.update next (w 31) (literalCodec.encode (terminal,false)) := by
      simp only [List.tail_nil,List.length_nil,List.replicate_zero,Encoding.sequence,List.nil_append,List.headD_nil,Bool.not_true]
      rw [←zero,Function.update_eq_self,←sourceEq,Function.update_eq_self]
    refine ⟨1+(5*(literalCodec.encode (terminal,true)).length+2+1+(5*(literalCodec.encode (terminal,false)).length+2)),?_,?_⟩
    · rw [positive,negative]
      omega
    · rw [finalEq]
      exact run
  | cons literal rest =>
    let consumed := Function.update store (w 24) (List.replicate rest.length true)
    have readSource : consumed (w 0)=literalCodec.encode literal++(Encoding.sequence literalCodec rest++suffix) := by
      simpa only [consumed,Function.update_of_ne (ne 0 24 (by decide)),Encoding.sequence,List.append_assoc] using source
    obtain ⟨time,bound,run⟩ := atomRead_executes (extra+2) (optionalParserRoles extra w) consumed literal.1 literal.2 accepted
      (Encoding.sequence literalCodec rest++suffix) tail readSource
      (by simpa [optionalParserRoles,consumed,w.injective.eq_iff] using status)
      (by
        intro i member
        have diff : (Fin.castLE (by decide : 32≤34) i : Fin 34)≠24 := by
          intro same
          have value := congrArg Fin.val same
          simp only [List.mem_cons,List.not_mem_nil] at member
          rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h <;> simp_all
        simpa only [optionalParserRoles,Function.Embedding.trans_apply,Fin.castLEEmb_apply,consumed,
          Function.update_of_ne (ne _ _ diff)] using
          empty (Fin.castLE (by decide : 32≤34) i) (by
            simp only [List.mem_cons,List.not_mem_nil] at member
            rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h <;> simp_all [optionalScratch]))
    have branch := branch_executes_true (w 24) (atomRead (extra+2) (optionalParserRoles extra w)) (terminalAtom extra w)
      store _ (List.replicate rest.length true) time (by simpa only [List.length_cons,List.replicate_succ] using counter) run
    refine ⟨1+time,?_,branch⟩
    · have sourceSame : consumed (w 0)=store (w 0) := by simp [consumed,w.injective.eq_iff]
      change time≤100*((consumed (w 0)).length+1) at bound
      rw [sourceSame] at bound
      omega

end Counting.External.CNFMachine
