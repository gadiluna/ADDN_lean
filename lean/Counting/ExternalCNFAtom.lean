import Counting.ExternalSATLiteralRead

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

def signProgram (extra : Nat) (flag positive negative : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 5
  code state := match state.val with
    | 0 => .pop flag 1 1 3
    | 1 => .push positive false 2
    | 2 => .push negative true 5
    | 3 => .push positive true 4
    | 4 => .push negative false 5
    | _ => .halt

theorem sign_executes (extra : Nat) (flag positive negative : Fin (extra+2))
    (fp : flag≠positive) (fn : flag≠negative) (pn : positive≠negative)
    (store : Fin (extra+2) → List Bool) (bit : Bool) (tail : List Bool)
    (source : store flag=bit::tail) :
    Executes (ofProgram (signProgram extra flag positive negative)) store 3
      (Function.update (Function.update (Function.update store flag tail) positive (bit::store positive))
        negative ((!bit)::store negative)) := by
  let result := Function.update (Function.update (Function.update store flag tail) positive (bit::store positive))
    negative ((!bit)::store negative)
  refine ⟨⟨5,result⟩,?_,rfl,rfl⟩
  cases bit <;>
    simp [Machine.run,step,signProgram,source,result,Ne.symm fp,Ne.symm fn,Ne.symm pn]

def atomRead (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readLiteral extra w)
    (sequence (ofProgram (signProgram (extra+30) (w 21) (w 30) (w 31)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 18) (w 30) (w 3)))
        (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 18) (w 31) (w 3))) (clear (w 18)))))

theorem atomRead_executes (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool)
    (index : Nat) (sign accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.product Encoding.natural Encoding.boolean).encode (index,sign)++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈([2,3,4,5,6,9,10,18,21,30,31] : List (Fin 32)),store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+1),
      Executes (atomRead extra w) store time
        (Function.update (Function.update (Function.update store (w 0) suffix)
          (w 30) ((Encoding.product Encoding.natural Encoding.boolean).encode (index,sign)))
          (w 31) ((Encoding.product Encoding.natural Encoding.boolean).encode (index,!sign))) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  obtain ⟨readTime,readBound,reading⟩ := readLiteral_executes extra w store index sign accepted suffix tail source status
    (fun i member => empty i (by simp only [List.mem_cons,List.not_mem_nil] at member ⊢; tauto))
  let code := Encoding.natural.encode index
  let readStore := Function.update (Function.update (Function.update store (w 0) suffix) (w 18) code) (w 21) [sign]
  have signing := sign_executes (extra+30) (w 21) (w 30) (w 31)
    (ne 21 30 (by decide)) (ne 21 31 (by decide)) (ne 30 31 (by decide)) readStore sign [] (by simp [readStore])
  have positiveEmpty : readStore (w 30)=[] := by simp [readStore,w.injective.eq_iff,empty 30 (by decide)]
  have negativeEmpty : readStore (w 31)=[] := by simp [readStore,w.injective.eq_iff,empty 31 (by decide)]
  rw [positiveEmpty,negativeEmpty] at signing
  let signed := Function.update (Function.update (Function.update readStore (w 21) []) (w 30) [sign]) (w 31) [!sign]
  have first := copy_executes (extra+29) (w 18) (w 30) (w 3)
    (ne 18 30 (by decide)) (ne 18 3 (by decide)) (ne 30 3 (by decide)) signed
    (by simp [signed,readStore,w.injective.eq_iff,empty 3 (by decide)])
  have signedHeader : signed (w 18)=code := by simp [signed,readStore,w.injective.eq_iff]
  have signedPositive : signed (w 30)=[sign] := by simp [signed,w.injective.eq_iff]
  rw [signedHeader,signedPositive] at first
  let firstStore := Function.update signed (w 30) (code++[sign])
  have second := copy_executes (extra+29) (w 18) (w 31) (w 3)
    (ne 18 31 (by decide)) (ne 18 3 (by decide)) (ne 31 3 (by decide)) firstStore
    (by simp [firstStore,signed,readStore,w.injective.eq_iff,empty 3 (by decide)])
  have firstHeader : firstStore (w 18)=code := by simp [firstStore,w.injective.eq_iff,signedHeader]
  have firstNegative : firstStore (w 31)=[!sign] := by simp [firstStore,signed,w.injective.eq_iff]
  rw [firstHeader,firstNegative] at second
  let secondStore := Function.update firstStore (w 31) (code++[!sign])
  have clearing := clear_executes (w 18) secondStore
  have secondHeader : secondStore (w 18)=code := by simp [secondStore,w.injective.eq_iff,firstHeader]
  rw [secondHeader] at clearing
  have finalStore : Function.update secondStore (w 18) []=
      Function.update (Function.update (Function.update store (w 0) suffix)
        (w 30) ((Encoding.product Encoding.natural Encoding.boolean).encode (index,sign)))
        (w 31) ((Encoding.product Encoding.natural Encoding.boolean).encode (index,!sign)) := by
    funext r
    by_cases a : r=w 18
    · subst r;simp [w.injective.eq_iff,empty 18 (by decide)]
    · by_cases b : r=w 31
      · subst r;simp [secondStore,code,Encoding.product,Encoding.boolean,w.injective.eq_iff]
      · by_cases c : r=w 30
        · subst r;simp [secondStore,firstStore,code,Encoding.product,Encoding.boolean,w.injective.eq_iff]
        · by_cases d : r=w 21
          · subst r;simp [secondStore,firstStore,signed,w.injective.eq_iff,empty 21 (by decide)]
          · simp [secondStore,firstStore,signed,readStore,a,b,c,d]
  rw [finalStore] at clearing
  have combined := reading.sequence (signing.sequence (first.sequence (second.sequence clearing)))
  refine ⟨readTime+1+(3+1+(5*code.length+2+1+(5*code.length+2+1+(code.length+1)))),?_,combined⟩
  have codeBound : code.length≤(store (w 0)).length := by
    rw [source]
    simp only [Encoding.product,Encoding.boolean,List.length_append,List.length_singleton]
    dsimp [code]
    omega
  nlinarith only [readBound,codeBound]

end Counting.External.CNFMachine
