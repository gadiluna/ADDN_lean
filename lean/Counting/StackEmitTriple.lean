import Counting.StackRoutineCopyReverse
import Counting.StackEmitClause

namespace Counting.StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Three encoded literal sources, reversed output, empty buffer and scratch. -/
abbrev TripleWorkspace (extra : Nat) := Fin 6 ↪ Fin (extra+6)

def tripleSourceRoles (w : TripleWorkspace extra) (source : Fin 3) : Fin 4 ↪ Fin (extra+6) where
  toFun i := w (![source.castLE (by decide),3,4,5] i)
  inj' := by
    intro a b equal
    have same := w.injective equal
    fin_cases source <;> fin_cases a <;> fin_cases b <;> simp_all

def emitTriple (extra : Nat) (w : TripleWorkspace extra) : Routine (extra+4) :=
  sequence (prepend (w 3) (Encoding.natural.encode 3).reverse)
    (sequence (copyReverse (extra+2) (tripleSourceRoles w 0))
      (sequence (copyReverse (extra+2) (tripleSourceRoles w 1))
        (copyReverse (extra+2) (tripleSourceRoles w 2))))

theorem emitTriple_words (extra : Nat) (w : TripleWorkspace extra)
    (store : Fin (extra+6) → List Bool) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    Executes (emitTriple extra w) store
      (7*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length)+25)
      (Function.update store (w 3)
        ((Encoding.natural.encode 3++store (w 0)++store (w 1)++store (w 2)).reverse++store (w 3))) := by
  let header := (Encoding.natural.encode 3).reverse
  let first := Function.update store (w 3) (header++store (w 3))
  let second := Function.update first (w 3) ((store (w 0)).reverse++first (w 3))
  let third := Function.update second (w 3) ((store (w 1)).reverse++second (w 3))
  have headerRun := prepend_executes (w 3) header store
  have a := copyReverse_executes (extra+2) (tripleSourceRoles w 0) first
    (by simp [tripleSourceRoles,first,w.injective.eq_iff,e4])
    (by simp [tripleSourceRoles,first,w.injective.eq_iff,e5])
  have b := copyReverse_executes (extra+2) (tripleSourceRoles w 1) second
    (by simp [tripleSourceRoles,second,first,w.injective.eq_iff,e4])
    (by simp [tripleSourceRoles,second,first,w.injective.eq_iff,e5])
  have c := copyReverse_executes (extra+2) (tripleSourceRoles w 2) third
    (by simp [tripleSourceRoles,third,second,first,w.injective.eq_iff,e4])
    (by simp [tripleSourceRoles,third,second,first,w.injective.eq_iff,e5])
  have firstSource : first (tripleSourceRoles w 0 0)=store (w 0) := by simp [first,tripleSourceRoles,w.injective.eq_iff]
  have secondSource : second (tripleSourceRoles w 1 0)=store (w 1) := by simp [second,first,tripleSourceRoles,w.injective.eq_iff]
  have thirdSource : third (tripleSourceRoles w 2 0)=store (w 2) := by simp [third,second,first,tripleSourceRoles,w.injective.eq_iff]
  rw [firstSource] at a
  rw [secondSource] at b
  rw [thirdSource] at c
  have combined := headerRun.sequence (a.sequence (b.sequence c))
  convert combined using 1
  · rfl
  · have length : header.length=5 := by decide
    rw [length]
    omega
  · change Function.update store (w 3)
      ((Encoding.natural.encode 3++store (w 0)++store (w 1)++store (w 2)).reverse++store (w 3)) =
      Function.update third (w 3) ((store (w 2)).reverse++third (w 3))
    simp only [third,second,first,Function.update_self,Function.update_idem,
      List.reverse_append,List.append_assoc,header]

theorem emitTriple_literals (extra : Nat) (w : TripleWorkspace extra)
    (store : Fin (extra+6) → List Bool) (a b c : Nat×Bool)
    (first : store (w 0)=literalCodec.encode a) (second : store (w 1)=literalCodec.encode b)
    (third : store (w 2)=literalCodec.encode c) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    Executes (emitTriple extra w) store
      (7*((literalCodec.encode a).length+(literalCodec.encode b).length+(literalCodec.encode c).length)+25)
      (Function.update store (w 3) (((Encoding.list literalCodec).encode [a,b,c]).reverse++store (w 3))) := by
  simpa only [first,second,third,Encoding.list,Encoding.sequence,List.length_cons,List.length_nil,List.append_nil,
    List.append_assoc] using emitTriple_words extra w store e4 e5

end Counting.StackMachine.Routine
