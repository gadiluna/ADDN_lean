import Counting.StackEmitTriple

namespace Counting.StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Select the three literal sources independently. Repeated selections require
no additional copies of the input data. All six workspace registers are distinct. -/
def emitTripleSelected (extra : Nat) (w : TripleWorkspace extra)
    (selection : Fin 3 → Fin 3) : Routine (extra+4) :=
  sequence (prepend (w 3) (Encoding.natural.encode 3).reverse)
    (sequence (copyReverse (extra+2) (tripleSourceRoles w (selection 0)))
      (sequence (copyReverse (extra+2) (tripleSourceRoles w (selection 1)))
        (copyReverse (extra+2) (tripleSourceRoles w (selection 2)))))

theorem tripleSource_ne_output (w : TripleWorkspace extra) (source : Fin 3) :
    w (source.castLE (by decide)) ≠ w 3 := by
  apply w.injective.ne
  fin_cases source <;> decide

theorem emitTripleSelected_words (extra : Nat) (w : TripleWorkspace extra)
    (selection : Fin 3 → Fin 3) (store : Fin (extra+6) → List Bool)
    (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    let word := fun i => store (w ((selection i).castLE (by decide)))
    Executes (emitTripleSelected extra w selection) store
      (7*((word 0).length+(word 1).length+(word 2).length)+25)
      (Function.update store (w 3)
        ((Encoding.natural.encode 3++word 0++word 1++word 2).reverse++store (w 3))) := by
  dsimp only
  let word := fun i => store (w ((selection i).castLE (by decide)))
  let header := (Encoding.natural.encode 3).reverse
  let first := Function.update store (w 3) (header++store (w 3))
  let second := Function.update first (w 3) ((word 0).reverse++first (w 3))
  let third := Function.update second (w 3) ((word 1).reverse++second (w 3))
  have headerRun := prepend_executes (w 3) header store
  have a := copyReverse_executes (extra+2) (tripleSourceRoles w (selection 0)) first
    (by simp [tripleSourceRoles,first,w.injective.eq_iff,e4])
    (by simp [tripleSourceRoles,first,w.injective.eq_iff,e5])
  have b := copyReverse_executes (extra+2) (tripleSourceRoles w (selection 1)) second
    (by simp [tripleSourceRoles,second,first,w.injective.eq_iff,e4])
    (by simp [tripleSourceRoles,second,first,w.injective.eq_iff,e5])
  have c := copyReverse_executes (extra+2) (tripleSourceRoles w (selection 2)) third
    (by simp [tripleSourceRoles,third,second,first,w.injective.eq_iff,e4])
    (by simp [tripleSourceRoles,third,second,first,w.injective.eq_iff,e5])
  have firstSource : first (tripleSourceRoles w (selection 0) 0)=word 0 := by
    change first (w ((selection 0).castLE (by decide)))=word 0
    simp only [first,Function.update_of_ne (tripleSource_ne_output w _),word]
  have secondSource : second (tripleSourceRoles w (selection 1) 0)=word 1 := by
    change second (w ((selection 1).castLE (by decide)))=word 1
    simp only [second,first,Function.update_of_ne (tripleSource_ne_output w _),word]
  have thirdSource : third (tripleSourceRoles w (selection 2) 0)=word 2 := by
    change third (w ((selection 2).castLE (by decide)))=word 2
    simp only [third,second,first,Function.update_of_ne (tripleSource_ne_output w _),word]
  rw [firstSource] at a
  rw [secondSource] at b
  rw [thirdSource] at c
  have combined := headerRun.sequence (a.sequence (b.sequence c))
  convert combined using 1
  · rfl
  · have length : header.length=5 := by decide
    rw [length]
    dsimp only [word]
    omega
  · change Function.update store (w 3)
      ((Encoding.natural.encode 3++word 0++word 1++word 2).reverse++store (w 3)) =
      Function.update third (w 3) ((word 2).reverse++third (w 3))
    simp only [third,second,first,Function.update_self,Function.update_idem,
      List.reverse_append,List.append_assoc,header]

theorem emitTripleSelected_literals (extra : Nat) (w : TripleWorkspace extra)
    (selection : Fin 3 → Fin 3) (literals : Fin 3 → Nat×Bool)
    (store : Fin (extra+6) → List Bool)
    (sources : ∀ i : Fin 3, store (w (i.castLE (by decide)))=literalCodec.encode (literals i))
    (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    Executes (emitTripleSelected extra w selection) store
      (7*((literalCodec.encode (literals (selection 0))).length+
        (literalCodec.encode (literals (selection 1))).length+
        (literalCodec.encode (literals (selection 2))).length)+25)
      (Function.update store (w 3)
        (((Encoding.list literalCodec).encode
          [literals (selection 0),literals (selection 1),literals (selection 2)]).reverse++store (w 3))) := by
  simpa only [sources,Encoding.list,Encoding.sequence,List.length_cons,List.length_nil,
    List.append_nil,List.append_assoc] using emitTripleSelected_words extra w selection store e4 e5

end Counting.StackMachine.Routine
