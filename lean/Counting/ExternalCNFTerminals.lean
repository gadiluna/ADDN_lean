import Counting.StackEmitTripleSelected

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def emitTerminals (extra : Nat) (w : TripleWorkspace extra) : Routine (extra+4) :=
  sequence (emitTripleSelected extra w ![0,0,0]) (emitTripleSelected extra w ![1,1,1])

theorem emitTerminals_executes (extra : Nat) (w : TripleWorkspace extra)
    (store : Fin (extra+6) → List Bool) (base terminal : Nat)
    (first : store (w 0)=literalCodec.encode (base,true))
    (last : store (w 1)=literalCodec.encode (terminal,false))
    (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    Executes (emitTerminals extra w) store
      (21*((literalCodec.encode (base,true)).length+(literalCodec.encode (terminal,false)).length)+51)
      (Function.update store (w 3)
        ((Encoding.sequence (Encoding.list literalCodec)
          [List.replicate 3 (base,true),List.replicate 3 (terminal,false)]).reverse++store (w 3))) := by
  let positive := (Encoding.natural.encode 3++literalCodec.encode (base,true)++literalCodec.encode (base,true)++literalCodec.encode (base,true)).reverse
  let next := Function.update store (w 3) (positive++store (w 3))
  have a : Executes (emitTripleSelected extra w ![0,0,0]) store
      (7*((literalCodec.encode (base,true)).length+(literalCodec.encode (base,true)).length+(literalCodec.encode (base,true)).length)+25) next := by
    simpa [first,positive,next] using emitTripleSelected_words extra w ![0,0,0] store e4 e5
  have b := emitTripleSelected_words extra w ![1,1,1] next
    (by simp [next,w.injective.eq_iff,e4]) (by simp [next,w.injective.eq_iff,e5])
  dsimp only at b
  have sourceNext : next (w 1)=literalCodec.encode (terminal,false) := by simp [next,w.injective.eq_iff,last]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at b
  change Executes _ next (7*((next (w 1)).length+(next (w 1)).length+(next (w 1)).length)+25)
    (Function.update next (w 3) ((Encoding.natural.encode 3++next (w 1)++next (w 1)++next (w 1)).reverse++next (w 3))) at b
  rw [sourceNext] at b
  have combined := a.sequence b
  convert combined using 1
  · rfl
  · omega
  · simp only [next,positive,Encoding.sequence,Encoding.list,List.length_cons,List.length_nil,List.replicate_succ,
      List.replicate_zero,List.append_nil,Function.update_self,Function.update_idem,
      List.reverse_append,List.append_assoc]

end Counting.External.CNFMachine
