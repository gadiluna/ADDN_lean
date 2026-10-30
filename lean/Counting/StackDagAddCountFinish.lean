import Counting.StackDagAddCountFlush
import Counting.StackEmitNatural
import Counting.StackRoutineMove

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def AddWorkspace.lengthEmitter (w : AddWorkspace extra) : PowerWorkspace (extra+15) :=
  (⟨![5,18,6,7,19],by decide⟩ : Fin 5 ↪ Fin 20).trans w

def finishEdges (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (ofProgram (ListPrograms.reverseProgram (extra+18) (w 3) (w 18)))
    (sequence (emitNatural (extra+15) w.lengthEmitter)
      (sequence (move (extra+17) (w 18) (w 3) (w 19)) (clear (w 5))))

/-- Reverse the generated sparse stream once, prepend its measured list
header, and restore every temporary register. -/
theorem finishEdges_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (edges : List (Nat×Nat)) (output : store (w 3)=(Encoding.sequence edgeCodec edges).reverse)
    (counter : store (w 5)=List.replicate edges.length true)
    (empty : ∀ j∈([6,7,18,19]:List (Fin 20)),store (w j)=[]) :
    ∃ time ≤ 40*((Encoding.sequence edgeCodec edges).length+edges.length+1)^2,
      Executes (finishEdges extra w) store time
        (Function.update (Function.update store (w 3) ((Encoding.list edgeCodec).encode edges)) (w 5) []) := by
  let stream:=Encoding.sequence edgeCodec edges
  have reversing:=reverse_executes (extra+18) (w 3) (w 18) (by simp [w.injective.eq_iff]) store
  rw [output,empty 18 (by simp),List.reverse_reverse,List.append_nil,List.length_reverse] at reversing
  let reversed:=Function.update (Function.update store (w 3) []) (w 18) stream
  obtain ⟨headerTime,headerBound,framing⟩:=emitNatural_executes (extra+15) w.lengthEmitter reversed
    (by simp [AddWorkspace.lengthEmitter,reversed,w.injective.eq_iff,empty])
    (by simp [AddWorkspace.lengthEmitter,reversed,w.injective.eq_iff,empty])
    (by simp [AddWorkspace.lengthEmitter,reversed,w.injective.eq_iff,empty])
  have countAt : (reversed (w.lengthEmitter 0)).length=edges.length := by
    simp [AddWorkspace.lengthEmitter,reversed,w.injective.eq_iff,counter]
  have targetAt : reversed (w.lengthEmitter 1)=stream := by simp [AddWorkspace.lengthEmitter,reversed]
  rw [countAt] at headerBound framing
  rw [targetAt] at framing
  let code:=(Encoding.list edgeCodec).encode edges
  let framed:=Function.update reversed (w 18) code
  change Executes (emitNatural (extra+15) w.lengthEmitter) reversed headerTime framed at framing
  have moving:=move_executes (extra+17) (w 18) (w 3) (w 19)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) framed
    (by simp [framed,reversed,w.injective.eq_iff,empty])
  have codeAt : framed (w 18)=code := by simp [framed]
  have outputAt : framed (w 3)=[] := by simp [framed,reversed,w.injective.eq_iff]
  rw [codeAt,outputAt,List.append_nil] at moving
  let moved:=Function.update (Function.update framed (w 3) code) (w 18) []
  have clearing:=clear_executes (w 5) moved
  have counterAt : moved (w 5)=List.replicate edges.length true := by
    simp [moved,framed,reversed,w.injective.eq_iff,counter]
  rw [counterAt,List.length_replicate] at clearing
  have final : Function.update moved (w 5) []=
      Function.update (Function.update store (w 3) code) (w 5) [] := by
    funext r
    by_cases a : r=w 18
    · subst r;simp [moved,w.injective.eq_iff,empty]
    · by_cases b : r=w 3
      · subst r;simp [moved,framed,reversed,w.injective.eq_iff]
      · simp [moved,framed,reversed,Function.update_apply,a,b]
  rw [final] at clearing
  have codeLength : code.length=2*edges.length.size+1+stream.length := by
    simp only [code,Encoding.list,List.length_append,Encoding.natural_length]
    rfl
  have headerSize : edges.length.size ≤ edges.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have combined:=reversing.sequence (framing.sequence (moving.sequence clearing))
  refine ⟨_,?_,combined⟩
  change 2*stream.length+1+1+(headerTime+1+(6*code.length+4+1+(edges.length+1))) ≤
    40*(stream.length+edges.length+1)^2
  nlinarith only [headerBound,codeLength,headerSize,Nat.zero_le stream.length,Nat.zero_le edges.length]

end Counting.StackMachine.DagUpdate
