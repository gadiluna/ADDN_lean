import Counting.StackDagAddCountMerge

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def edgeCodec : Encoding.Codec (Nat×Nat) := Encoding.product Encoding.natural Encoding.natural

def emittedResult (w : AddWorkspace extra) (store : Store (extra+18))
    (edges : List (Nat×Nat)) (pending : Bool) (tail : List Bool) : Store (extra+18) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 6) []) (w 7) []) (w 3) ((Encoding.sequence edgeCodec edges).reverse++store (w 3)))
    (w 5) (List.replicate edges.length true++store (w 5))) (w 4) (pending::tail)

theorem emitCurrent_result (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (i c : Nat) (pending : Bool) (tail : List Bool)
    (index : store (w 6)=i.bits) (count : store (w 7)=c.bits)
    (flag : store (w 4)=pending::tail) (buffer : store (w 15)=[]) (scratch : store (w 16)=[]) :
    Executes (emitCurrent extra w) store (9*(i.bits.length+c.bits.length)+19)
      (emittedResult w store [(i,c)] pending tail) := by
  have run:=emitCurrent_executes extra w store buffer scratch
  rw [index,count] at run
  convert run using 1
  funext r
  by_cases a : r=w 4
  · subst r;simp [emittedResult,w.injective.eq_iff,flag]
  · simp [emittedResult,edgeCodec,Encoding.sequence,Encoding.product,Encoding.natural,a]

def insertCurrent (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (emitNew extra w) (sequence (emitCurrent extra w) (finishPending extra w))

theorem insertCurrent_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count i c : Nat) (pending : Bool) (tail : List Bool)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (currentIndex : store (w 6)=i.bits) (currentCount : store (w 7)=c.bits)
    (flag : store (w 4)=pending::tail)
    (empty : ∀ j∈([8,9,10,15,16]:List (Fin 20)),store (w j)=[]) :
    Executes (insertCurrent extra w) store
      (14*(index.bits.length+count.bits.length)+9*(i.bits.length+c.bits.length)+49)
      (emittedResult w store [(index,count),(i,c)] false tail) := by
  have inserting:=emitNew_executes extra w store empty
  rw [query,increment] at inserting
  let inserted:=Function.update (Function.update store (w 3)
    ((edgeCodec.encode (index,count)).reverse++store (w 3))) (w 5) (true::store (w 5))
  change Executes (emitNew extra w) store (14*(index.bits.length+count.bits.length)+25) inserted at inserting
  have emitting:=emitCurrent_executes extra w inserted
    (by simp [inserted,w.injective.eq_iff,empty]) (by simp [inserted,w.injective.eq_iff,empty])
  have iAt : inserted (w 6)=i.bits := by simp [inserted,w.injective.eq_iff,currentIndex]
  have cAt : inserted (w 7)=c.bits := by simp [inserted,w.injective.eq_iff,currentCount]
  rw [iAt,cAt] at emitting
  let emitted:=Function.update (Function.update (Function.update (Function.update inserted
    (w 6) []) (w 7) []) (w 3) ((edgeCodec.encode (i,c)).reverse++inserted (w 3)))
    (w 5) (true::inserted (w 5))
  have finishing:=finishPending_executes extra w emitted pending tail
    (by simp [emitted,inserted,w.injective.eq_iff,flag])
  have final : Function.update emitted (w 4) (false::tail)=
      emittedResult w store [(index,count),(i,c)] false tail := by
    funext r
    by_cases a : r=w 3
    · subst r;simp [emittedResult,emitted,inserted,Encoding.sequence,List.reverse_append,List.append_assoc,w.injective.eq_iff]
    · by_cases b : r=w 5
      · subst r;simp [emittedResult,emitted,inserted,w.injective.eq_iff]
      · simp [emittedResult,emitted,inserted,Function.update_apply,a,b]
  rw [final] at finishing
  simpa only [insertCurrent,show 14*(index.bits.length+count.bits.length)+25+1+
    (9*(i.bits.length+c.bits.length)+19+1+3)=
      14*(index.bits.length+count.bits.length)+9*(i.bits.length+c.bits.length)+49 by omega]
    using inserting.sequence (emitting.sequence finishing)

def mergeAndEmit (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (mergeCurrent extra w) (sequence (emitCurrent extra w) (finishPending extra w))

theorem mergeAndEmit_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (count i c : Nat) (pending : Bool) (tail : List Bool)
    (increment : store (w 2)=count.bits) (currentIndex : store (w 6)=i.bits)
    (currentCount : store (w 7)=c.bits) (flag : store (w 4)=pending::tail)
    (empty : ∀ j∈([10,12,13,14,15,16]:List (Fin 20)),store (w j)=[]) :
    ∃ time ≤ 25*(count.bits.length+i.bits.length+c.bits.length)+56,
      Executes (mergeAndEmit extra w) store time (emittedResult w store [(i,c+count)] false tail) := by
  have coreEmpty (j : Fin 20) (member : j∈([10,12,13,14]:List (Fin 20))) : store (w j)=[] := by
    apply empty
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    tauto
  obtain ⟨time,bound,merging⟩:=mergeCurrent_executes extra w store coreEmpty
  rw [increment,currentCount,Encoding.value_bits,Encoding.value_bits] at merging
  rw [increment,currentCount] at bound
  let merged:=Function.update store (w 7) (c+count).bits
  have emitting:=emitCurrent_executes extra w merged
    (by simp [merged,w.injective.eq_iff,empty]) (by simp [merged,w.injective.eq_iff,empty])
  have iAt : merged (w 6)=i.bits := by simp [merged,w.injective.eq_iff,currentIndex]
  have cAt : merged (w 7)=(c+count).bits := by simp [merged]
  rw [iAt,cAt] at emitting
  let emitted:=Function.update (Function.update (Function.update (Function.update merged
    (w 6) []) (w 7) []) (w 3) ((edgeCodec.encode (i,c+count)).reverse++merged (w 3)))
    (w 5) (true::merged (w 5))
  have finishing:=finishPending_executes extra w emitted pending tail
    (by simp [emitted,merged,w.injective.eq_iff,flag])
  have final : Function.update emitted (w 4) (false::tail)=emittedResult w store [(i,c+count)] false tail := by
    funext r
    by_cases a : r=w 3
    · subst r;simp [emittedResult,emitted,merged,Encoding.sequence,w.injective.eq_iff]
    · by_cases b : r=w 5
      · subst r;simp [emittedResult,emitted,merged,w.injective.eq_iff]
      · by_cases d : r=w 7 <;> simp [emittedResult,emitted,merged,Function.update_apply,a,b,d]
  rw [final] at finishing
  have sumBound:=RealizabilityCheck.sum_bits_length c.bits count.bits
  simp only [Encoding.value_bits] at sumBound
  exact ⟨_,by omega,merging.sequence (emitting.sequence finishing)⟩

end Counting.StackMachine.DagUpdate
