import Counting.StackEncodingIncomingPrefix
import Counting.StackEncodingListReadHeader
import Counting.StackDagClean

/-! Exact canonical-input semantics for the existing binary incoming checker.
The list may fail any graph condition; its serialized boundary remains exact. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

 theorem scanIncoming_canonical (bound previous : List Bool) (first accepted : Bool)
    (edges : List (Nat×Nat)) (suffix : List Bool) :
    let result:=scanIncoming bound edges.length
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix) previous first accepted
    result.suffix=suffix ∧
      result.accepted=(accepted && incomingCheck (Encoding.value bound) (incomingPrevious previous first) edges) := by
  induction edges generalizing previous first accepted with
  | nil=>simp [scanIncoming,Encoding.sequence,incomingCheck]
  | cons edge edges ih=>
    rcases edge with ⟨index,count⟩
    let rest:=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix
    have parsed : parsePair ((Encoding.product Encoding.natural Encoding.natural).encode (index,count)++rest)=
        ⟨index.bits,count.bits,rest,true⟩:=parsePair_frames _ _ _
    have item : incomingPayloadCheck bound previous first ⟨index.bits,count.bits,rest,true⟩=
        (decide (0<count) && decide (index<Encoding.value bound) &&
          (incomingPrevious previous first).all (fun p=>decide (p< index))) := by
      apply Bool.eq_iff_iff.mpr
      have result:=incomingPayloadCheck_frames bound previous first index count rest
      rw [parsed] at result
      simpa only [Bool.and_eq_true,decide_eq_true_eq,Option.all_eq_true,Option.mem_def,and_assoc] using result
    have tail:=ih index.bits false (accepted && incomingPayloadCheck bound previous first
      ⟨index.bits,count.bits,rest,true⟩)
    simp only [List.length_cons,Encoding.sequence,List.append_assoc,scanIncoming]
    change (scanIncoming bound edges.length (parsePair _).suffix (parsePair _).first false _).suffix=suffix ∧ _
    rw [parsed]
    refine ⟨tail.1,?_⟩
    rw [tail.2,item]
    simp only [incomingPrevious,Bool.false_eq_true,↓reduceIte,Encoding.value_bits,incomingCheck,Bool.and_assoc]

 theorem incomingPrefix_canonical (bound : Nat) (accepted : Bool) (edges : List (Nat×Nat))
    (suffix : List Bool) :
    let result:=incomingPrefixResult bound.bits
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix) [] true accepted
    result.suffix=suffix ∧ result.accepted=(accepted && incomingCheck bound none edges) := by
  have positive (edge : Nat×Nat) : 0<((Encoding.product Encoding.natural Encoding.natural).encode edge).length:=by
    simp [Encoding.product,Encoding.natural_length]
  obtain ⟨rest,count,header⟩:=listHeader_natural (Encoding.product Encoding.natural Encoding.natural) positive edges suffix
  dsimp only
  simp only [incomingPrefixResult,rest,count,header,Bool.and_true]
  simpa only [Encoding.value_bits,incomingPrevious,↓reduceIte] using
    scanIncoming_canonical bound.bits [] true accepted edges suffix

end Counting.StackMachine.DagValidation
