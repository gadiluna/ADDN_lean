import Counting.StackEncodingListExact

namespace Counting.StackMachine.EncodingPrograms

/-- The generic parser's flag recognizes exactly the canonical prefix
language, including when arbitrary preexisting flag bits follow it. -/
theorem listPrefix_status_iff (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool) :
    (listPrefixStore extra w base (w 1)).head?=some true ↔
      ∃ values : List Nat, ∃ suffix, (Encoding.list Encoding.natural).encode values++suffix=base (w 0) := by
  simp only [listPrefixStore,w.injective.eq_iff,show (1:Fin 17)≠0 by decide,if_false,ite_true,
    List.head?_cons,Option.some.injEq]
  exact listScan_accept_iff _

/-- Both exposed outputs are determined by the actual canonical prefix;
all other registers are unchanged. -/
theorem listPrefix_roundtrip (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool) (values : List Nat) (suffix : List Bool)
    (input : base (w 0)=(Encoding.list Encoding.natural).encode values++suffix) :
    listPrefixStore extra w base = fun r => if r=w 0 then suffix
      else if r=w 1 then true::base (w 1)
      else if r=w 2 then Encoding.sequence Encoding.natural values else base r := by
  funext r
  simp only [listPrefixStore,input,listScan_append,List.reverse_reverse]

/-- On acceptance, the returned suffix and serialized body belong to the
same decoded list; this also covers any external registers used by callers. -/
theorem listPrefix_success (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool)
    (accepted : (listPrefixStore extra w base (w 1)).head?=some true) :
    ∃ values : List Nat,
      (Encoding.list Encoding.natural).encode values++listPrefixStore extra w base (w 0)=base (w 0) ∧
      listPrefixStore extra w base (w 2)=Encoding.sequence Encoding.natural values := by
  have status : (listScan (base (w 0))).accepted=true := by
    simpa only [listPrefixStore,w.injective.eq_iff,show (1:Fin 17)≠0 by decide,if_false,ite_true,
      List.head?_cons,Option.some.injEq] using accepted
  obtain ⟨values,split,body⟩:=listScan_sound (base (w 0)) status
  refine ⟨values,?_,?_⟩
  · simpa only [listPrefixStore,ite_true] using split
  · simp only [listPrefixStore,w.injective.eq_iff,show (2:Fin 17)≠0 by decide,
      show (2:Fin 17)≠1 by decide,if_false,ite_true,body,List.reverse_reverse]

theorem listExact_status_iff (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool) :
    (listExactStore extra w base (w 1)).head?=some true ↔
      ∃ values : List Nat, (Encoding.list Encoding.natural).encode values=base (w 0) := by
  simp only [listExactStore,w.injective.eq_iff,show (1:Fin 17)≠0 by decide,if_false,ite_true,
    List.head?_cons,Option.some.injEq,listCheck_decodeExact,Option.isSome_iff_exists]
  exact exists_congr fun values => Encoding.Codec.decodeExact_iff _ _ values

end Counting.StackMachine.EncodingPrograms
