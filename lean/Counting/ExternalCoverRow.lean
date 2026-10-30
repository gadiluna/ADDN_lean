import Counting.ExternalCoverRowLayout
import Counting.ExternalMatchingEmitter

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

 theorem generateRow_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (a b c : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode [a,b,c]++suffix)
    (status : store (w 1)=accepted::tail)
    (ha : a≤(store (w 17)).length) (hb : b≤(store (w 17)).length) (hc : c≤(store (w 17)).length)
    (empty : ∀ i∈rowScratch,store (w i)=[]) :
    ∃ time ≤ 4000*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (generateRow extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 36)
          (((Encoding.list Encoding.natural).encode [a,(store (w 17)).length+b,2*(store (w 17)).length+c]).reverse++store (w 36))) := by
  let q := (store (w 17)).length
  let ca := Encoding.natural.encode a
  let cb := Encoding.natural.encode (q+b)
  let cc := Encoding.natural.encode (2*q+c)
  let rest2 := Encoding.natural.encode c++suffix
  let rest1 := Encoding.natural.encode b++rest2
  let body := Encoding.natural.encode a++rest1
  let parsed := Function.update (Function.update store (w 0) body) (w 18) (Encoding.natural.encode 3)
  obtain ⟨headerTime,headerBound,headerRun⟩ := readNatural_executes (extra+16) w.reader store 3 accepted body tail
    (by simpa [RowWorkspace.reader,rowReaderPositions,Encoding.list,Encoding.sequence,List.append_assoc] using source)
    status (by
      intro i mem
      simp only [List.mem_cons,List.not_mem_nil] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|h
      all_goals first | contradiction | simpa [RowWorkspace.reader,rowReaderPositions] using empty _ (by decide))
  change Executes (readNatural (extra+16) w.reader) store headerTime parsed at headerRun
  have clearingHeader := clear_executes (w 18) parsed
  have headerSize : (parsed (w 18)).length=5 := by simp only [parsed,Function.update_self];decide
  rw [headerSize] at clearingHeader
  let ready := Function.update store (w 0) body
  have headerFinal : Function.update parsed (w 18) []=ready := by
    funext r
    by_cases e : r=w 18
    · subst r;simp [ready,w.injective.eq_iff,empty,rowScratch]
    · simp [parsed,ready,e]
  rw [headerFinal] at clearingHeader
  have coordinateEmpty (r : Fin 48) (mem : r∈([2,3,4,5,6,9,10,11,12,18,19,20,26,28,29,30] : List (Fin 48))) :
      store (w r)=[] := empty r (by
    simp only [rowScratch,List.mem_cons,List.not_mem_nil] at mem ⊢;tauto)
  have different (r : Fin 48) (mem : r∈([2,3,4,5,6,9,10,11,12,18,19,20,26,28,29,30] : List (Fin 48))) :
      r≠0 ∧ r≠32 ∧ r≠33 ∧ r≠34 := by
    simp only [List.mem_cons,List.not_mem_nil] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | decide
  obtain ⟨t0,b0,r0⟩ := readCoordinate_executes extra w 0 ready a accepted rest1 tail
    (by simp [ready,body]) (by simp [ready,w.injective.eq_iff,status])
    (by simpa [ready,w.injective.eq_iff] using ha)
    (fun i mem=>by simpa [ready,w.injective.eq_iff,(different i mem).1] using coordinateEmpty i mem)
  let s1 := Function.update (Function.update store (w 0) rest1) (w 32) ca
  have s1Eq : Function.update (Function.update ready (w 0) rest1) (w (codePosition 0))
      (Encoding.natural.encode (0*(ready (w 17)).length+a)++ready (w (codePosition 0)))=s1 := by
    simp [ready,s1,codePosition,ca,w.injective.eq_iff,empty,rowScratch]
  rw [show (0 : Fin 3).val=0 by rfl,s1Eq] at r0
  obtain ⟨t1,b1,r1⟩ := readCoordinate_executes extra w 1 s1 b accepted rest2 tail
    (by simp [s1,rest1,w.injective.eq_iff]) (by simp [s1,w.injective.eq_iff,status])
    (by simpa [s1,w.injective.eq_iff] using hb)
    (fun i mem=>by simpa [s1,w.injective.eq_iff,(different i mem).1,(different i mem).2.1] using coordinateEmpty i mem)
  let s2 := Function.update (Function.update s1 (w 0) rest2) (w 33) cb
  have s2Eq : Function.update (Function.update s1 (w 0) rest2) (w (codePosition 1))
      (Encoding.natural.encode (1*(s1 (w 17)).length+b)++s1 (w (codePosition 1)))=s2 := by
    simp [s1,s2,codePosition,cb,q,w.injective.eq_iff,empty,rowScratch]
  rw [show (1 : Fin 3).val=1 by rfl,s2Eq] at r1
  obtain ⟨t2,b2,r2⟩ := readCoordinate_executes extra w 2 s2 c accepted suffix tail
    (by simp [s2,rest2,w.injective.eq_iff]) (by simp [s2,s1,w.injective.eq_iff,status])
    (by simpa [s2,s1,w.injective.eq_iff] using hc)
    (fun i mem=>by simpa [s2,s1,w.injective.eq_iff,(different i mem).1,(different i mem).2.1,(different i mem).2.2.1] using coordinateEmpty i mem)
  let s3 := Function.update (Function.update s2 (w 0) suffix) (w 34) cc
  have s3Eq : Function.update (Function.update s2 (w 0) suffix) (w (codePosition 2))
      (Encoding.natural.encode (2*(s2 (w 17)).length+c)++s2 (w (codePosition 2)))=s3 := by
    simp [s3,s2,s1,codePosition,cc,q,w.injective.eq_iff,empty,rowScratch]
  rw [show (2 : Fin 3).val=2 by rfl,s3Eq] at r2
  have emitter := emitTripleSelected_words (extra+42) w.triple id s3
    (by simp [RowWorkspace.triple,rowTriplePositions,s3,s2,s1,w.injective.eq_iff,empty,rowScratch])
    (by simp [RowWorkspace.triple,rowTriplePositions,s3,s2,s1,w.injective.eq_iff,empty,rowScratch])
  let row := (Encoding.list Encoding.natural).encode [a,q+b,2*q+c]
  let emitted := Function.update s3 (w 36) (row.reverse++store (w 36))
  have emitterAs : Executes (emitTripleSelected (extra+42) w.triple id) s3
      (7*(ca.length+cb.length+cc.length)+25) emitted := by
    simpa [RowWorkspace.triple,rowTriplePositions,s3,s2,s1,emitted,row,ca,cb,cc,w.injective.eq_iff,
      Encoding.list,Encoding.sequence,List.append_assoc] using emitter
  have codeA := MatchingMachine.natural_length_le a
  have codeB := MatchingMachine.natural_length_le (q+b)
  have codeC := MatchingMachine.natural_length_le (2*q+c)
  have selectedBound (r : Fin (extra+48)) (mem : r∈[w 32,w 33,w 34]) : (emitted r).length≤6*q+1 := by
    simp only [List.mem_cons,List.not_mem_nil] at mem
    rcases mem with rfl|rfl|rfl|h
    · have eq : emitted (w 32)=ca := by simp [emitted,s3,s2,s1,w.injective.eq_iff]
      rw [eq];dsimp [ca];dsimp [q] at *;omega
    · have eq : emitted (w 33)=cb := by simp [emitted,s3,s2,w.injective.eq_iff]
      rw [eq];dsimp [cb];dsimp [q] at *;omega
    · have eq : emitted (w 34)=cc := by simp [emitted,s3,w.injective.eq_iff]
      rw [eq];dsimp [cc];dsimp [q] at *;omega
    · contradiction
  obtain ⟨clearTime,clearBound,clearRun⟩ := clearRegisters_selected_executes [w 32,w 33,w 34] emitted (6*q+1) selectedBound
  have final : clearedStore [w 32,w 33,w 34] emitted=
      Function.update (Function.update store (w 0) suffix) (w 36) (row.reverse++store (w 36)) := by
    funext r
    by_cases e32 : r=w 32
    · subst r;simp [clearedStore,w.injective.eq_iff,empty,rowScratch]
    · by_cases e33 : r=w 33
      · subst r;simp [clearedStore,w.injective.eq_iff,empty,rowScratch]
      · by_cases e34 : r=w 34
        · subst r;simp [clearedStore,w.injective.eq_iff,empty,rowScratch]
        · by_cases e0 : r=w 0
          · subst r;simp [clearedStore,emitted,s3,s2,s1,w.injective.eq_iff]
          · simp [clearedStore,emitted,s3,s2,s1,e32,e33,e34,e0,Function.update_apply]
  rw [final] at clearRun
  refine ⟨_,?_,headerRun.sequence (clearingHeader.sequence (r0.sequence (r1.sequence (r2.sequence (emitterAs.sequence clearRun)))))⟩
  let S := (store (w 0)).length+q+1
  have suffixBounds : body.length≤(store (w 0)).length ∧ rest1.length≤(store (w 0)).length ∧ rest2.length≤(store (w 0)).length := by
    rw [source];dsimp only [body,rest1,rest2]
    simp only [Encoding.list,Encoding.sequence,List.length_cons,List.length_nil,List.length_append,List.append_nil]
    omega
  have limits : t0≤1000*S^3 ∧ t1≤1000*S^3 ∧ t2≤1000*S^3 := by
    constructor
    · apply b0.trans;apply Nat.mul_le_mul_left;apply Nat.pow_le_pow_left
      simpa [ready,w.injective.eq_iff,S,q] using Nat.add_le_add_right (Nat.add_le_add_right suffixBounds.1 q) 1
    · constructor
      · apply b1.trans;apply Nat.mul_le_mul_left;apply Nat.pow_le_pow_left
        simpa [s1,w.injective.eq_iff,S,q] using Nat.add_le_add_right (Nat.add_le_add_right suffixBounds.2.1 q) 1
      · apply b2.trans;apply Nat.mul_le_mul_left;apply Nat.pow_le_pow_left
        simpa [s2,s1,w.injective.eq_iff,S,q] using Nat.add_le_add_right (Nat.add_le_add_right suffixBounds.2.2 q) 1
  have linear : S≤S^3 := Nat.le_self_pow (by decide) S
  have positive : 1≤S^3 := Nat.one_le_pow _ _ (by dsimp [S];omega)
  change headerTime≤60*((store (w 0)).length+1) at headerBound
  simp only [List.length_cons,List.length_nil] at clearBound
  change _≤4000*S^3
  dsimp only [ca,cb,cc]
  dsimp only [q,S] at *
  omega

end Counting.External.CoverMachine
