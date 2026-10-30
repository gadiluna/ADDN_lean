import Counting.ExternalMatchingLiteralLayout

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem generateLiteral_executes (extra : Nat) (w : LiteralWorkspace extra)
    (store : Fin (extra+48) → List Bool) (index width occurrence shift : Nat)
    (sign accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.product Encoding.natural Encoding.boolean).encode (index,sign)++suffix)
    (status : store (w 1)=accepted::tail) (fits : index ≤ (store (w 17)).length)
    (widthValue : store (w 32)=List.replicate width true)
    (occurrenceValue : store (w 34)=List.replicate occurrence true)
    (shiftValue : store (w 33)=List.replicate shift true)
    (empty : ∀ i∈generateLiteralScratch,store (w i)=[]) :
    ∃ time ≤ generateLiteralCost (store (w 0)).length (store (w 17)).length width occurrence shift (store (w 35)).length,
      Executes (generateLiteral extra w) store time (generateLiteralResult extra w store index sign suffix) := by
  let n := (store (w 17)).length
  let first := (store (w 35)).length
  let port := portValue index width occurrence shift sign
  have readEmpty (i : Fin 32) (member : i∈matchingLiteralScratch) : store (w.reader i)=[] := by
    simp only [matchingLiteralScratch,List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simpa [LiteralWorkspace.reader] using empty _ (by simp [generateLiteralScratch])
  obtain ⟨readTime,readBound,readRun⟩ := readMatchingLiteral_executes (extra+16) w.reader store index sign accepted suffix tail
    source status fits readEmpty
  let read := Function.update (Function.update (Function.update store (w 0) suffix) (w 26) (List.replicate index true)) (w 21) [sign]
  have portRun := computePort_executes (extra+40) w.port read index width occurrence shift sign
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff])
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff,widthValue])
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff,occurrenceValue])
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff,shiftValue])
    (by simp [LiteralWorkspace.port,literalPortPositions,read])
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff,empty,generateLiteralScratch])
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff,empty,generateLiteralScratch])
    (by simp [LiteralWorkspace.port,literalPortPositions,read,w.injective.eq_iff,empty,generateLiteralScratch])
  let ported := Function.update (Function.update read (w 21) []) (w 37) (List.replicate port true)
  have portAs : Executes (computePort (extra+40) w.port) read (portCost index width occurrence shift sign) ported := portRun
  have copying := copy_executes (extra+45) (w 35) (w 27) (w 39) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) ported
    (by simp [ported,read,w.injective.eq_iff,empty,generateLiteralScratch])
  let copied := Function.update ported (w 27) (store (w 35))
  have copyRun : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 35) (w 27) (w 39))) ported (5*first+2) copied := by
    simpa +instances [copied,ported,read,first,w.injective.eq_iff,empty,generateLiteralScratch,ListPrograms.copyProgram] using copying
  have edgeEmpty (i : Fin 12) (member : i∈([3,4,5,7,8,9,10,11] : List (Fin 12))) : copied (w.edge i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [LiteralWorkspace.edge,literalEdgePositions,copied,ported,read,w.injective.eq_iff,empty,generateLiteralScratch]
  obtain ⟨edgeTime,edgeBound,edgeRun⟩ := emitEdge_executes (extra+36) w.edge copied edgeEmpty
  let edge := (Encoding.list Encoding.natural).encode (literalEdge first index width occurrence shift sign)
  let emitted := Function.update copied (w 36) (edge.reverse++store (w 36))
  have emit : Executes (emitEdge (extra+36) w.edge) copied edgeTime emitted := by
    simpa [LiteralWorkspace.edge,literalEdgePositions,copied,ported,read,emitted,edge,literalEdge,first,port,w.injective.eq_iff] using edgeRun
  have portBound : port ≤ n*width+occurrence+shift := by
    have product := Nat.mul_le_mul_right width fits
    dsimp [port,portValue,n] at *
    cases sign <;> simp only [if_true,Bool.false_eq_true,if_false] <;> omega
  have selected (r : Fin (extra+48)) (member : r∈[w 26,w 27,w 37]) :
      (emitted r).length ≤ n+first+n*width+occurrence+shift := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|h
    · simp only [emitted,copied,ported,read,Function.update_of_ne (w.injective.ne (by decide : (26:Fin 48)≠36)),
        Function.update_of_ne (w.injective.ne (by decide : (26:Fin 48)≠27)),Function.update_of_ne (w.injective.ne (by decide : (26:Fin 48)≠37)),
        Function.update_of_ne (w.injective.ne (by decide : (26:Fin 48)≠21)),Function.update_self,List.length_replicate]
      omega
    · have eq : emitted (w 27)=store (w 35) := by simp [emitted,copied,w.injective.eq_iff]
      rw [eq];dsimp [first];omega
    · have eq : emitted (w 37)=List.replicate port true := by simp [emitted,copied,ported,w.injective.eq_iff]
      rw [eq,List.length_replicate];omega
    · contradiction
  obtain ⟨clearTime,clearBound,clearRun⟩ := clearRegisters_selected_executes [w 26,w 27,w 37] emitted
    (n+first+n*width+occurrence+shift) selected
  let cleaned := Function.update (Function.update store (w 0) suffix) (w 36) (edge.reverse++store (w 36))
  have clearEq : clearedStore [w 26,w 27,w 37] emitted=cleaned := by
    funext r
    by_cases a : r=w 26
    · subst r;simp [clearedStore,cleaned,w.injective.eq_iff,empty,generateLiteralScratch]
    · by_cases b : r=w 27
      · subst r;simp [clearedStore,cleaned,w.injective.eq_iff,empty,generateLiteralScratch]
      · by_cases c : r=w 37
        · subst r;simp [clearedStore,cleaned,w.injective.eq_iff,empty,generateLiteralScratch]
        · by_cases d : r=w 21
          · subst r;simp [clearedStore,emitted,copied,ported,cleaned,w.injective.eq_iff,empty,generateLiteralScratch]
          · simp [clearedStore,emitted,copied,ported,read,cleaned,a,b,c,d,Function.update_apply]
  rw [clearEq] at clearRun
  have increment := pushBit_executes (w 34) true cleaned
  have final : Function.update cleaned (w 34) (true::cleaned (w 34))=generateLiteralResult extra w store index sign suffix := by
    funext r
    by_cases e34 : r=w 34
    · subst r;simp [cleaned,generateLiteralResult,w.injective.eq_iff]
    · simp [cleaned,generateLiteralResult,edge,literalEdge,first,widthValue,occurrenceValue,shiftValue,e34,Function.update_apply]
  rw [final] at increment
  have combined := readRun.sequence (portAs.sequence (copyRun.sequence (emit.sequence (clearRun.sequence increment))))
  refine ⟨readTime+1+(portCost index width occurrence shift sign+1+(5*first+2+1+(edgeTime+1+(clearTime+1+1)))),?_,combined⟩
  have portTime := portCost_le index width occurrence shift (n+width+occurrence+shift) sign (by dsimp [n];omega) (by omega) (by omega) (by omega)
  have edgeLimit : edgeTime ≤ 300*(2*first+n*width+occurrence+shift+1)^2 := by
    apply edgeBound.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp [LiteralWorkspace.edge,literalEdgePositions,copied,ported,read,w.injective.eq_iff]
    dsimp [first]
    omega
  change readTime ≤ 200*((store (w 0)).length+n+1)^3 at readBound
  simp only [List.length_cons,List.length_nil] at clearBound
  change _ ≤ generateLiteralCost (store (w 0)).length n width occurrence shift first
  unfold generateLiteralCost
  omega

end Counting.External.MatchingMachine
