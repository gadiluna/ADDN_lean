import Counting.StackEmitTripleSelected

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Current±, next±, atom±, reversed output, buffer, scratch. -/
abbrev GateWorkspace (extra : Nat) := Fin 9 ↪ Fin (extra+9)

def gatePositions (row : Fin 3) : Fin 6 ↪ Fin 9 :=
  ⟨![![1,4,2,6,7,8],![0,5,2,6,7,8],![0,3,2,6,7,8]] row,by
    intro i j same
    fin_cases row <;> fin_cases i <;> fin_cases j <;> simp_all⟩

def gateRoles (extra : Nat) (w : GateWorkspace extra) (row : Fin 3) : TripleWorkspace (extra+3) :=
  (gatePositions row).trans w

def gateEmitter (extra : Nat) (w : GateWorkspace extra) : Routine (extra+7) :=
  sequence (emitTripleSelected (extra+3) (gateRoles extra w 0) ![0,1,2])
    (sequence (emitTripleSelected (extra+3) (gateRoles extra w 1) ![0,1,1])
      (emitTripleSelected (extra+3) (gateRoles extra w 2) ![0,1,1]))

def gateClauses (current : Nat) (atom : Nat×Bool) : List (List (Nat×Bool)) :=
  [[(current,false),atom,(current+1,true)],
   [(current,true),(atom.1,!atom.2),(atom.1,!atom.2)],
   [(current,true),(current+1,false),(current+1,false)]]

def gateSource (current : Nat) (atom : Nat×Bool) : Fin 6 → Nat×Bool :=
  ![(current,true),(current,false),(current+1,true),(current+1,false),atom,(atom.1,!atom.2)]

theorem gateEmitter_executes (extra : Nat) (w : GateWorkspace extra) (store : Fin (extra+9) → List Bool)
    (current : Nat) (atom : Nat×Bool) (limit : Nat)
    (source : ∀ i : Fin 6,store (w (Fin.castLE (by decide) i))=literalCodec.encode (gateSource current atom i))
    (bounded : ∀ i : Fin 6,(literalCodec.encode (gateSource current atom i)).length≤limit)
    (e7 : store (w 7)=[]) (e8 : store (w 8)=[]) :
    ∃ time ≤ 63*limit+77,
      Executes (gateEmitter extra w) store time
        (Function.update store (w 6)
          ((Encoding.sequence (Encoding.list literalCodec) (gateClauses current atom)).reverse++store (w 6))) := by
  let c0 := (Encoding.list literalCodec).encode [(current,false),atom,(current+1,true)]
  let c1 := (Encoding.list literalCodec).encode [(current,true),(atom.1,!atom.2),(atom.1,!atom.2)]
  let c2 := (Encoding.list literalCodec).encode [(current,true),(current+1,false),(current+1,false)]
  let s1 := Function.update store (w 6) (c0.reverse++store (w 6))
  let s2 := Function.update s1 (w 6) (c1.reverse++s1 (w 6))
  have r0 := emitTripleSelected_literals (extra+3) (gateRoles extra w 0) ![0,1,2]
    ![(current,false),atom,(current+1,true)] store
    (by intro i; fin_cases i
        · exact source 1
        · exact source 4
        · exact source 2)
    e7 e8
  have r1 := emitTripleSelected_literals (extra+3) (gateRoles extra w 1) ![0,1,1]
    ![(current,true),(atom.1,!atom.2),(current+1,true)] s1
    (by intro i;fin_cases i <;> simp [gateRoles,gatePositions,s1,w.injective.eq_iff];all_goals first | exact source 0 | exact source 5 | exact source 2)
    (by simp [gateRoles,gatePositions,s1,w.injective.eq_iff,e7])
    (by simp [gateRoles,gatePositions,s1,w.injective.eq_iff,e8])
  have r2 := emitTripleSelected_literals (extra+3) (gateRoles extra w 2) ![0,1,1]
    ![(current,true),(current+1,false),(current+1,true)] s2
    (by intro i;fin_cases i <;> simp [gateRoles,gatePositions,s2,s1,w.injective.eq_iff];all_goals first | exact source 0 | exact source 3 | exact source 2)
    (by simp [gateRoles,gatePositions,s2,s1,w.injective.eq_iff,e7])
    (by simp [gateRoles,gatePositions,s2,s1,w.injective.eq_iff,e8])
  let L0 := (literalCodec.encode (current,false)).length+(literalCodec.encode atom).length+(literalCodec.encode (current+1,true)).length
  let L1 := (literalCodec.encode (current,true)).length+(literalCodec.encode (atom.1,!atom.2)).length+(literalCodec.encode (atom.1,!atom.2)).length
  let L2 := (literalCodec.encode (current,true)).length+(literalCodec.encode (current+1,false)).length+(literalCodec.encode (current+1,false)).length
  change Executes _ store (7*L0+25) s1 at r0
  change Executes _ s1 (7*L1+25) s2 at r1
  change Executes _ s2 (7*L2+25) (Function.update s2 (w 6) (c2.reverse++s2 (w 6))) at r2
  have finalStore : Function.update s2 (w 6) (c2.reverse++s2 (w 6))=
      Function.update store (w 6) ((Encoding.sequence (Encoding.list literalCodec) (gateClauses current atom)).reverse++store (w 6)) := by
    simp [s2,s1,c0,c1,c2,gateClauses,Encoding.sequence,List.reverse_append,List.append_assoc]
  rw [finalStore] at r2
  have combined := r0.sequence (r1.sequence r2)
  refine ⟨7*L0+25+1+(7*L1+25+1+(7*L2+25)),?_,combined⟩
  have b0 := bounded 0
  have b1 := bounded 1
  have b2 := bounded 2
  have b3 := bounded 3
  have b4 := bounded 4
  have b5 := bounded 5
  dsimp [gateSource] at b0 b1 b2 b3 b4 b5
  dsimp [L0,L1,L2]
  omega

end Counting.External.CNFMachine
