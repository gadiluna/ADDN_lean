import Counting.ExternalMatchingGeneratorLayout

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def matchingFinalize (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (clear (w 1)) (sequence (ofProgram (ListPrograms.reverseProgram (extra+62) (w 36) (w 1)))
    (CNFMachine.formulaHeaders (extra+58) w.headers))

def matchingFinalizeCost (order edges streamLength : Nat) :=
  2*streamLength+20*(edges+1)^2+28*(order+1)^2+6

theorem matchingFinalize_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (order edges : Nat) (stream : List Bool) (flag : Bool) (store : Fin (extra+64) → List Bool)
    (orderValue : store (w 48)=List.replicate order true) (edgesValue : (store (w 50)).length=edges)
    (output : store (w 36)=stream.reverse) (status : store (w 1)=[flag])
    (e18 : store (w 18)=[]) (e19 : store (w 19)=[]) (e59 : store (w 59)=[]) :
    ∃ time ≤ matchingFinalizeCost order edges stream.length,
      Executes (matchingFinalize extra w) store time
        (Function.update (Function.update store (w 36) []) (w 1)
          ((Encoding.list Encoding.boolean).encode (List.replicate order true)++Encoding.natural.encode edges++stream)) := by
  have clearing := clear_executes (w 1) store
  rw [status] at clearing
  let s1 := Function.update store (w 1) []
  have reversing := reverse_executes (extra+62) (w 36) (w 1) (by simp [w.injective.eq_iff]) s1
  have data : s1 (w 36)=stream.reverse := by simp [s1,w.injective.eq_iff,output]
  rw [data,List.length_reverse,List.reverse_reverse] at reversing
  let s2 := Function.update (Function.update store (w 36) []) (w 1) stream
  have reverseResult : Function.update (Function.update s1 (w 36) []) (w 1) (stream++s1 (w 1))=s2 := by
    funext r
    by_cases a : r=w 1
    · subst r;simp [s1,s2]
    · simp [s1,s2,Function.update_apply,a]
  rw [reverseResult] at reversing
  obtain ⟨ht,hb,headers⟩ := CNFMachine.formulaHeaders_executes (extra+58) w.headers order edges s2
    (by simp [GeneratorWorkspace.headers,generatorHeaderPositions,s2,w.injective.eq_iff,orderValue])
    (by simpa [GeneratorWorkspace.headers,generatorHeaderPositions,s2,w.injective.eq_iff] using edgesValue)
    (by simp [GeneratorWorkspace.headers,generatorHeaderPositions,s2,w.injective.eq_iff,e18])
    (by simp [GeneratorWorkspace.headers,generatorHeaderPositions,s2,w.injective.eq_iff,e19])
    (by simp [GeneratorWorkspace.headers,generatorHeaderPositions,s2,w.injective.eq_iff,e59])
  have combined := clearing.sequence (reversing.sequence headers)
  refine ⟨2+1+(2*stream.length+1+1+ht),?_,?_⟩
  · dsimp only [matchingFinalizeCost];omega
  · simpa [matchingFinalize,GeneratorWorkspace.headers,generatorHeaderPositions,s2,List.append_assoc] using combined

end Counting.External.MatchingMachine
