import Counting.ExternalMatchingGeneratorLayout
import Counting.StackScaleLength

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false

def coverCounts (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (scaleLength (extra+61) (w 17) (w 48) (w 59) 3)
    (ofProgram (ListPrograms.copyProgram (extra+61) (w 25) (w 50) (w 59)))

theorem coverCounts_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (q m : Nat)
    (hq : (store (w 17)).length=q) (hm : store (w 25)=List.replicate m true)
    (e48 : store (w 48)=[]) (e50 : store (w 50)=[]) (e59 : store (w 59)=[]) :
    Executes (coverCounts extra w) store (15*q+5*m+12)
      (Function.update (Function.update store (w 48) (List.replicate (3*q) true)) (w 50) (List.replicate m true)) := by
  have scale := scaleLength_executes (extra+61) (w 17) (w 48) (w 59)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) 3 store e59
  simp only [hq,e48,List.append_nil] at scale
  let scaled := Function.update store (w 48) (List.replicate (3*q) true)
  have copy := copy_executes (extra+61) (w 25) (w 50) (w 59)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) scaled
    (by simp [scaled,w.injective.eq_iff,e59])
  have source : scaled (w 25)=List.replicate m true := by simp [scaled,w.injective.eq_iff,hm]
  have output : scaled (w 50)=[] := by simp [scaled,w.injective.eq_iff,e50]
  rw [source,output,List.append_nil,List.length_replicate] at copy
  convert scale.sequence copy using 1 <;> first | rfl | omega

end Counting.External.CoverMachine
