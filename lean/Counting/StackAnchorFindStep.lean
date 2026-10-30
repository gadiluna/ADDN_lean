import Counting.StackAnchorFindItem

namespace Counting.StackMachine.AnchorFind
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

theorem cleanup_executes (input query key value result pending counter : List Bool) :
    Executes cleanup (file input query key value result pending [] counter)
      (key.length+value.length+3) (file input query [] [] result pending [] counter) := by
  have first := clear_executes (2:Fin 13) (file input query key value result pending [] counter)
  have firstStore : Function.update (file input query key value result pending [] counter) 2 []=
      file input query [] value result pending [] counter := by funext r;fin_cases r <;> simp [file]
  rw [firstStore] at first
  have second := clear_executes (3:Fin 13) (file input query [] value result pending [] counter)
  have secondStore : Function.update (file input query [] value result pending [] counter) 3 []=
      file input query [] [] result pending [] counter := by funext r;fin_cases r <;> simp [file]
  rw [secondStore] at second
  have composed := first.sequence second
  convert composed using 1
  simp [file]
  omega

theorem item_executes (query result counter : List Bool) (pending : Bool)
    (edge : Nat×Nat) (suffix : List Bool) :
    ∃ time ≤ 100*(((Encoding.product Encoding.natural Encoding.natural).encode edge).length+
        suffix.length+query.length+result.length+1),
      Executes item
        (file ((Encoding.product Encoding.natural Encoding.natural).encode edge++suffix)
          query [] [] result [pending] [] counter) time
        (file suffix query [] [] (if pending && decide (query=edge.1.bits) then edge.2.bits else result)
          [pending && !decide (query=edge.1.bits)] [] counter) := by
  let input := (Encoding.product Encoding.natural Encoding.natural).encode edge++suffix
  let start := file input query [] [] result [pending] [] counter
  obtain ⟨readTime,readBound,readRun⟩ := pair_executes 8 pairRoles pairRoles.injective start rfl
  rw [pair_result_spec 8 pairRoles pairRoles.injective] at readRun
  have parsed : parsePair input=⟨edge.1.bits,edge.2.bits,suffix,true⟩ := parsePair_frames _ _ _
  let next := file suffix query edge.1.bits edge.2.bits result [pending] [] counter
  have readStore : pairExpected 8 pairRoles start=Function.update next 6 [true] := by
    funext r;fin_cases r <;> simp [pairExpected,start,next,file,pairRoles,parsed]
  rw [readStore] at readRun
  have cleared := clear_executes (6:Fin 13) (Function.update next 6 [true])
  have restored : Function.update (Function.update next 6 [true]) 6 []=next := by
    funext r;fin_cases r <;> simp [next,file]
  rw [restored] at cleared
  obtain ⟨dispatchTime,dispatchBound,dispatched⟩ := dispatch_executes suffix query edge.1.bits edge.2.bits result counter pending
  have cleaned := cleanup_executes suffix query edge.1.bits
    (if pending && decide (query=edge.1.bits) then [] else edge.2.bits)
    (if pending && decide (query=edge.1.bits) then edge.2.bits else result)
    [pending && !decide (query=edge.1.bits)] counter
  have composed := readRun.sequence (cleared.sequence (dispatched.sequence cleaned))
  refine ⟨_,?_,composed⟩
  change readTime≤ 6*input.length+13 at readBound
  have inputLength : input.length=2*edge.1.bits.length+1+(2*edge.2.bits.length+1)+suffix.length := by
    simp [input,Encoding.product,Encoding.natural,Encoding.frame_length,Nat.add_assoc]
  have valueLength : (if pending && decide (query=edge.1.bits) then [] else edge.2.bits).length≤edge.2.bits.length := by
    split <;> simp
  change readTime+1+(2+1+(dispatchTime+1+
    (edge.1.bits.length+(if pending && decide (query=edge.1.bits) then [] else edge.2.bits).length+3)))≤ _
  have wholeLength : ((Encoding.product Encoding.natural Encoding.natural).encode edge).length+suffix.length=input.length := List.length_append.symm
  rw [wholeLength]
  omega

end Counting.StackMachine.AnchorFind
