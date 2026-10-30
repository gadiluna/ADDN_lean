import Counting.StackAnchorFindStep
import Counting.StackLoop
import Counting.EncodingBinary

namespace Counting.StackMachine.AnchorFind
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev edgeCodec := Encoding.product Encoding.natural Encoding.natural

def search (query : List Bool) : List (Nat×Nat) → Bool → List Bool → Bool×List Bool
  | [],pending,result => (pending,result)
  | edge::edges,pending,result => search query edges
      (pending && !decide (query=edge.1.bits))
      (if pending && decide (query=edge.1.bits) then edge.2.bits else result)

theorem search_false (query : List Bool) (edges : List (Nat×Nat)) (result : List Bool) :
    search query edges false result=(false,result) := by
  induction edges with
  | nil => rfl
  | cons edge edges ih => simpa [search] using ih

theorem search_find (query : Nat) (edges : List (Nat×Nat)) (result : List Bool) :
    (search query.bits edges true result).2=
      ((edges.find? (fun edge=>edge.1==query)).map (fun edge=>edge.2.bits)).getD result := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
    by_cases equal : query=edge.1
    · simp [search,equal,search_false]
    · have ne : edge.1≠query := Ne.symm equal
      simpa [search,Encoding.bits_injective.eq_iff,equal,ne] using ih

abbrev loop : Routine 11 := forEach 12 item

theorem loop_executes (query : List Bool) (edges : List (Nat×Nat)) (suffix : List Bool)
    (pending : Bool) (result counter : List Bool) (length : counter.length=edges.length)
    (limit : Nat) (inputBound : (Encoding.sequence edgeCodec edges++suffix).length ≤  limit)
    (resultBound : result.length ≤  limit) :
    ∃ time  ≤  edges.length*(100*(2*limit+query.length+1)+2)+1,
      Executes loop (file (Encoding.sequence edgeCodec edges++suffix) query [] [] result [pending] [] counter)
        time (file suffix query [] [] (search query edges pending result).2
          [(search query edges pending result).1] [] []) := by
  induction edges generalizing pending result counter with
  | nil =>
    have nil : counter=[] := List.length_eq_zero_iff.mp length
    subst counter
    obtain ⟨ran,halted⟩ := repeat_empty (12:Fin 13) item
      (file suffix query [] [] result [pending] [] []) rfl
    exact ⟨1,by simp,⟨1,file suffix query [] [] result [pending] [] []⟩,ran,halted,rfl⟩
  | cons edge edges ih =>
    cases counter with
    | nil => simp at length
    | cons bit counter =>
      let source := Encoding.sequence edgeCodec edges++suffix
      let start := file (edgeCodec.encode edge++source) query [] [] result [pending] [] (bit::counter)
      let selected := pending && decide (query=edge.1.bits)
      let nextPending := pending && !decide (query=edge.1.bits)
      let nextResult := if selected then edge.2.bits else result
      have popped : Function.update start 12 counter=
          file (edgeCodec.encode edge++source) query [] [] result [pending] [] counter := by
        funext r;fin_cases r <;> simp [start,file]
      obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalted,bodyStore⟩ :=
        item_executes query result counter pending edge source
      have nextLength : counter.length=edges.length := by simpa using length
      have nextInput : (Encoding.sequence edgeCodec edges++suffix).length ≤  limit := by
        simp only [Encoding.sequence,List.length_append] at inputBound ⊢
        omega
      have countLength : edge.2.bits.length ≤  limit := by
        have encoded : (edgeCodec.encode edge).length=2*edge.1.bits.length+1+(2*edge.2.bits.length+1) := by
          simp [edgeCodec,Encoding.product,Encoding.natural,Encoding.frame_length]
        simp only [Encoding.sequence,List.length_append] at inputBound
        omega
      have nextBound : nextResult.length ≤  limit := by dsimp only [nextResult];split <;> assumption
      obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalted,tailStore⟩ :=
        ih nextPending nextResult counter nextLength nextInput nextBound
      have firstRun := repeat_iteration (12:Fin 13) item start bit counter rfl bodyTime bodyFinish
        (popped.symm ▸ bodyRun) bodyHalted
      refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalted,?_⟩
      · have bodyLimit : bodyTime ≤ 100*(2*limit+query.length+1) := by
          change bodyTime ≤ 100*((edgeCodec.encode edge).length+source.length+query.length+result.length+1) at bodyBound
          have allInput : (edgeCodec.encode edge).length+source.length ≤ limit := by
            simpa only [Encoding.sequence,List.length_append,List.append_assoc,source] using inputBound
          omega
        simp only [List.length_cons]
        nlinarith
      · simp only [Encoding.sequence,List.append_assoc]
        change Machine.run (step (forEach 12 item).program) (bodyTime+2+tailTime) ⟨0,start⟩=some tailFinish
        rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun
      · simpa only [search,nextPending,nextResult,selected] using tailStore

end Counting.StackMachine.AnchorFind
