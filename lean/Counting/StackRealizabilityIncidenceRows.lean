import Counting.StackRealizabilityIncidenceRow
import Counting.StackRealizabilityIncidenceValues

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem incidenceRows_executes (source index incoming parent statusTail width bits : List Bool)
    (accepted : Bool) (prior nodes : List Executable.Node) (suffix : List Bool)
    (input : source=Encoding.sequence Encoding.node (prior++nodes)++suffix)
    (indexAt : index.length=prior.length) (counted : bits.length=nodes.length) :
    ∃ time ≤ nodes.length*(30000*(source.length+width.length+1)^6+2)+1,
      Executes (forEach 44 incidenceRow)
        (incidenceTableFile source index [] incoming parent (accepted::statusTail) width [] bits) time
        (incidenceTableFile source (List.replicate nodes.length true++index) []
          ((incomingRows nodes width.length).reverse++incoming)
          ((parentRows nodes width.length).reverse++parent)
          (accepted::statusTail) width [] []) := by
  induction nodes generalizing prior index incoming parent bits with
  | nil =>
    have empty : bits=[] := List.length_eq_zero_iff.mp (by simpa using counted)
    subst bits
    obtain ⟨ran,halted⟩ := repeat_empty (44:Fin 46) incidenceRow
      (incidenceTableFile source index [] incoming parent (accepted::statusTail) width [] [])
      (by simp [incidenceTableFile])
    exact ⟨1,by simp,⟨1,_⟩,ran,halted,by simp [incomingRows,parentRows]⟩
  | cons node nodes ih =>
    cases bits with
    | nil => simp at counted
    | cons bit bits =>
      let all := prior++node::nodes
      let position : Fin all.length := ⟨prior.length,by simp [all]⟩
      have selected : all[position]=node := by simp [all,position]
      let original := incidenceTableFile source index [] incoming parent (accepted::statusTail) width [] (bit::bits)
      let consumed := incidenceTableFile source index [] incoming parent (accepted::statusTail) width [] bits
      let nextIncoming := (incomingRowValues node 0 width.length).reverse++incoming
      let nextParent := (parentRowValues node 0 width.length).reverse++parent
      obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalted,bodyStore⟩ := incidenceRow_executes
        source index incoming parent statusTail width bits accepted all position suffix input indexAt
      rw [selected] at bodyStore
      obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalted,tailStore⟩ := ih (true::index)
        nextIncoming nextParent bits (prior++[node])
        (by simpa only [List.append_assoc,List.singleton_append] using input)
        (by simp [indexAt]) (by simpa using counted)
      have consumedEq : Function.update original 44 bits=consumed := by
        funext r
        fin_cases r <;> simp [original,consumed,incidenceTableFile]
      have iteration := repeat_iteration (44:Fin 46) incidenceRow original bit bits
        (by simp [original,incidenceTableFile]) bodyTime bodyFinish
        (by simpa only [consumedEq] using bodyRun) bodyHalted
      refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalted,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
        exact tailRun
      · apply tailStore.trans
        congr 1
        · simp [List.replicate_succ',List.append_assoc]
        · simp [incomingRows,nextIncoming,List.append_assoc]
        · simp [parentRows,nextParent,List.append_assoc]

end Counting.StackMachine.RealizabilityCheck
