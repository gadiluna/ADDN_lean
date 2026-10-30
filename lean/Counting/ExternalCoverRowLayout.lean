import Counting.ExternalCoverShifted
import Counting.StackEmitTripleSelected
import Counting.StackRoutineClearSelected

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false

abbrev RowWorkspace (extra : Nat) := Fin 48 ↪ Fin (extra+48)
def coordinatePositions (which : Fin 3) : Fin 32 ↪ Fin 48 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      ![32,33,34] which,22,23,24,25,26,27,28,29,30,31],by fin_cases which <;> decide⟩
def RowWorkspace.coordinate (w : RowWorkspace extra) (which : Fin 3) : SATWorkspace (extra+16) :=
  (coordinatePositions which).trans w
def rowReaderPositions : Fin 32 ↪ Fin 48 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro i j same;exact Fin.ext (congrArg (fun k : Fin 48=>k.val) same)⟩
def RowWorkspace.reader (w : RowWorkspace extra) : SATWorkspace (extra+16) := rowReaderPositions.trans w
def rowTriplePositions : Fin 6 ↪ Fin 48 := ⟨![32,33,34,36,40,41],by decide⟩
def RowWorkspace.triple (w : RowWorkspace extra) : TripleWorkspace (extra+42) := rowTriplePositions.trans w
def codePosition (which : Fin 3) : Fin 48 := ![32,33,34] which

def rowScratch : List (Fin 48) := [2,3,4,5,6,9,10,11,12,18,19,20,26,28,29,30,32,33,34,40,41]

def generateRow (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (readNatural (extra+16) w.reader)
    (sequence (clear (w 18))
      (sequence (readShifted (extra+16) (w.coordinate 0) 0)
        (sequence (readShifted (extra+16) (w.coordinate 1) 1)
          (sequence (readShifted (extra+16) (w.coordinate 2) 2)
            (sequence (emitTripleSelected (extra+42) w.triple id) (clearRegisters [w 32,w 33,w 34]))))))

theorem readCoordinate_executes (extra : Nat) (w : RowWorkspace extra) (which : Fin 3)
    (store : Fin (extra+48) → List Bool) (index : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode index++suffix)
    (status : store (w 1)=accepted::tail) (fits : index≤(store (w 17)).length)
    (empty : ∀ i∈([2,3,4,5,6,9,10,11,12,18,19,20,26,28,29,30] : List (Fin 48)),store (w i)=[]) :
    ∃ time ≤ 1000*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (readShifted (extra+16) (w.coordinate which) which.val) store time
        (Function.update (Function.update store (w 0) suffix) (w (codePosition which))
          (Encoding.natural.encode (which.val*(store (w 17)).length+index)++store (w (codePosition which)))) := by
  have workEmpty (i : Fin 32) (mem : i∈shiftedScratch) : store (w.coordinate which i)=[] := by
    simp only [shiftedScratch,coverIndexScratch,List.mem_append,List.mem_cons,List.not_mem_nil] at mem
    rcases mem with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h)|(rfl|rfl|rfl|h)
    all_goals first | contradiction | simpa [RowWorkspace.coordinate,coordinatePositions] using empty _ (by decide)
  obtain ⟨time,bounded,ran⟩ := readShifted_executes (extra+16) (w.coordinate which) which.val (by omega) store index accepted suffix tail
    (by simpa [RowWorkspace.coordinate,coordinatePositions] using source)
    (by simpa [RowWorkspace.coordinate,coordinatePositions] using status)
    (by simpa [RowWorkspace.coordinate,coordinatePositions] using fits) workEmpty
  exact ⟨time,by simpa [RowWorkspace.coordinate,coordinatePositions] using bounded,
    by simpa [RowWorkspace.coordinate,coordinatePositions,codePosition] using ran⟩

end Counting.External.CoverMachine
