import Counting.NetworkVistaArcRead
import Counting.NetworkVistaBundleSelect

namespace Counting.StackMachine.NetworkVista
open Routine
set_option backward.isDefEq.respectTransparency false

def appendReceivedBundle : Routine 14 := sequence readArc selectBundle

def receivedBundleStore (store:Store 14) (vista:Executable.Vista) (count:Nat) : Store 14 :=
  if count=0 then store else
    Function.update (Function.update store
      3 (((Encoding.product Encoding.vista Encoding.natural).encode (vista,count)).reverse++store 3))
      4 (true::store 4)

/-- A single sender contributes exactly one compact pair when its edge
multiplicity is positive. No copies proportional to that multiplicity are
created; all physical instructions are bounded by serialized bit lengths. -/
theorem appendReceivedBundle_executes (store:Store 14) (vista:Executable.Vista)
    (row:Array Nat) (index:Fin row.size)
    (view:store 0=Encoding.vista.encode vista)
    (source:store 1=(Encoding.array Encoding.natural).encode row)
    (position:(store 2).length=index.val)
    (empty:∀r:Fin 16,r∈({5,6,7,8,9,10,11,12}:Finset (Fin 16)) → store r=[]) :
    ∃time ≤ 80*((store 0).length+(store 1).length+(store 2).length+1),
      Executes appendReceivedBundle store time (receivedBundleStore store vista row[index.val]) := by
  obtain ⟨readTime,readBound,reading⟩:=readArc_executes store row index source position empty
  let parsed:=Function.update store 5 row[index.val].bits
  obtain ⟨selectTime,selectBound,selecting⟩:=selectBundle_executes parsed
    (by simp [parsed,empty 8 (by decide)]) (by simp [parsed,empty 9 (by decide)])
  have selected:=selectedBundleStore_typed parsed vista row[index.val]
    (by simp [parsed,view]) (by simp [parsed])
  have final:selectedBundleStore parsed=receivedBundleStore store vista row[index.val]:=by
    rw [selected]
    by_cases zero:row[index.val]=0
    · simp [receivedBundleStore,zero,parsed,←empty 5 (by decide)]
    · funext r
      by_cases n3:r=3 <;> by_cases n4:r=4 <;> by_cases n5:r=5 <;>
        simp [receivedBundleStore,zero,parsed,n3,n4,n5,empty 5 (by decide)]
  rw [final] at selecting
  have amountLength:row[index.val].size≤(store 1).length:=by
    have bound:=Encoding.array_member_length_le Encoding.natural row row[index.val] (by simp)
    rw [Encoding.natural_length] at bound
    rw [source]
    omega
  have sameView:parsed 0=store 0:=by simp [parsed]
  have amount:parsed 5=row[index.val].bits:=by simp [parsed]
  rw [sameView,amount,Encoding.bits_length] at selectBound
  refine ⟨readTime+1+selectTime,?_,reading.sequence selecting⟩
  omega

end Counting.StackMachine.NetworkVista
