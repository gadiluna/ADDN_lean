import Counting.NetworkVistaParse
import Counting.NetworkVistaBundle
import Counting.NetworkRecognitionParser

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def senderViewRoles : Fin 20 ↪ Fin 40 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,21,18,27],by decide⟩

def senderRowRoles : Fin 20 ↪ Fin 40 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,22,18,28],by decide⟩

def senderBundleRoles : Fin 16 ↪ Fin 40 :=
  ⟨![27,28,23,24,25,29,30,31,32,33,34,35,36,37,38,39],by decide⟩

/-- The offline simulator advances the two explicit sender streams in
lockstep, and emits a binary bundle only for a positive selected arc. -/
def senderItem : Routine 38 := sequence (relocate (Forward.parseForward DagParser.vista) senderViewRoles)
  (sequence (relocate (Forward.parseForward NetworkRecognition.row) senderRowRoles)
    (sequence (relocate appendReceivedBundle senderBundleRoles)
      (sequence (clear 27) (clear 28))))

def senderItemStore (store:Store 38) (vista:Executable.Vista) (amount:Nat)
    (viewSuffix rowSuffix:List Bool) : Store 38 :=
  let consumed:=Function.update (Function.update store 21 viewSuffix) 22 rowSuffix
  if amount=0 then consumed else
    Function.update (Function.update consumed
      24 (((Encoding.product Encoding.vista Encoding.natural).encode (vista,amount)).reverse++store 24))
      25 (true::store 25)

def SenderEmpty (store:Store 38) : Prop :=
  (∀r:Fin 40,r.val<17 → r≠1 → store r=[]) ∧
  (∀r:Fin 40,27≤r.val → r.val≤36 → store r=[])

theorem Forward.work_small {α:Type} {codec:Encoding.Codec α}
    (parser:VerifiedParser 15 0 1 2 α codec) (r:Fin 20)
    (member:r∈(Forward.wideParser parser).work) : r.val<17 ∧ r≠1 := by
  change r∈parser.work.map Forward.parserRoles at member
  obtain ⟨i,inside,rfl⟩:=Finset.mem_map.mp member
  obtain ⟨i0,i1,_⟩:=parser.separate i inside
  constructor
  · simp [Forward.parserRoles,i0]
  · intro same
    apply i1
    apply Forward.parserRoles.injective
    exact same

theorem senderView_work (store:Store 38) (empty:SenderEmpty store) (r:Fin 20)
    (member:r∈(Forward.wideParser DagParser.vista).work) : store (senderViewRoles r)=[] := by
  obtain ⟨small,n1⟩:=Forward.work_small DagParser.vista r member
  apply empty.1
  · fin_cases r <;> simp_all [senderViewRoles]
  · intro same
    apply n1
    exact senderViewRoles.injective same

theorem senderRow_work (store:Store 38) (empty:SenderEmpty store) (r:Fin 20)
    (member:r∈(Forward.wideParser NetworkRecognition.row).work) : store (senderRowRoles r)=[] := by
  obtain ⟨small,n1⟩:=Forward.work_small NetworkRecognition.row r member
  apply empty.1
  · fin_cases r <;> simp_all [senderRowRoles]
  · intro same
    apply n1
    exact senderRowRoles.injective same

end Counting.StackMachine.NetworkVista
