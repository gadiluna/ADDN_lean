import Counting.StackRealizabilityExternalFields

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def secondFields : Routine 128 := sequence (clearExternal 1)
  (sequence (clearExternal 3) (sequence (copyExternal 7 1) (copyExternal 6 3)))

def secondFieldsData (data : Fin 30→List Bool) : Fin 30→List Bool :=
  Function.update (Function.update data 1 (data 7)) 3 (data 6)

theorem secondFields_executes (data : Fin 30→List Bool) :
    Executes secondFields (file data)
      ((data 1).length+(data 3).length+5*(data 7).length+5*(data 6).length+9)
      (file (secondFieldsData data)) := by
  have a := clearExternal_executes data 1
  have b := clearExternal_executes (Function.update data 1 []) 3
  have c := copyExternal_executes (Function.update (Function.update data 1 []) 3 []) 7 1 (by decide)
  have d := copyExternal_executes
    (Function.update (Function.update (Function.update data 1 []) 3 []) 1 (data 7)) 6 3 (by decide)
  simp only [Function.update_of_ne (show (7:Fin 30)≠3 by decide),
    Function.update_of_ne (show (7:Fin 30)≠1 by decide),Function.update_self,
    Function.update_of_ne (show (1:Fin 30)≠3 by decide),List.append_nil] at c
  simp only [Function.update_of_ne (show (6:Fin 30)≠1 by decide),
    Function.update_of_ne (show (6:Fin 30)≠3 by decide),
    Function.update_of_ne (show (3:Fin 30)≠1 by decide),Function.update_self,List.append_nil] at d
  have run := a.sequence (b.sequence (c.sequence d))
  have timeEq : (data 1).length+1+1+
      ((Function.update data 1 [] 3).length+1+1+(5*(data 7).length+2+1+(5*(data 6).length+2)))=
      (data 1).length+(data 3).length+5*(data 7).length+5*(data 6).length+9 := by
    simp only [Function.update_of_ne (show (3:Fin 30)≠1 by decide)]
    omega
  rw [timeEq] at run
  have final : Function.update (Function.update (Function.update (Function.update data 1 []) 3 [])
      1 (data 7)) 3 (data 6)=secondFieldsData data := by
    funext i
    by_cases i=1 <;> by_cases i=3 <;> simp_all [secondFieldsData]
  rw [final] at run
  exact run

end Counting.StackMachine.VistaComplement
