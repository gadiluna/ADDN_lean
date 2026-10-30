import Counting.StackDagImportNodes
import Counting.StackUnframeCanonical
import Counting.StackRoutineClean

namespace Counting.StackMachine.DagUpdate.Import
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def importInput (pool : Array Executable.Node) (nodes : List Executable.Node) : List Bool :=
  Encoding.frame ((Encoding.array Encoding.node).encode pool)++(Encoding.list Encoding.node).encode nodes

def importOutput (pool : Array Executable.Node) (nodes : List Executable.Node) : List Bool :=
  let result := nodes.foldl advance (pool,#[])
  (Encoding.product (Encoding.array Encoding.node) (Encoding.array Encoding.natural)).encode result

def prepareImport : Routine 94 := sequence (ofProgram (unframeProgram 93 0 64 69))
  (sequence (move 93 0 70 69) (pushBit 71 true))

def preparedImport (pool : Array Executable.Node) (nodes : List Executable.Node) : Store 94 :=
  Function.update (Function.update (Function.update (fun _=>[]) 64
    ((Encoding.array Encoding.node).encode pool)) 70 ((Encoding.list Encoding.node).encode nodes)) 71 [true]

theorem prepareImport_executes (pool : Array Executable.Node) (nodes : List Executable.Node) :
    Executes prepareImport (inputStore 94 (importInput pool nodes))
      (5*((Encoding.array Encoding.node).encode pool).length+
        6*((Encoding.list Encoding.node).encode nodes).length+9) (preparedImport pool nodes) := by
  let store := inputStore 94 (importInput pool nodes)
  let poolCode := (Encoding.array Encoding.node).encode pool
  let sourceCode := (Encoding.list Encoding.node).encode nodes
  have parse := unframe_canonical_executes 93 (0:Fin 96) 64 69 (by decide) (by decide) (by decide)
    store poolCode sourceCode rfl rfl
  have poolEmpty : store 64=[] := rfl
  rw [poolEmpty,List.append_nil] at parse
  let parsed := Function.update (Function.update store 0 sourceCode) 64 poolCode
  have moving := move_executes 93 (0:Fin 96) 70 69 (by decide) (by decide) (by decide)
    parsed (by simp [parsed,store,inputStore])
  have sourceAt : parsed 0=sourceCode := by simp [parsed]
  have targetEmpty : parsed 70=[] := by simp [parsed,store,inputStore]
  rw [sourceAt,targetEmpty,List.append_nil] at moving
  let moved := Function.update (Function.update parsed 70 sourceCode) 0 []
  have flag := pushBit_executes (71:Fin 96) true moved
  have flagEmpty : moved 71=[] := by simp [moved,parsed,store,inputStore]
  rw [flagEmpty] at flag
  have final : Function.update moved 71 [true]=preparedImport pool nodes := by
    funext r
    by_cases r0 : r=0 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;> by_cases r71 : r=71 <;>
      simp [preparedImport,moved,parsed,store,inputStore,poolCode,sourceCode,r0,r64,r70,r71]
  rw [final] at flag
  convert parse.sequence (moving.sequence flag) using 1 <;>
    first | rfl | (dsimp only [poolCode,sourceCode];omega)

def finishImport : Routine 94 := sequence (move 93 64 1 69) (clear 71)

theorem finishImport_executes (pool : Array Executable.Node) (nodes : List Executable.Node) :
    let result := nodes.foldl advance (pool,#[])
    Executes finishImport (importResult (preparedImport pool nodes) pool nodes [])
      (6*((Encoding.array Encoding.node).encode result.1).length+7)
      (outputStore 94 (importOutput pool nodes)) := by
  let result := nodes.foldl advance (pool,#[])
  let store := importResult (preparedImport pool nodes) pool nodes []
  let poolCode := (Encoding.array Encoding.node).encode result.1
  let mapCode := (Encoding.array Encoding.natural).encode result.2
  have moving := move_executes 93 (64:Fin 96) 1 69 (by decide) (by decide) (by decide)
    store (by simp [store,importResult,preparedImport])
  have poolAt : store 64=poolCode := by simp [store,importResult,poolCode,result]
  have mapAt : store 1=mapCode := by simp [store,importResult,mapCode,result]
  rw [poolAt,mapAt] at moving
  let moved := Function.update (Function.update store 1 (poolCode++mapCode)) 64 []
  have cleanup := clear_executes (71:Fin 96) moved
  have flagAt : moved 71=[true] := by simp [moved,store,importResult,preparedImport]
  rw [flagAt,List.length_singleton] at cleanup
  have final : Function.update moved 71 []=outputStore 94 (importOutput pool nodes) := by
    funext r
    by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;> by_cases r71 : r=71 <;>
      simp [outputStore,importOutput,Encoding.product,moved,store,importResult,preparedImport,
        poolCode,mapCode,result,r1,r64,r70,r71]
  rw [final] at cleanup
  exact moving.sequence cleanup

def completeImport : Routine 94 := sequence prepareImport (sequence importNodes finishImport)

def completeImportBudget (pool : Array Executable.Node) (nodes : List Executable.Node) : Nat :=
  let result := nodes.foldl advance (pool,#[])
  5*((Encoding.array Encoding.node).encode pool).length+
    6*((Encoding.list Encoding.node).encode nodes).length+
    importNodesBudget pool nodes ((Encoding.list Encoding.node).encode nodes).length+
    6*((Encoding.array Encoding.node).encode result.1).length+18

/-- A closed stack program with one encoded input and one encoded output.
Both original source words and every scratch register are consumed. -/
theorem completeImport_executes (pool : Array Executable.Node) (nodes : List Executable.Node) :
    ∃ time ≤ completeImportBudget pool nodes,
      Executes completeImport (inputStore 94 (importInput pool nodes)) time
        (outputStore 94 (importOutput pool nodes)) := by
  have preparation := prepareImport_executes pool nodes
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := importNodes_executes (preparedImport pool nodes) pool nodes []
    (by simp [preparedImport]) (by simp [preparedImport]) (by simp [preparedImport]) (by
      intro r member
      have n64 : r≠64 := by
        rcases member with first|last|last
        · exact first.2
        · subst r
          decide
        · subst r
          decide
      have n70 : r≠70 := by intro equal;subst r;norm_num [Fin.ext_iff] at member
      have n71 : r≠71 := by intro equal;subst r;norm_num [Fin.ext_iff] at member
      simp [preparedImport,n64,n70,n71])
  have finish := finishImport_executes pool nodes
  refine ⟨_,?_,preparation.sequence (bodyRun.sequence finish)⟩
  change bodyTime ≤ importNodesBudget pool nodes ((Encoding.list Encoding.node).encode nodes).length at bodyBound
  dsimp only [completeImportBudget]
  omega

end Counting.StackMachine.DagUpdate.Import
