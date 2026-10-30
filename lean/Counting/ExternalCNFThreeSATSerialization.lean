import Counting.ExternalEncoding
import Mathlib.Data.List.OfFn

namespace Counting.External.CNF

@[simp] theorem liftLiteral_index {n : Nat} (formula : CNF n) (literal : Literal n) :
    (formula.liftLiteral literal).var.val=literal.var.val := rfl

@[simp] theorem freshLiteral_index {n : Nat} (formula : CNF n) (c : Fin formula.length)
    (j : Fin (formula.width+1)) :
    (formula.freshLiteral c j).var.val=n+c.val*(formula.width+1)+j.val := by
  change n+(j.val+(formula.width+1)*c.val)=_
  ac_rfl

@[simp] theorem liftLiteral_sign {n : Nat} (formula : CNF n) (literal : Literal n) :
    (formula.liftLiteral literal).positive=literal.positive := rfl
@[simp] theorem freshLiteral_sign {n : Nat} (formula : CNF n) (c : Fin formula.length)
    (j : Fin (formula.width+1)) : (formula.freshLiteral c j).positive=true := rfl

/-- Canonical order of the rows within one source clause: three gate rows
for every position, followed by the true initial and false terminal rows. -/
def serialRows {n : Nat} (formula : CNF n) : List (Row formula) :=
  (List.finRange formula.width).flatMap (fun j => [.inl (j,0),.inl (j,1),.inl (j,2)])++[.inr 0,.inr 1]

theorem rowEquiv_inl_val {n : Nat} (formula : CNF n) (j : Fin formula.width) (r : Fin 3) :
    (formula.rowEquiv (.inl (j,r))).val=3*j.val+r.val := by
  change r.val+3*j.val=_
  omega

theorem rowEquiv_inr_val {n : Nat} (formula : CNF n) (r : Fin 2) :
    (formula.rowEquiv (.inr r)).val=3*formula.width+r.val := rfl

theorem serialRows_eq_ofFn {n : Nat} (formula : CNF n) :
    List.ofFn formula.rowEquiv.symm=formula.serialRows := by
  rw [List.ofFn_add]
  have left : (List.ofFn fun i : Fin (3*formula.width) =>
      formula.rowEquiv.symm (i.castLE (Nat.le_add_right (3*formula.width) 2))) =
      (List.finRange formula.width).flatMap (fun j => [.inl (j,0),.inl (j,1),.inl (j,2)]) := by
    rw [List.ofFn_mul']
    have inverse (j : Fin formula.width) (r : Fin 3) :
        formula.rowEquiv.symm ⟨3*j.val+r.val,by have := j.isLt;have := r.isLt;omega⟩ = .inl (j,r) := by
      apply formula.rowEquiv.symm_apply_eq.mpr
      apply Fin.ext
      exact (rowEquiv_inl_val formula j r).symm
    simp only [Fin.castLE_mk,inverse]
    simp [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def,List.ofFn_succ]
  have right : (List.ofFn fun i : Fin 2 => formula.rowEquiv.symm (i.natAdd (3*formula.width)))=[.inr 0,.inr 1] := by
    have inverse (r : Fin 2) : formula.rowEquiv.symm (r.natAdd (3*formula.width))=.inr r := by
      apply formula.rowEquiv.symm_apply_eq.mpr
      apply Fin.ext
      exact (rowEquiv_inr_val formula r).symm
    simp only [inverse]
    simp [List.ofFn_succ]
  rw [left,right]
  rfl

private theorem ofFn_product {α : Type} {m k : Nat} (f : Fin (m*k)→α) :
    List.ofFn f=(List.finRange m).flatMap (fun i=>(List.finRange k).map (fun j=>f (finProdFinEquiv (i,j)))) := by
  rw [List.ofFn_mul]
  simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

def serialBlock {n : Nat} (formula : CNF n) (c : Fin formula.length) : CNF formula.targetVariables :=
  (List.finRange formula.width).flatMap (fun j =>
    [List.ofFn (orRows (formula.freshLiteral c j.castSucc) (formula.atomLiteral c j) (formula.freshLiteral c j.succ) 0),
     List.ofFn (orRows (formula.freshLiteral c j.castSucc) (formula.atomLiteral c j) (formula.freshLiteral c j.succ) 1),
     List.ofFn (orRows (formula.freshLiteral c j.castSucc) (formula.atomLiteral c j) (formula.freshLiteral c j.succ) 2)])++
  [List.replicate 3 (formula.freshLiteral c 0),
   List.replicate 3 ((formula.freshLiteral c (Fin.last formula.width)).negate)]

theorem serialBlock_eq {n : Nat} (formula : CNF n) (c : Fin formula.length) :
    (List.ofFn formula.rowEquiv.symm).map (fun row=>List.ofFn (formula.rowLiteral c row))=formula.serialBlock c := by
  rw [serialRows_eq_ofFn]
  simp [serialRows,serialBlock,List.map_flatMap,rowLiteral]

theorem toThreeSAT_toCNF_serial {n : Nat} (formula : CNF n) :
    formula.toThreeSAT.toCNF=(List.finRange formula.length).flatMap formula.serialBlock := by
  simp only [ThreeSAT.toCNF,List.finRange,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun index : Fin (formula.length*(3*formula.width+2)) =>
    List.ofFn (formula.toThreeSAT.literal index))=_
  rw [ofFn_product]
  apply congrArg (fun block => (List.finRange formula.length).flatMap block)
  funext c
  have index (r : Fin (3*formula.width+2)) :
      finProdFinEquiv (c,r)=formula.clauseEquiv (c,formula.rowEquiv.symm r) := by
    simp [clauseEquiv]
    rfl
  have literal (r : Fin (3*formula.width+2)) :
      formula.toThreeSAT.literal (formula.clauseEquiv (c,formula.rowEquiv.symm r)) =
        formula.rowLiteral c (formula.rowEquiv.symm r) := by
    funext p
    exact toThreeSAT_literal formula c (formula.rowEquiv.symm r) p
  simp only [index,literal]
  simpa only [List.finRange,List.map_ofFn,Function.comp_def] using serialBlock_eq formula c

/-- Raw indices used by the concrete serializer. The position may be the
terminal `width`, so this definition does not discard the final variable. -/
def freshRaw {n : Nat} (formula : CNF n) (c j : Nat) : Nat × Bool :=
  (n+c*(formula.width+1)+j,true)

def negateRaw (literal : Nat × Bool) : Nat × Bool :=
  (literal.1,!literal.2)

def atomRaw {n : Nat} (formula : CNF n) (c : Fin formula.length) (j : Nat) : Nat × Bool :=
  match (formula.clause c)[j]? with
  | some literal => CNFEncoding.literalRaw literal
  | none => formula.freshRaw c.val formula.width

@[simp] theorem literalRaw_lift {n : Nat} (formula : CNF n) (literal : Literal n) :
    CNFEncoding.literalRaw (formula.liftLiteral literal)=CNFEncoding.literalRaw literal := rfl

@[simp] theorem literalRaw_fresh {n : Nat} (formula : CNF n) (c : Fin formula.length)
    (j : Fin (formula.width+1)) :
    CNFEncoding.literalRaw (formula.freshLiteral c j)=formula.freshRaw c.val j.val := by
  simp [CNFEncoding.literalRaw,freshRaw]

@[simp] theorem literalRaw_negate {n : Nat} (literal : Literal n) :
    CNFEncoding.literalRaw literal.negate=negateRaw (CNFEncoding.literalRaw literal) := rfl

@[simp] theorem literalRaw_atom {n : Nat} (formula : CNF n) (c : Fin formula.length)
    (j : Fin formula.width) :
    CNFEncoding.literalRaw (formula.atomLiteral c j)=formula.atomRaw c j.val := by
  simp only [atomLiteral,atomRaw]
  split <;> simp_all

private theorem ofFn_triple {n : Nat} (a b c : Literal n) :
    List.ofFn (tripleLiterals a b c)=[a,b,c] := by
  simp [List.ofFn_succ,tripleLiterals]

/-- Exact serialized block, including repeated literals and the two terminal
clauses. No sorting or permutation is hidden in this representation. -/
def serialRawBlock {n : Nat} (formula : CNF n) (c : Fin formula.length) : List (List (Nat × Bool)) :=
  (List.finRange formula.width).flatMap (fun j =>
    let current := formula.freshRaw c.val j.val
    let atom := formula.atomRaw c j.val
    let next := formula.freshRaw c.val (j.val+1)
    [[negateRaw current,atom,next],
     [current,negateRaw atom,negateRaw atom],
     [current,negateRaw next,negateRaw next]])++
  [List.replicate 3 (formula.freshRaw c.val 0),
   List.replicate 3 (negateRaw (formula.freshRaw c.val formula.width))]

theorem serialBlock_raw {n : Nat} (formula : CNF n) (c : Fin formula.length) :
    (formula.serialBlock c).map (List.map CNFEncoding.literalRaw)=formula.serialRawBlock c := by
  simp [serialBlock,serialRawBlock,List.map_flatMap,orRows,tripleLiterals]

theorem toThreeSAT_toRaw_serial {n : Nat} (formula : CNF n) :
    CNFEncoding.toRaw ⟨formula.targetVariables,formula.toThreeSAT.toCNF⟩ =
      (List.replicate formula.targetVariables true,
       (List.finRange formula.length).flatMap formula.serialRawBlock) := by
  simp only [CNFEncoding.toRaw,toThreeSAT_toCNF_serial,List.map_flatMap]
  congr 1
  congr 1
  funext c
  exact serialBlock_raw formula c

end Counting.External.CNF
