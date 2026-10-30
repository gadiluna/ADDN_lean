import Counting.StoredGaussian

/-!
# Executable local counting algorithm
The local interface contains no population size, identities or physical graph.
Vistas are immutable DAGs with an implicit root; multiplicities are binary Nat
counts. Exact signatures, not hashes, control merging. The refinement modules prove DAG semantics and complete audit correctness.
MachineCountingRuntimeTheorems proves the total polynomial local runtime.
-/
namespace Counting.Executable
open DirectedCounting.VerifiedGaussianAnchorSolver
open scoped Matrix BigOperators

/-- Rectangular normal equations have exactly the same homogeneous kernel.
The array representation is connected by the executable refinement modules. -/
theorem gram_kernel {m n : Nat} (A : Matrix (Fin m) (Fin n) ℚ)
    (x : Fin n → ℚ) :
    (Aᵀ * A) *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · intro h
    have hz : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = 0 := by
      rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, h]
      simp
    exact dotProduct_self_eq_zero.mp hz
  · intro h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- Thus a unique solution to all original equations is not lost by using
normal equations before Gaussian elimination. -/
theorem gram_injective_iff {m n : Nat} (A : Matrix (Fin m) (Fin n) ℚ) :
    Function.Injective (Aᵀ * A).mulVec ↔ Function.Injective A.mulVec := by
  constructor
  · intro h x y hxy
    apply h
    simpa only [← Matrix.mulVec_mulVec] using congrArg Aᵀ.mulVec hxy
  · intro h x y hxy
    apply h
    have hsub : (Aᵀ * A) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have original := (gram_kernel A (x-y)).mp hsub
    simpa only [Matrix.mulVec_sub, sub_eq_zero] using original

structure Node where
  level : Nat
  parent : Option Nat
  leader : Bool
  degree : Nat
  incoming : List (Nat × Nat)
deriving DecidableEq, BEq, Repr, Inhabited

structure Vista where
  nodes : Array Node
  bottom : Nat
deriving DecidableEq, BEq, Repr, Inhabited

def Vista.node (v : Vista) (i : Nat) : Node := v.nodes[i]?.getD default

def initialVista (leader : Bool) : Vista := ⟨#[⟨0, none, leader, 0, []⟩], 0⟩

/-- Sparse sorted binary counts; repeated states are never expanded. -/
def addCount (index count : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => if count == 0 then [] else [(index, count)]
  | (i, c) :: rest =>
      if count == 0 then (i, c) :: rest
      else if index == i then (i, c + count) :: rest
      else if index < i then (index, count) :: (i, c) :: rest
      else (i, c) :: addCount index count rest

def countFrom (node : Node) (source : Nat) : Nat :=
  ((node.incoming.find? fun edge => edge.1 == source).map Prod.snd).getD 0

def referenceMap (mapping : Array Nat) (node : Node) : Node :=
  { node with
    parent := node.parent.map (fun i => mapping[i]?.getD 0)
    incoming := node.incoming.foldl
      (fun acc edge => addCount (mapping[edge.1]?.getD 0) edge.2 acc) [] }

def Node.key (node : Node) : List Nat :=
  [node.level, if node.leader then 1 else 0,
    node.parent.map (· + 1) |>.getD 0, node.degree] ++
      node.incoming.flatMap (fun edge => [edge.1, edge.2])

def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then lexLE xs ys else x < y

/-- Local node indices identify structural signatures, never network agents. -/
def intern (nodes : Array Node) (node : Node) : Array Node × Nat :=
  match (List.range nodes.size).find? (fun i => nodes[i]?.getD default == node) with
  | some index => (nodes, index)
  | none => (nodes.push node, nodes.size)

def importVista (pool : Array Node) (source : Vista) : Array Node × Array Nat :=
  source.nodes.foldl (fun state node =>
    let (nodes, mapping) := state
    let (next, index) := intern nodes (referenceMap mapping node)
    (next, mapping.push index)) (pool, #[])

/-- Level-by-level full-signature ordering removes import-order dependence.
Its semantic correspondence is proved in the DAG refinement modules. -/
def canonicalize (vista : Vista) : Vista := Id.run do
  let mut result : Array Node := #[]
  let mut mapping : Array Nat := Array.replicate vista.nodes.size 0
  let maxLevel := vista.nodes.foldl (fun n node => max n node.level) 0
  for level in List.range (maxLevel + 1) do
    let atLevel := (List.range vista.nodes.size).filter
      (fun i => (vista.node i).level == level)
    let ordered := atLevel.mergeSort (fun i j =>
      lexLE (referenceMap mapping (vista.node i)).key
        (referenceMap mapping (vista.node j)).key)
    for index in ordered do
      let node := referenceMap mapping (vista.node index)
      let (next, newIndex) := intern result node
      result := next
      mapping := mapping.set! index newIndex
  return ⟨result, mapping[vista.bottom]?.getD 0⟩

def levelNodes (vista : Vista) (level : Nat) : List Nat :=
  (List.range vista.nodes.size).filter (fun i => (vista.node i).level == level)

def children (vista : Vista) (parent level : Nat) : List Nat :=
  (levelNodes vista level).filter (fun i => (vista.node i).parent == some parent)

def countsSorted : List (Nat × Nat) → Bool
  | [] => true
  | (i, c) :: rest => c > 0 &&
      (rest.head?.map (fun edge => decide (i < edge.1)) |>.getD true) && countsSorted rest

def nodeValid (vista : Vista) (index : Nat) : Bool :=
  let node := vista.node index
  if node.level == 0 then
    node.parent.isNone && node.degree == 0 && node.incoming.isEmpty
  else match node.parent with
    | none => false
    | some parent =>
        parent < index && (vista.node parent).level + 1 == node.level &&
        (vista.node parent).leader == node.leader && countsSorted node.incoming &&
        node.incoming.all (fun edge => edge.1 < index &&
          (vista.node edge.1).level + 1 == node.level)

/-- Bounded reachability in the DAG; no recursive expansion of repeated trees. -/
def closure (vista : Vista) : Array Bool := Id.run do
  let mut seen := (Array.replicate vista.nodes.size false).set! vista.bottom true
  for _ in List.range vista.nodes.size do
    for i in List.range vista.nodes.size do
      if seen[i]?.getD false then
        let node := vista.node i
        if let some parent := node.parent then seen := seen.set! parent true
        for edge in node.incoming do seen := seen.set! edge.1 true
  return seen

def Vista.valid (vista : Vista) : Bool :=
  vista.bottom < vista.nodes.size &&
  (List.range vista.nodes.size).all (nodeValid vista) &&
  vista.nodes.toList.eraseDups.length == vista.nodes.size &&
  (closure vista).all id

/-- Receive whole previous vistas with binary counts, then learn the outdegree. -/
def updateVista? (old : Vista) (received : List (Vista × Nat))
    (outdegree : Nat) : Option Vista := do
  if !old.valid then none else do
    let previousRound := (old.node old.bottom).level
    if !received.all (fun message => message.2 > 0 && message.1.valid &&
        (message.1.node message.1.bottom).level == previousRound) then none else do
      let (start, oldMap) := importVista #[] old
      let ownBottom := oldMap[old.bottom]?.getD 0
      let (pool, incoming) := received.foldl (fun state message =>
        let (nodes, accumulated) := state
        let (next, mapping) := importVista nodes message.1
        (next, addCount (mapping[message.1.bottom]?.getD 0) message.2 accumulated))
        (start, [])
      let node : Node := ⟨previousRound + 1, some ownBottom,
        (old.node old.bottom).leader, outdegree, incoming⟩
      return canonicalize ⟨pool.push node, pool.size⟩

abbrev Equation := Array ℚ × ℚ

def normalSystem (width : Nat) (rows : List Equation) : RationalSystem width where
  coeff := fun i j => (rows.map (fun row =>
    (row.1[i.val]?.getD 0) * (row.1[j.val]?.getD 0))).sum
  rhs := fun i => (rows.map (fun row => (row.1[i.val]?.getD 0) * row.2)).sum

/-- Replay-verified Gaussian solution of the Gram system followed by checking
ALL original equations. Singular and inconsistent systems return none. -/
def solveLinear? (width : Nat) (rows : List Equation) : Option (Array ℚ) := do
  if !rows.all (fun row => row.1.size == width) then none else do
    let solution ← Counting.StoredGaussian.solve? (normalSystem width rows)
    if rows.all (fun row =>
        ((List.finRange width).map (fun i =>
          (row.1[i.val]?.getD 0) * solution i)).sum == row.2) then
      return ((List.finRange width).map solution).toArray
    else none

def positiveNaturals? (vector : Array ℚ) : Option (Array Nat) :=
  if vector.all (fun x => x.den == 1 && x.num > 0) then
    some (vector.map (fun x => x.num.toNat)) else none

def flat (vista : Vista) (level : Nat) : Bool :=
  level > 0 && !(levelNodes vista (level - 1)).isEmpty &&
  (levelNodes vista (level - 1)).all (fun parent =>
    (children vista parent level).length == 1)

def anchorRows (vista : Vista) (anchor leaders : Nat) : List Equation :=
  let current := levelNodes vista anchor
  let flow := (levelNodes vista (anchor - 1)).map (fun parent =>
    ((current.map (fun v =>
      (countFrom (vista.node v) parent : ℚ) -
        if (vista.node v).parent == some parent then (vista.node v).degree else 0)).toArray, 0))
  flow ++ [((current.map (fun v => if (vista.node v).leader then 1 else 0)).toArray,
    (leaders : ℚ))]

def ascend (vista : Vista) : Nat → Nat → Option Nat
  | 0, node => some node
  | steps + 1, node => (vista.node node).parent.bind (ascend vista steps)

structure AuditWitness where
  anchor : Nat
  weights : Array Nat
deriving Repr, BEq, DecidableEq

/-- Anchor assignment followed by the unchanged backward propagation loop. -/
def propagateWeights (vista : Vista) (anchor : Nat) (natural : Array Nat) : Array Nat := Id.run do
  let mut weights := Array.replicate vista.nodes.size 0
  for entry in (levelNodes vista anchor).zip natural.toList do
    weights := weights.set! entry.1 entry.2
  for r in (List.range anchor).reverse do
    for node in levelNodes vista r do
      let total := ((children vista node (r+1)).map
        (fun child => weights[child]?.getD 0)).sum
      weights := weights.set! node total
  return weights

/-- Explicit solver-call syntax used by the executable audit itself. The
continuation performs the remaining solver-free checks. -/
inductive SolverPlan (α : Type) where
  | done (result : α)
  | solve (width : Nat) (rows : List Equation) (next : Option (Array ℚ) → α)

def SolverPlan.eval {α : Type} : SolverPlan α → α
  | .done result => result
  | .solve width rows next => next (solveLinear? width rows)

def SolverPlan.widths {α : Type} : SolverPlan α → List Nat
  | .done _ => []
  | .solve width _ _ => [width]

def SolverPlan.map {α β : Type} (f : α → β) : SolverPlan α → SolverPlan β
  | .done result => .done (f result)
  | .solve width rows next => .solve width rows (fun result => f (next result))

@[simp] theorem SolverPlan.eval_map {α β : Type} (f : α → β) (plan : SolverPlan α) :
    (plan.map f).eval = f plan.eval := by cases plan <;> rfl

@[simp] theorem SolverPlan.widths_map {α β : Type} (f : α → β) (plan : SolverPlan α) :
    (plan.map f).widths = plan.widths := by cases plan <;> rfl

theorem SolverPlan.at_most_one {α : Type} (plan : SolverPlan α) :
    plan.widths.length ≤ 1 := by cases plan <;> simp [SolverPlan.widths]

/-- All checks preceding the unique possible solver invocation. -/
def auditPrefix? (vista : Vista) (leaders candidate last : Nat) : Option Nat := do
  if !vista.valid || leaders == 0 || candidate < leaders || last == 0 ||
      (vista.node vista.bottom).level < last then none else do
    if !(levelNodes vista 0).any (fun i => (vista.node i).leader) then none else do
      if !(List.range (last + 1)).all (fun r =>
          (levelNodes vista r).length ≤ candidate) then none else do
        if !(List.range last).all (fun r =>
            (levelNodes vista r).all (fun i => !(children vista i (r+1)).isEmpty)) then none else
          ((List.range (last + 1)).reverse).find? (flat vista)

/-- All checks after the solver returns; no system is solved here. -/
def auditSuffix? (vista : Vista) (candidate last anchor : Nat)
    (values : Option (Array ℚ)) : Option AuditWitness := do
  let values ← values
  let natural ← positiveNaturals? values
  if natural.toList.sum != candidate then none else do
    let weights := propagateWeights vista anchor natural
    if !(List.range anchor).all (fun r => r == 0 ||
        (levelNodes vista (r-1)).all (fun parent =>
          ((levelNodes vista r).map (fun v =>
            countFrom (vista.node v) parent * (weights[v]?.getD 0))).sum ==
          ((children vista parent r).map (fun v =>
            (vista.node v).degree * (weights[v]?.getD 0))).sum)) then none else do
      if !(levelNodes vista anchor).all (fun v =>
          ((levelNodes vista last).filter (fun descendant =>
            ascend vista (last-anchor) descendant == some v)).length ≤
            (weights[v]?.getD 0)) then none else
        return ⟨anchor, weights⟩

def auditPlan (vista : Vista) (leaders candidate last : Nat) : SolverPlan (Option AuditWitness) :=
  match auditPrefix? vista leaders candidate last with
  | none => .done none
  | some anchor => .solve (levelNodes vista anchor).length (anchorRows vista anchor leaders)
      (auditSuffix? vista candidate last anchor)

/-- Five-step audit: `last` is m for core counting and m-1 for the short test. -/
def audit? (vista : Vista) (leaders candidate last : Nat) : Option AuditWitness :=
  (auditPlan vista leaders candidate last).eval

/-- Preservation of the original five-step control flow. -/
theorem audit_unfold (vista : Vista) (leaders candidate last : Nat) :
    audit? vista leaders candidate last = do
  if !vista.valid || leaders == 0 || candidate < leaders || last == 0 ||
      (vista.node vista.bottom).level < last then none else do
    if !(levelNodes vista 0).any (fun i => (vista.node i).leader) then none else do
      if !(List.range (last + 1)).all (fun r =>
          (levelNodes vista r).length ≤ candidate) then none else do
        if !(List.range last).all (fun r =>
            (levelNodes vista r).all (fun i => !(children vista i (r+1)).isEmpty)) then none else do
          let anchor ← ((List.range (last + 1)).reverse).find? (flat vista)
          let values ← solveLinear? (levelNodes vista anchor).length
            (anchorRows vista anchor leaders)
          let natural ← positiveNaturals? values
          if natural.toList.sum != candidate then none else do
            let weights := propagateWeights vista anchor natural
            if !(List.range anchor).all (fun r => r == 0 ||
                (levelNodes vista (r-1)).all (fun parent =>
                  ((levelNodes vista r).map (fun v =>
                    countFrom (vista.node v) parent * (weights[v]?.getD 0))).sum ==
                  ((children vista parent r).map (fun v =>
                    (vista.node v).degree * (weights[v]?.getD 0))).sum)) then none else do
              if !(levelNodes vista anchor).all (fun v =>
                  ((levelNodes vista last).filter (fun descendant =>
                    ascend vista (last-anchor) descendant == some v)).length ≤
                    (weights[v]?.getD 0)) then none else
                return ⟨anchor, weights⟩ := by
  unfold audit? auditPlan auditPrefix?
  by_cases first : (!vista.valid || leaders == 0 || candidate < leaders || last == 0 ||
      (vista.node vista.bottom).level < last) = true
  · simp only [first, if_true]; rfl
  · simp only [first]
    by_cases second : (!(levelNodes vista 0).any (fun i => (vista.node i).leader)) = true
    · simp only [second, if_true]; rfl
    · simp only [second]
      by_cases third : (!(List.range (last + 1)).all (fun r =>
          (levelNodes vista r).length ≤ candidate)) = true
      · simp only [third, if_true]; rfl
      · simp only [third]
        by_cases fourth : (!(List.range last).all (fun r =>
            (levelNodes vista r).all (fun i => !(children vista i (r+1)).isEmpty))) = true
        · simp only [fourth, if_true]; rfl
        · simp only [fourth]
          cases ((List.range (last + 1)).reverse).find? (flat vista) <;> rfl


structure LocalState where
  leaders : Nat
  vista : Vista
  output : Option Nat
deriving Repr, BEq, DecidableEq

def initialState (leaders : Nat) (isLeader : Bool) : LocalState :=
  ⟨leaders, initialVista isLeader, none⟩

def candidateAt (leaders round : Nat) : Option (Nat × Nat) :=
  if leaders == 0 || round ≤ leaders then none
  else if leaders == 1 then
    if round % 2 == 1 then
      let candidate := (round + 1) / 2
      some (candidate, candidate)
    else none
  else if round % 2 == 0 then
    let candidate := round / 2 + 1
    if candidate > leaders then some (candidate, candidate - 1) else none
  else none

/-- The optimized schedule selects at most one audit in a round. -/
def scheduledPlan (leaders : Nat) (vista : Vista) : SolverPlan (Option Nat) :=
  let round := (vista.node vista.bottom).level
  if round == leaders &&
      !(levelNodes vista 0).any (fun i => !(vista.node i).leader) then .done (some leaders)
  else match candidateAt leaders round with
    | none => .done none
    | some (candidate, last) =>
        (auditPlan vista leaders candidate last).map
          (fun result => if result.isSome then some candidate else none)

/-- Solver-call plan for the actual local transition, with updates before
candidate testing and no calls by already halted agents. -/
def advancePlan (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) : SolverPlan (Option LocalState) :=
  if state.output.isSome then .done (some state)
  else if state.leaders == 0 then .done none
  else match updateVista? state.vista received outdegree with
    | none => .done none
    | some vista => (scheduledPlan state.leaders vista).map
        (fun output => some { state with vista := vista, output := output })

/-- Send the old state before calling this transition with the learned degree. -/
def advance? (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) : Option LocalState := (advancePlan state received outdegree).eval

theorem advance_unfold (state : LocalState) (received : List (Vista × Nat)) (outdegree : Nat) :
    advance? state received outdegree =   if state.output.isSome then some state else do
    if state.leaders == 0 then none else do
      let vista ← updateVista? state.vista received outdegree
      let round := (vista.node vista.bottom).level
      let output :=
        if round == state.leaders &&
            !(levelNodes vista 0).any (fun i => !(vista.node i).leader) then
          some state.leaders
        else match candidateAt state.leaders round with
          | none => none
          | some (candidate, last) =>
              if (audit? vista state.leaders candidate last).isSome then some candidate else none
      return { state with vista := vista, output := output }
 := by
  unfold advance? advancePlan
  split
  · rfl
  · split
    · rfl
    · cases updateVista? state.vista received outdegree with
      | none => rfl
      | some vista =>
          simp only [SolverPlan.eval_map, scheduledPlan]
          dsimp only [bind, pure]
          rw [Option.bind_some]
          split
          · rfl
          · cases candidateAt state.leaders (vista.node vista.bottom).level with
            | none => rfl
            | some pair => simp only [SolverPlan.eval_map]; rfl

theorem advance_halted (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) (h : state.output.isSome = true) :
    advance? state received outdegree = some state := by
  simp [advance_unfold, h]

end Counting.Executable
