import OddMath.Frontier.OddLRThm38
import OddMath.Frontier.OddLRThm38Controls

open scoped BigOperators
open OddMath.Frontier OddMath.SkewPolynomial

/-! Audit.  Every headline statement is restated below with its
full type and NO hypothesis other than the row bound `λ.colLen 0 ≤ n+2` (thm38, sK_eq_schur)
or the height condition `N < λ.colLen 0` (thm38_tall). -/

-- Definitional checks: the hypotheses discharged are the existing ones, verbatim.
example (N : ℕ) : OddLRElimination.Pieri310 N =
    ∀ (lam : YoungDiagram) (k : ℕ),
      CompleteTableauExpansion.sp N lam * CompleteTableauExpansion.sp N (TableauExtremal.columnShape k) =
        ∑ I ∈ OddLRElimination.stripRows lam k,
          (-1 : ℤ) ^ (∑ a ∈ I, OddLRElimination.belowRows lam a) •
            CompleteTableauExpansion.sp N (OddLRElimination.addStrip lam k I) := rfl
example (n : ℕ) : OddLREKIdentification.EliminationC n =
    ∀ lam : YoungDiagram, lam.colLen 0 ≤ n + 2 →
      CompleteTableauExpansion.sp (n+2) lam =
        OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam) := rfl
example (N : ℕ) (lam : YoungDiagram) : CompleteTableauExpansion.sp N lam =
    (-1 : ℤ) ^ (TableauStripSigns.directNorth lam + TableauStripSigns.north lam) •
      TableauPolynomial.tableauPolynomial N lam := rfl

-- Headline statements, restated with no residual hypothesis.
example : ∀ N : ℕ, OddLRElimination.Pieri310 N := OddLRThm38.pieri310
example : ∀ n : ℕ, OddLRElimination.Pieri310Bounded n := OddLRThm38.pieri310Bounded
example : ∀ n : ℕ, OddLREKIdentification.EliminationC n := OddLRThm38.eliminationC
example (n : ℕ) (α : OddSymmetrizer.PartitionExponent n) :
    CompleteTableauExpansion.sp (n+2) (OddLRElimination.toYoung α) = OddSymmetrizer.schur n α :=
  OddLRThm38.sp_eq_schur n α
example (n : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ n + 2) :
    OddLREKIdentification.piN (n+2) (OddLREKIdentification.sK lam) =
        CompleteTableauExpansion.sp (n+2) lam ∧
      CompleteTableauExpansion.sp (n+2) lam =
        OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam) :=
  OddLRThm38.thm38 n lam hl
example (n : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ n + 2) :
    OddLREKIdentification.piN (n+2) (OddLREKIdentification.sK lam) =
      OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam) :=
  OddLRThm38.sK_eq_schur n lam hl
example (N : ℕ) (lam : YoungDiagram) (h : N < lam.colLen 0) :
    OddLREKIdentification.piN N (OddLREKIdentification.sK lam) = 0 ∧
      CompleteTableauExpansion.sp N lam = 0 :=
  OddLRThm38.thm38_tall N lam h
example (N : ℕ) (lam : YoungDiagram) :
    OddLREKIdentification.piN N (OddLREKIdentification.sK lam) =
      CompleteTableauExpansion.sp N lam :=
  OddLRThm38.sK_eq_sp N lam

-- The unconditional theorem is the existing conditional one applied to the discharged
-- hypothesis (no restatement of the hypothesis).
example (n : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ n + 2) :
    OddLRThm38.thm38 n lam hl =
      OddLREKIdentification.thm38_conditional n (OddLRThm38.eliminationC n) lam hl := rfl

#check @OddLRThm38.pieri310
#check @OddLRThm38.thm38
#print axioms OddLRThm38.column_eq_columnShape
#print axioms OddLRThm38.belowCount_eq_belowRows
#print axioms OddLRThm38.rowLen_of_vertical
#print axioms OddLRThm38.stripBelow_of_vertical
#print axioms OddLRThm38.rowsOf_mem
#print axioms OddLRThm38.addStrip_rowsOf
#print axioms OddLRThm38.card_addStrip
#print axioms OddLRThm38.pieri310
#print axioms OddLRThm38.pieri310Bounded
#print axioms OddLRThm38.sp_eq_schur
#print axioms OddLRThm38.toExponent_eq_ofYoung
#print axioms OddLRThm38.eliminationC
#print axioms OddLRThm38.thm38
#print axioms OddLRThm38.sK_eq_schur
#print axioms OddLRThm38.thm38_tall
#print axioms OddLRThm38.sK_eq_sp
#print axioms OddLRThm38Controls.offByOne_distinguished
#print axioms OddLRThm38Controls.belowCount_col2_0
#print axioms OddLRThm38Controls.belowRows_col2_0

-- Sweep every owned constant: every logical declaration is safe and uses standard axioms only.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.OddLRThm38,
        `OddMath.Frontier.OddLRThm38Controls].contains env.header.moduleNames[idx.toNat]!
    | none => false
  for required in [``OddLRThm38.pieri310, ``OddLRThm38.pieri310Bounded,
      ``OddLRThm38.sp_eq_schur, ``OddLRThm38.eliminationC, ``OddLRThm38.thm38,
      ``OddLRThm38.sK_eq_schur, ``OddLRThm38.thm38_tall, ``OddLRThm38.sK_eq_sp,
      ``OddLRThm38Controls.offByOne_distinguished] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler && info.isUnsafe then
      stages := stages + 1
    else
      if info.isUnsafe then throwError "Unexpected non-safe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"
