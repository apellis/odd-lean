import OddMath.Frontier.EKRskBijection

/-!
# Audit: EK Thm 4.3 / (4.4)

Exact exported statement types (by `example`, checked against the production declarations),
and a transitive standard-axiom audit of every owned declaration in the three modules.
-/

open scoped BigOperators
open OddMath.Frontier TableauSign TableauContent DegreeShapes
namespace OddMath.Frontier.EKRskBijectionAudit
open EKRskBijection

attribute [local instance] degreeFintype

-- Matrices: row(A) = µ (row sums), col(A) = ρ (column sums), EK p.24/p.32.
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :
    Mat μ ρ = {A : Fin m → Fin n → ℕ // (∀ i, ∑ j, A i j = μ i) ∧ ∀ j, ∑ i, A i j = ρ j} := rfl
-- Content of a composition in paper labels 1..k.
example {k : ℕ} (c : Fin k → ℕ) : compContent c = ∑ i, Finsupp.single (i.val + 1) (c i) := rfl
-- The codomain hit by RSK: cont(P) = ρ, cont(Q) = µ.
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :
    Target μ ρ = Σ la : YoungDiagram, {P : PositiveTableau la // content P = compContent ρ} ×
      {Q : PositiveTableau la // content Q = compContent μ} := rfl
-- The codomain exactly as printed in (4.3): cont(P) = µ, cont(Q) = ρ.
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :
    PrintedTarget μ ρ = Σ la : YoungDiagram, {P : PositiveTableau la // content P = compContent μ} ×
      {Q : PositiveTableau la // content Q = compContent ρ} := rfl
-- Theorem 4.3 (contents as the RSK map/EK examples actually produce them).
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) : Function.Bijective (rsk μ ρ) :=
  rsk_bijective μ ρ
-- The map is the frozen fold (P state and every Q entry).
example {m n : ℕ} (A : Fin m → Fin n → ℕ) :
    (rskFold A).1 = (rskRec n m A).pState ∧
      ∀ p : ℕ × ℕ, (rskFold A).2 p = (rskRec n m A).2.2.1.entry p.1 p.2 := rsk_eq_frozen n m A
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) (A : Mat μ ρ) :
    (rsk μ ρ A).1 = (rskRec n m A.1).1 := rfl
-- The frozen step is existing `TableauInsertion.insert` plus recording at `newCell`.
example (n : ℕ) (s : St n × (ℕ × ℕ → ℕ)) (x : ℕ × Fin n) :
    foldStep n s x =
      (⟨(TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).shape,
        ⟨(TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).tableau,
          (TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).bounded⟩⟩,
        fun p => if p = (TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).newCell
          then x.1 + 1 else s.2 p) := rfl
-- EK's lexicographic two-line array (u = row index, v = column index, ties in v increasing).
example {m n : ℕ} (A : Fin m → Fin n → ℕ) :
    twoLine A = (List.finRange m).flatMap fun i => (rowWord (A i)).map fun j => (i.val, j) := rfl
-- Printed (4.3) obstruction, general and on EK's Example 4.5 data.
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) (hne : compContent μ ≠ compContent ρ)
    (A : Mat μ ρ) :
    ¬ (content (rsk μ ρ A).2.1.1 = compContent μ ∧ content (rsk μ ρ A).2.2.1 = compContent ρ) :=
  printed_codomain_obstruction μ ρ hne A
example : Nonempty (Mat (![2, 2] : Fin 2 → ℕ) (![2, 1, 1] : Fin 3 → ℕ)) ∧
    ∀ A : Mat (![2, 2] : Fin 2 → ℕ) (![2, 1, 1] : Fin 3 → ℕ),
      ¬ (content (rsk _ _ A).2.1.1 = compContent (![2, 2] : Fin 2 → ℕ) ∧
        content (rsk _ _ A).2.2.1 = compContent (![2, 1, 1] : Fin 3 → ℕ)) :=
  ex45_printed_obstruction
-- (4.4) as printed, unsigned Kostka numbers, λ over all diagrams with |µ| cells.
example (la : YoungDiagram) {k : ℕ} (c : Fin k → ℕ) :
    kostka0 la c = (tableauxOfContent la (compContent c)).card := rfl
example {m n : ℕ} (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :
    Nat.card (Mat μ ρ) = ∑ la : DegreeShape (∑ i, μ i), kostka0 la.val μ * kostka0 la.val ρ :=
  ek_eq_4_4 μ ρ
example (d : ℕ) : DegreeShape d = {la : YoungDiagram // la.card = d} := rfl

end OddMath.Frontier.EKRskBijectionAudit

#print axioms OddMath.Frontier.EKRskBijection.rsk_bijective
#print axioms OddMath.Frontier.EKRskBijection.rsk_eq_frozen
#print axioms OddMath.Frontier.EKRskBijection.rskRec_mirror
#print axioms OddMath.Frontier.EKRskBijection.printed_codomain_obstruction
#print axioms OddMath.Frontier.EKRskBijection.ex45_printed_obstruction
#print axioms OddMath.Frontier.EKRskBijection.ek_eq_4_4
#print axioms OddMath.Frontier.EKRskBijection.ex45a_production
#print axioms OddMath.Frontier.EKRskBijection.ex45b_production
#print axioms OddMath.Frontier.EKRskBijection.ex45c_production
#print axioms OddMath.Frontier.EKRskBijection.ex45d_production

-- All owned declarations (all three modules) are audited transitively.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKRskBijection,
        `OddMath.Frontier.EKRskBijectionControls,
        `OddMath.Frontier.EKRskBijectionAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``EKRskBijection.rsk_bijective, ``EKRskBijection.rsk_eq_frozen,
      ``EKRskBijection.rskRec_mirror, ``EKRskBijection.printed_codomain_obstruction,
      ``EKRskBijection.ex45_printed_obstruction, ``EKRskBijection.ek_eq_4_4,
      ``EKRskBijection.ex45a_production, ``EKRskBijection.ex45b_production,
      ``EKRskBijection.ex45c_production, ``EKRskBijection.ex45d_production,
      ``EKRskBijection.ex45a_rsk, ``EKRskBijection.ex45b_rsk, ``EKRskBijection.ex45c_rsk,
      ``EKRskBijection.ex45d_rsk, ``EKRskBijection.ex45_margins, ``EKRskBijection.ex44a_rsk,
      ``EKRskBijection.ex44b_rsk, ``EKRskBijection.ex44c_rsk,
      ``EKRskBijection.ex45a_P_content_is_columns, ``EKRskBijection.allSmall_images_nodup] do
    unless owned.any (fun (name, _) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler && info.isUnsafe then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' unsafe=true depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' unsafe=false depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"
