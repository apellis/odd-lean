import OddMath.QuiverHecke.CyclotomicAction.ELVModuleNilpotence
import OddMath.QuiverHecke.CyclotomicAction.ELVAffineDetection

noncomputable section
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u

section Modules
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Finite I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)
include sy hc in
example (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (M : TruncatedModules D Sc cutoff N)
      (v : TruncatedCategory D Sc cutoff N), v.word.Perm ν →
      let f : End (M.obj ((truncatedAppend D Sc cutoff N [i]).obj v)) :=
        ((moduleRestrictionDot D Sc cutoff N i).app (D.parity i) M).app (D.parity i) v
      f ^ e = 0 :=
  moduleRestrictionDot_pow_zero D Sc cutoff sy hc N ν i

example (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d →
        ∀ (σ : List I) (M : TruncatedModules D Sc cutoff N),
          (((moduleInduction D Sc cutoff N σ).obj M).toFunctor.mapEnd
            (⟨v⟩ : TruncatedCategory D Sc cutoff N) f) ^ e = 0 :=
  moduleInduction_positive_pow_zero D Sc cutoff sy hc N ν
end Modules

section Detection
variable {I X k : Type u} [AddCommGroup X] [Field k] [Finite I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

-- The nilpotent quotient is not forced to be zero: each specified affine PBW
-- basis element survives at high cutoffs, alongside the uniform dot exponent.
include hc in
example (v : List I) (a : NFIdx v v) :
    ∃ K : ℕ, ∀ (cutoff : I → ℕ) (N : ℕ),
      (∀ j ∈ v, K ≤ cutoff j) → K ≤ N →
      (truncatedIdeal D Sc cutoff N v v).mkQ (affineUnit D Sc cutoff v v
        (a.nf (D := D) (Sc := Sc))) ≠ 0 ∧
      ∃ e : ℕ, 0 < e ∧ ∀ (w : List I), w.Perm v →
        ∀ (r : ℕ) (i : I), w[r]? = some i →
          truncatedDot D Sc cutoff N w r ^ e = 0 := by
  obtain ⟨K, hK⟩ := affinePBW_detected_at_high_cutoffs D sy Sc hc v (a.deg D sy + 1)
  refine ⟨K, fun cutoff N hcut hN => ⟨?_,
    truncatedContent_dot_pow_zero D Sc cutoff sy hc N v⟩⟩
  have ha : a.nf (D := D) (Sc := Sc) ∈ affinePBWDegreeBelow D sy Sc v v (a.deg D sy + 1) :=
    Submodule.subset_span ⟨a, by change a.deg D sy < a.deg D sy + 1; omega, rfl⟩
  intro hz
  have he := hK cutoff N hcut hN v v (List.Perm.refl _) (List.Perm.refl _)
    (a₁ := ⟨a.nf, ha⟩) (a₂ := 0) (by simpa using hz)
  exact (linearIndependent_nf D Sc v v).ne_zero a (congrArg Subtype.val he)
end Detection

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence,
      `OddMath.QuiverHecke.CyclotomicAction.ELVModuleNilpotence] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
