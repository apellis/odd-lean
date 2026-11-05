/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctIdealSpan

/-! # The mixed crossing after both outer cyclotomic quotients

The full-coefficient crossing isomorphism required in Brundan–Ellis (1.12),
`DeformedActionAssembly.md` §§2–4. Equality (9.3) identifies the output-old
quotient with the first-factor quotient in the independently balanced source.
The literal cup-crossing-cap comparison is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary output postcomposition in the old-only append quotient. -/
def outputPost (i : I) (v : List I) {w z : List I} (r : hom D Sc cutoff w z) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v z :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v z)
    (Linear.rightComp k _ r) (fun _ hh => appendRelations_comp D Sc cutoff i hh r)

@[simp] theorem outputPost_projection (i : I) (v : List I) {w z : List I}
    (r : hom D Sc cutoff w z) (f : hom D Sc cutoff (v ++ [i]) w) :
    outputPost D Sc cutoff i v r (appendProjection D Sc cutoff i v w f) =
      appendProjection D Sc cutoff i v z (f ≫ r) := rfl

/-- Postcomposing a crossing class by an old ideal arrow lands in the
image of the literal first-factor tensor ideal. -/
theorem outputPost_shortCross_mem_map (i j : I) (v w z : List I)
    (r : hom D Sc cutoff w z) (hr : r ∈ ideal D Sc cutoff w z)
    (a : ShortTarget D Sc cutoff i j v w) :
    outputPost D Sc cutoff i v (rightContext D Sc cutoff [j] _ _ r)
      (shortCross D Sc cutoff i j v w a) ∈
      (firstIdeal D Sc cutoff i j v z).map (shortCross D Sc cutoff i j v z) := by
  let S := (firstIdeal D Sc cutoff i j v z).map (shortCross D Sc cutoff i j v z)
  have hzero : S.mkQ ∘ₗ outputPost D Sc cutoff i v
      (rightContext D Sc cutoff [j] _ _ r) ∘ₗ shortCross D Sc cutoff i j v w = 0 := by
    apply BalancedInduction.hom_ext
    intro s c b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j])).mkQ_surjective b
    change S.mkQ (outputPost D Sc cutoff i v _
      (shortCross D Sc cutoff i j v w (shortTensor D Sc cutoff i j v s.word w c _))) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨shortTensor D Sc cutoff i j v s.word z (c ≫ r)
      ((ideal D Sc cutoff v (s.word ++ [j])).mkQ b),
        Submodule.subset_span ⟨s.word, c ≫ r, comp_ideal D Sc cutoff c hr, _, rfl⟩, ?_⟩
    rw [shortCross_tensor, shortCrossPair_mk, shortCross_tensor, shortCrossPair_mk,
      outputPost_projection, rightContext_comp]
    simp only [Category.assoc]
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun hzero a)

/-- The second outer ideal is precisely accounted for by the first tensor ideal. -/
theorem projection_outputOldRelations_mem_map (i j : I) (hij : i ≠ j) (v t : List I)
    (f : hom D Sc cutoff (v ++ [i]) (t ++ [j]))
    (hf : f ∈ outputOldRelations D Sc cutoff j (v ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [j]) f ∈
      (firstIdeal D Sc cutoff i j v t).map (shortCross D Sc cutoff i j v t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, r, hr, c, rfl⟩ := hf
    obtain ⟨a, ha⟩ := shortCross_surjective D Sc cutoff i j hij v s
      (appendProjection D Sc cutoff i v (s ++ [j]) c)
    have hs := outputPost_shortCross_mem_map D Sc cutoff i j v s t r hr a
    rw [ha, outputPost_projection] at hs
    exact hs
  | zero =>
    simpa only [map_zero] using Submodule.zero_mem
      ((firstIdeal D Sc cutoff i j v t).map (shortCross D Sc cutoff i j v t))
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul a b _ hb => simpa only [map_smul] using Submodule.smul_mem _ a hb

/-- Exact kernel after identifying both outer quotient spans by (9.3). -/
theorem ker_canonical_shortCross (i j : I) (hij : i ≠ j) (v t : List I) :
    LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ
      shortCross D Sc cutoff i j v t) = firstIdeal D Sc cutoff i j v t := by
  apply le_antisymm
  · intro a ha
    obtain ⟨f, hf⟩ := appendProjection_surjective D Sc cutoff i v (t ++ [j])
      (shortCross D Sc cutoff i j v t a)
    have hi : f ∈ ideal D Sc cutoff (v ++ [i]) (t ++ [j]) := by
      have hz := LinearMap.mem_ker.mp ha
      change canonicalAppendTarget D Sc cutoff i v (t ++ [j])
        (shortCross D Sc cutoff i j v t a) = 0 at hz
      rw [← hf, canonicalAppendTarget_projection] at hz
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [ideal_eq_appendRelations_sup_outputOldRelations D Sc cutoff i j hij v t] at hi
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hi
    have he : appendProjection D Sc cutoff i v (t ++ [j]) c =
        shortCross D Sc cutoff i j v t a := by
      rw [← hf, ← hbc, map_add, (appendProjection_eq_zero_iff D Sc cutoff i v _ b).mpr hb,
        zero_add]
    obtain ⟨a', ha', h⟩ := projection_outputOldRelations_mem_map D Sc cutoff i j hij v t c hc
    have hsame : a' = a := shortCross_injective D Sc cutoff i j hij v t (h.trans he)
    exact hsame ▸ ha'
  · intro a ha
    rw [shortCross_quotient_square]
    change toCyclotomic D Sc cutoff i j v t (q D Sc cutoff i j v t a) = 0
    rw [LinearMap.mem_ker.mp (firstIdeal_le_ker_q D Sc cutoff i j v t ha), map_zero]

/-- Injectivity after both outer quotients, without tensor flatness. -/
theorem toCyclotomic_injective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Injective (toCyclotomic D Sc cutoff i j v t) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i j v t z
  have ha : a ∈ LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ
      shortCross D Sc cutoff i j v t) := by
    rw [shortCross_quotient_square]
    exact hz
  rw [ker_canonical_shortCross D Sc cutoff i j hij v t] at ha
  exact firstIdeal_le_ker_q D Sc cutoff i j v t ha

/-- Surjectivity after both outer quotients. -/
theorem toCyclotomic_surjective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Surjective (toCyclotomic D Sc cutoff i j v t) := by
  intro z
  obtain ⟨a, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [j]) z
  obtain ⟨b, rfl⟩ := shortCross_surjective D Sc cutoff i j hij v t a
  refine ⟨q D Sc cutoff i j v t b, ?_⟩
  exact (LinearMap.congr_fun (shortCross_quotient_square D Sc cutoff i j v t) b).symm

/-- The prescribed balanced crossing is an isomorphism in every distinct corner. -/
def cyclotomicEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    Source D Sc cutoff i j v t ≃ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff i j v t)
    ⟨toCyclotomic_injective D Sc cutoff i j hij v t,
      toCyclotomic_surjective D Sc cutoff i j hij v t⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
