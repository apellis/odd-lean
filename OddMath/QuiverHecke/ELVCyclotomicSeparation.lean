/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.WeightedDeformationIdeal
import OddMath.SKM.BubbleELVSpecialization

/-! # Explicit ELV cyclotomic polynomials in the native affine category

All multiplication is the actual signed coefficient extension. No SKM action
or identification of categorical bubbles is assumed here.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem extendedScore_antitone {t t' : List I} {s r : ℤ} (h : s ≤ r) :
    ExtendedScore D Sc t t' r ≤ ExtendedScore D Sc t t' s := by
  apply Submodule.span_mono
  rintro _ ⟨a, gs, hg, hs, rfl⟩
  exact ⟨a, gs, hg, h.trans hs, rfl⟩

def elvCyclotomic (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    coefficientObj D Sc (i.1 :: tail) ⟶ coefficientObj D Sc (i.1 :: tail) :=
  deformedCyclotomic D Sc (i.1 :: tail) N (SKM.SYM.elvMonicCoefficient D k i N)

theorem elvCyclotomic_mem_score (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    elvCyclotomic D Sc i tail N ∈ ExtendedScore D Sc (i.1 :: tail) (i.1 :: tail) (N : ℤ) :=
  deformedCyclotomic_mem_score D Sc _ _ _ (by simp)
    (SKM.SYM.elvMonicCoefficient_mem_coefficientAtLeast D k i N)

def evenCyclotomic (i : I) (tail : List I) (N : ℕ) :
    coefficientObj D Sc (i :: tail) ⟶ coefficientObj D Sc (i :: tail) :=
  deformedCyclotomic D Sc (i :: tail) N (SKM.SYM.evenMonicCoefficient D k i N)

theorem evenCyclotomic_mem_score (i : I) (hi : D.parity i = 0) (tail : List I) (N : ℕ) :
    evenCyclotomic D Sc i tail N ∈ ExtendedScore D Sc (i :: tail) (i :: tail) (N : ℤ) :=
  deformedCyclotomic_mem_score D Sc _ _ _ (by simp)
    (SKM.SYM.evenMonicCoefficient_mem_coefficientAtLeast D k i hi N)

/-- The exact coefficient relations and the colour-correct first-strand
polynomial are the generators of the proposed odd cyclotomic quotient. -/
def ELVGenerator (cutoff : I → ℕ) (t : List I)
    (r : coefficientObj D Sc t ⟶ coefficientObj D Sc t) : Prop :=
  (∃ a : SKM.SYM D k, a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff ∧
    r = sourceCoefficientHom D Sc a (𝟙 ((pres D Sc).obj (ob D t)))) ∨
  (∃ i : {i : I // D.parity i = 1}, ∃ tail, ∃ h : t = i.1 :: tail,
    r = eqToHom (congrArg (coefficientObj D Sc) h) ≫
      elvCyclotomic D Sc i tail (cutoff i.1) ≫
      eqToHom (congrArg (coefficientObj D Sc) h.symm)) ∨
  (∃ i : I, D.parity i = 0 ∧ ∃ tail, ∃ h : t = i :: tail,
    r = eqToHom (congrArg (coefficientObj D Sc) h) ≫
      evenCyclotomic D Sc i tail (cutoff i) ≫
      eqToHom (congrArg (coefficientObj D Sc) h.symm))

theorem elvGenerator_mem_score {cutoff : I → ℕ} {N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) {t : List I}
    {r : coefficientObj D Sc t ⟶ coefficientObj D Sc t}
    (hr : ELVGenerator D Sc cutoff t r) : r ∈ ExtendedScore D Sc t t (N : ℤ) := by
  rcases hr with ⟨a, ha, rfl⟩ | ⟨i, tail, h, rfl⟩ | ⟨i, hi, tail, h, rfl⟩
  · have hw := (SKM.SYM.mem_coefficientIdeal_iff D k _ _).mp
      (SKM.SYM.elvCoefficientIdeal_le_weight D k hN ha)
    have hm := highCoefficient_word_mem_score D Sc (t := t) (t' := t)
      (SKM.SYM.coefficientAtLeast_antitone D k (Nat.le_succ N) hw) [] (sChain_pl t [])
    simpa [coefficient_cl_nil, positionedScore, wordScore, crossCount] using hm
  · subst t
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact extendedScore_antitone D Sc (by exact_mod_cast hN i.1)
      (elvCyclotomic_mem_score D Sc i tail (cutoff i.1))
  · subst t
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact extendedScore_antitone D Sc (by exact_mod_cast hN i)
      (evenCyclotomic_mem_score D Sc i hi tail (cutoff i))

/-- The two-sided span of the explicit source relations, at fixed strand
number. Polynomial relations are imposed on precisely their own colour. -/
def ELVRelationSpan (cutoff : I → ℕ) (t t' : List I) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k {f | ∃ v : List I, v.length = t.length ∧
    ∃ r : coefficientObj D Sc v ⟶ coefficientObj D Sc v, ELVGenerator D Sc cutoff v r ∧
    ∃ a : coefficientObj D Sc t ⟶ coefficientObj D Sc v,
    ∃ b : coefficientObj D Sc v ⟶ coefficientObj D Sc t', a ≫ r ≫ b = f}

theorem elvRelationSpan_le_weighted {cutoff : I → ℕ} {N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) (t t' : List I) :
    ELVRelationSpan D Sc cutoff t t' ≤ WeightedRelationSpan D Sc t t' N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, r, hr, a, b, rfl⟩
  exact Submodule.subset_span ⟨v, hv, r, elvGenerator_mem_score D Sc hN hr, a, b, rfl⟩

/-- Explicit multicolour ELV coefficient relations and first-strand
deformations preserve every bounded affine PBW coefficient span. -/
theorem elv_quotient_injective_on_extendedAtMost {cutoff : I → ℕ} {t t' : List I}
    {d N : ℕ} (hN : ∀ i, N ≤ cutoff i) (hd : d + 2 * t.length.choose 2 < N) :
    Function.Injective (fun x : ExtendedAtMost D Sc t t' d =>
      (ELVRelationSpan D Sc cutoff t t').mkQ
        (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t')) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hm : (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t') - y ∈
      ELVRelationSpan D Sc cutoff t t' := (Submodule.Quotient.eq _).mp hxy
  exact Submodule.disjoint_def.mp
    (disjoint_extendedAtMost_extendedAtLeast D Sc (by omega)) _
    (Submodule.sub_mem _ x.property y.property)
    (weightedRelationSpan_le_extendedAtLeast D Sc t t' N
      (elvRelationSpan_le_weighted D Sc hN t t' hm))

/-- Even cutoffs alone suffice to detect every finite affine relation with
arbitrary abstract SYM coefficients. -/
theorem even_elv_quotients_jointly_detect {t t' : List I}
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ m, (ELVRelationSpan D Sc (fun _ => 2 * m) t t').mkQ f = 0) : f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc t t' f
  let m := d + 2 * t.length.choose 2 + 1
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc
    (cutoff := fun _ => 2 * m) (t := t) (t' := t') (d := d) (N := 2 * m)
    (fun _ => le_rfl) (by omega)
  have h := hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hf m)
  exact congrArg Subtype.val h

end OddMath.QuiverHecke
