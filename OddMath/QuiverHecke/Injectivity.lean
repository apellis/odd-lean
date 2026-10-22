/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GrothendieckIntegral
import OddMath.QuiverHecke.PairingRadical
import OddMath.SKM.DimensionFormula
import OddMath.SKM.LaurentianK0
import OddMath.SKM.MatchingEndpointSupport
import OddMath.CoveringQuantum.UDot.FiniteWeightForm
import OddMath.CoveringQuantum.UDot.ContextualExchange

/-!
# Injectivity of `γ`: BE2 Theorem 12.1

Brundan–Ellis, arXiv:1701.04133v2, Theorem 12.1: if the Nondegeneracy Conjecture holds, the
homomorphism `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` of Theorem 11.7 is injective.

The proof follows the paper. An element `x` of the `ℒ`-form with `γ(x) = 0` may be taken in a
single weight block `1_μ U̇ 1_ν`. There it is a combination of mixed words `θ_a 1_ν` with
coefficients in `𝕃 = ℚ(q)[π]/(π² - 1)`; after clearing denominators the coefficients lie in
`ℒ = ℤπ[q, q⁻¹]`, and `γ` sends `θ_a 1_ν` to the class of the word `a`
(`gammaInt_algebraWord`). Pairing a vanishing combination of classes with the class of a word `b`
and using the graded-dimension formula (dum) of the paper
(`SKM.hom_dimension_eq_form_mul_sym`, which is where the Nondegeneracy Conjecture enters) shows
that `(θ_b 1_ν, x) = 0` for every word `b`; nondegeneracy of the form of Theorem 10.1 then gives
`x = 0`.

Hypotheses. Besides the Nondegeneracy Conjecture, the theorem keeps the hypotheses of the
results it uses: the hypotheses of §9 on the scalars and a ground field (Theorem 11.7); the route
hypothesis `DegreeLocallyFinite` of Theorem 11.7; and, for nondegeneracy of the form
(`FiniteWeightForm.sesquilinearForm_nondegenerate`), finitely many colours, a finitely generated
free weight lattice, linearly independent roots and coroots, and bar-consistent data. The paper
states Theorem 12.1 for the setting of §9 with the Nondegeneracy Conjecture as its only
hypothesis; the remaining hypotheses are route hypotheses recorded in the README.

## Main results

* `SerreComplex.gammaInt_algebraWord`: `γ(θ_a 1_ν) = [E_a 1_ν]`.
* `SerreComplex.theorem_12_1`: `γ` is injective.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LaurentPolynomial
open CoveringQuantum CoveringQuantum.UDot
open CoveringQuantum.UDot.GenericVerma.MixedGram CoveringQuantum.UDot.GenericTensor

/-! ### Mixed words span the modified algebra -/

namespace MixedWordSpan

variable {I X : Type*} [AddCommGroup X] (D : CoveringQuantum.RootDatum I X)

local notation "𝕌" => CoveringUDot Coefficients.Ring D Coefficients.q Coefficients.pi

/-- The `𝕃`-span of the mixed words with right weight `η`. -/
def wordSpan (η : X) : Submodule Coefficients.Ring 𝕌 :=
  Submodule.span Coefficients.Ring
    (Set.range fun a : List (Bool × I) => (algebraWord D η a : 𝕌))

theorem algebraWord_mem_wordSpan (η : X) (a : List (Bool × I)) :
    (algebraWord D η a : 𝕌) ∈ wordSpan D η :=
  Submodule.subset_span ⟨a, rfl⟩

theorem gen_mul_algebraWord_mem (η : X) (g : Gen I X) (a : List (Bool × I)) :
    mk D Coefficients.q Coefficients.pi (FreeAlgebra.ι _ g) * (algebraWord D η a : 𝕌) ∈
      wordSpan D η := by
  have hw := algebraWord_mem_block D η a
  cases g with
  | one μ =>
    change UDot.one D _ _ μ * _ ∈ _
    rw [one_mul_of_mem_block _ _ _ hw]
    split_ifs
    · exact algebraWord_mem_wordSpan D η a
    · exact zero_mem _
  | e i μ =>
    change UDot.E D _ _ i μ * _ ∈ _
    by_cases h : μ = η + shift D a
    · subst h
      exact algebraWord_mem_wordSpan D η ((true, i) :: a)
    · rw [mul_eq_zero_of_mem_block _ _ _ (x := UDot.E D Coefficients.q Coefficients.pi i μ)
        (halfGen_mem_block D Coefficients.q Coefficients.pi true i μ) hw h]
      exact zero_mem _
  | f i μ =>
    change UDot.F D _ _ i μ * _ ∈ _
    by_cases h : μ = η + shift D a
    · subst h
      exact algebraWord_mem_wordSpan D η ((false, i) :: a)
    · rw [mul_eq_zero_of_mem_block _ _ _ (x := UDot.F D Coefficients.q Coefficients.pi i μ)
        (halfGen_mem_block D Coefficients.q Coefficients.pi false i μ) hw h]
      exact zero_mem _

theorem mul_mem_wordSpan (η : X) (x : 𝕌) {y : 𝕌} (hy : y ∈ wordSpan D η) :
    x * y ∈ wordSpan D η := by
  obtain ⟨z, rfl⟩ := mk_surjective D Coefficients.q Coefficients.pi x
  induction z using FreeAlgebra.induction generalizing y with
  | grade0 c =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ c hy
  | grade1 g =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact gen_mul_algebraWord_mem D η g a
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | add a b ha hb => rw [map_add, add_mul]; exact add_mem (ha hy) (hb hy)
  | mul a b ha hb => rw [map_mul, mul_assoc]; exact ha (hb hy)

/-- Every element of a block `1_μ U̇ 1_η` is a combination of mixed words ending at `η`. -/
theorem blockProj_mem_wordSpan (μ η : X) (x : 𝕌) :
    blockProj D Coefficients.q Coefficients.pi μ η x ∈ wordSpan D η := by
  rw [blockProj_apply, mul_assoc]
  apply mul_mem_wordSpan
  apply mul_mem_wordSpan
  have h := algebraWord_mem_wordSpan D η []
  simpa only [algebraWord] using h

/-- The mixed words of a fixed block. -/
def blockWords (μ η : X) : {a : List (Bool × I) // η + shift D a = μ} → 𝕌 :=
  fun a => (algebraWord D η a.1 : 𝕌)

/-- Every element of a block is a combination of the mixed words of that block. -/
theorem blockProj_mem_span_blockWords (μ η : X) (x : 𝕌) :
    blockProj D Coefficients.q Coefficients.pi μ η x ∈
      Submodule.span Coefficients.Ring (Set.range (blockWords D μ η)) := by
  have h := blockProj_mem_wordSpan D μ η x
  rw [← blockProj_eq_self D Coefficients.q Coefficients.pi
    (blockProj_mem D Coefficients.q Coefficients.pi μ η x)]
  have hmap : (wordSpan D η).map (blockProj D Coefficients.q Coefficients.pi μ η) ≤
      Submodule.span Coefficients.Ring (Set.range (blockWords D μ η)) := by
    rw [wordSpan, Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    rw [blockProj_of_mem _ _ _ (algebraWord_mem_block D η a)]
    split_ifs with hab
    · have hμ : η + shift D a = μ := (congrArg Prod.fst hab).symm
      exact Submodule.subset_span ⟨⟨a, hμ⟩, rfl⟩
    · exact zero_mem _
  exact hmap ⟨_, h, rfl⟩

/-- The `ℒ`-form lies in the modified algebra. -/
theorem lForm_le_modified (L : Type*) [CommRing L] [Algebra L Coefficients.Ring] {x : 𝕌}
    (hx : x ∈ lForm D Coefficients.q Coefficients.pi L) :
    x ∈ modified D Coefficients.q Coefficients.pi := by
  have hE : ∀ i n μ, mk D Coefficients.q Coefficients.pi (epow D i n μ) ∈
      modified D Coefficients.q Coefficients.pi := by
    intro i n
    induction n with
    | zero => intro μ; exact one_mem_modified _ _ _ μ
    | succ n ih =>
      intro μ
      rw [epow, map_mul]
      exact mul_mem (E_mem_modified _ _ _ _ _) (ih μ)
  have hF : ∀ i n μ, mk D Coefficients.q Coefficients.pi (fpow D i n μ) ∈
      modified D Coefficients.q Coefficients.pi := by
    intro i n
    induction n with
    | zero => intro μ; exact one_mem_modified _ _ _ μ
    | succ n ih =>
      intro μ
      rw [fpow, map_mul]
      exact mul_mem (F_mem_modified _ _ _ _ _) (ih μ)
  induction hx using NonUnitalAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with (⟨μ, rfl⟩ | ⟨⟨i, n, μ⟩, rfl⟩) | ⟨⟨i, n, μ⟩, rfl⟩
    · exact one_mem_modified _ _ _ μ
    · exact SMulMemClass.smul_mem _ (hE i n μ)
    · exact SMulMemClass.smul_mem _ (hF i n μ)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul Coefficients.Ring r x]
    exact SMulMemClass.smul_mem _ hx

/-- The generators `e_i 1_μ`, `f_i 1_μ` lie in the `ℒ`-form. -/
theorem halfGen_mem_lForm (L : Type*) [CommRing L] [Algebra L Coefficients.Ring] (b : Bool)
    (i : I) (μ : X) :
    halfGen D Coefficients.q Coefficients.pi b i μ ∈
      lForm D Coefficients.q Coefficients.pi L := by
  cases b
  · show UDot.F D _ _ i μ ∈ _
    rw [← fdp_one]
    exact fdp_mem_lForm _ _ _ _ i 1 _
  · show UDot.E D _ _ i μ ∈ _
    rw [← edp_one]
    exact edp_mem_lForm _ _ _ _ i 1 _

/-- Mixed words lie in the `ℒ`-form. -/
theorem algebraWord_mem_lForm (L : Type*) [CommRing L] [Algebra L Coefficients.Ring] (ζ : X)
    (a : List (Bool × I)) :
    (algebraWord D ζ a : 𝕌) ∈ lForm D Coefficients.q Coefficients.pi L := by
  induction a with
  | nil => exact one_mem_lForm _ _ _ _ ζ
  | cons g a ih => exact mul_mem (halfGen_mem_lForm D L g.1 g.2 _) ih

end MixedWordSpan

/-! ### Clearing denominators -/

namespace Coefficients
open CoveringQuantum.Coefficients

/-- Every `𝕃`-combination of vectors is, up to the image of an element of `intDenominators`, an
`ℒ`-combination. -/
theorem exists_integral_combination {ι M : Type*} [AddCommGroup M]
    [Module CoveringQuantum.Coefficients.Ring M] (v : ι → M)
    (c : ι →₀ CoveringQuantum.Coefficients.Ring) :
    ∃ (b : LaurentPolynomial Zπ) (_ : b ∈ intDenominators) (a : ι →₀ LaurentPolynomial Zπ),
      (a.sum fun t r => ofLaurentHom r • v t) = ofLaurentHom b • (c.sum fun t r => r • v t) := by
  have := isLocalization
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (R := LaurentPolynomial Zπ)
    (S := CoveringQuantum.Coefficients.Ring) intDenominators c.support c
  have hb' : ∀ t, ∃ r : LaurentPolynomial Zπ, ofLaurentHom r = ofLaurentHom b * c t := by
    intro t
    by_cases ht : t ∈ c.support
    · obtain ⟨r, hr⟩ := hb t ht
      exact ⟨r, hr.trans (Algebra.smul_def (R := LaurentPolynomial Zπ) _ _)⟩
    · refine ⟨0, ?_⟩
      rw [Finsupp.notMem_support_iff.1 ht, mul_zero, map_zero]
  choose a ha using hb'
  have ha0 : ∀ t, a t ≠ 0 → t ∈ c.support := by
    intro t h
    by_contra ht
    apply h
    apply ofLaurent_injective
    rw [map_zero]
    exact (ha t).trans (by rw [Finsupp.notMem_support_iff.1 ht, mul_zero])
  refine ⟨b, b.2, Finsupp.onFinset c.support a ha0, ?_⟩
  rw [Finsupp.onFinset_sum _ (fun t => by rw [map_zero, zero_smul]), Finsupp.sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ha t, mul_smul]

theorem isUnit_ofLaurentHom {b : LaurentPolynomial Zπ} (hb : b ∈ intDenominators) :
    IsUnit (ofLaurentHom b) := by
  have := isLocalization
  exact IsLocalization.map_units (S := CoveringQuantum.Coefficients.Ring) (M := intDenominators)
    ⟨b, hb⟩

end Coefficients

/-! ### `γ` on mixed words -/

namespace SerreComplex
open SKM.K0Relations

variable {I X : Type*} [AddCommGroup X] {k : Type*} [Field k]
variable (Q : CoveringQuantum.RootDatum I X) {S : SKM.Scalars Q.toSKM k} (hS : S.Homogeneous)
  (cs : SKM.CScalars S) (hf : Q.skmSymmetrizer.DegreeLocallyFinite)

local notation "𝕌" => CoveringUDot Coefficients.Ring Q Coefficients.q Coefficients.pi
local notation "Λ" => lForm Q Coefficients.q Coefficients.pi (LaurentPolynomial Zπ)

theorem choose_one_two : Nat.choose 1 2 = 0 := rfl

/-- `γ(e_i 1_μ) = [E_i 1_μ]` and `γ(f_i 1_μ) = [F_i 1_μ]`. -/
theorem gammaInt_halfGen (b : Bool) (i : I) (μ : X) :
    gammaInt Q hS cs hf ⟨_, MixedWordSpan.halfGen_mem_lForm Q _ b i μ⟩ =
      cls S Q.skmSymmetrizer hS (SKM.wt Q.toSKM μ [(b, i)]) μ [(b, i)] rfl 0 0 := by
  have hc : ((Nat.choose 1 2 : ℕ) : ℤ) = 0 := by rw [choose_one_two]; rfl
  cases b
  · have h : (⟨_, MixedWordSpan.halfGen_mem_lForm Q _ false i μ⟩ : Λ) =
        ⟨_, fdp_mem_lForm Q Coefficients.q Coefficients.pi _ i 1 μ⟩ :=
      Subtype.ext (show UDot.F Q _ _ i μ = _ from (fdp_one _ _ _ i μ).symm)
    rw [h, gammaInt_fdp, Fdp_congr Q.skmSymmetrizer hS rfl rfl rfl (m' := 0) (p' := 0)
      (by rw [hc, mul_zero, neg_zero]) rfl _ (wt_rep (-μ) 1),
      ← F_eq_Fdp Q.skmSymmetrizer hS i μ _ (wt_rep (-μ) 1), SKM.K0Relations.F]
    exact cls_congr _ _ (by simp [SKM.wt, SKM.sh, sub_eq_add_neg, add_comm]) rfl rfl _ _ _ _
  · have h : (⟨_, MixedWordSpan.halfGen_mem_lForm Q _ true i μ⟩ : Λ) =
        ⟨_, edp_mem_lForm Q Coefficients.q Coefficients.pi _ i 1 μ⟩ :=
      Subtype.ext (show UDot.E Q _ _ i μ = _ from (edp_one _ _ _ i μ).symm)
    rw [h, gammaInt_edp, Edp_congr Q.skmSymmetrizer hS rfl rfl rfl (m' := 0) (p' := 0)
      (by rw [hc, mul_zero]) (by rw [choose_one_two, Nat.cast_zero, zero_mul]) _ (wt_rep μ 1),
      ← E_eq_Edp Q.skmSymmetrizer hS i μ _ (wt_rep μ 1), SKM.K0Relations.E]
    exact cls_congr _ _ (by simp [SKM.wt, SKM.sh, add_comm]) rfl rfl _ _ _ _

/-- **`γ` on mixed words**: `γ(θ_a 1_ζ) = [E_a 1_ζ]`, the class of the word `a`. -/
theorem gammaInt_algebraWord (ζ : X) (a : List (Bool × I)) :
    gammaInt Q hS cs hf ⟨_, MixedWordSpan.algebraWord_mem_lForm Q _ ζ a⟩ =
      cls S Q.skmSymmetrizer hS (SKM.wt Q.toSKM ζ a) ζ a rfl 0 0 := by
  induction a with
  | nil => exact (gammaInt_one Q hS cs hf ζ).trans (by rw [← cls_nil]; rfl)
  | cons g a ih =>
    obtain ⟨b, i⟩ := g
    have hmul : (⟨_, MixedWordSpan.algebraWord_mem_lForm Q _ ζ ((b, i) :: a)⟩ : Λ) =
        ⟨_, MixedWordSpan.halfGen_mem_lForm Q _ b i (ζ + shift Q a)⟩ *
          ⟨_, MixedWordSpan.algebraWord_mem_lForm Q _ ζ a⟩ := rfl
    have hw : ζ + shift Q a = SKM.wt Q.toSKM ζ a := (mixed_word_physical_weight Q ζ a).symm
    rw [hmul, map_mul, ih, gammaInt_halfGen,
      cls_congr Q.skmSymmetrizer hS (by rw [hw]) hw rfl rfl rfl 0 0, cls_mul_cls,
      add_zero (0 : ℤ), add_zero (0 : ZMod 2)]
    exact cls_congr _ _ (SKM.wt_append _ ζ [(b, i)] a).symm rfl rfl _ _ _ _

theorem gammaInt_algebraWord_of_eq (ζ μ : X) (a : List (Bool × I)) (h : SKM.wt Q.toSKM ζ a = μ) :
    gammaInt Q hS cs hf ⟨_, MixedWordSpan.algebraWord_mem_lForm Q _ ζ a⟩ =
      cls S Q.skmSymmetrizer hS μ ζ a h 0 0 := by
  subst h
  exact gammaInt_algebraWord Q hS cs hf ζ a

/-! ### The pairing of word classes is a Hom dimension -/

/-- The weight object `μ` of the graded 2-category. -/
abbrev weightObj (μ : X) : SKM.UGr Q.toSKM S Q.skmSymmetrizer hS := ⟨μ⟩

/-- The graded dimension pairing of the classes of two words `b`, `a` from `ν` to `μ`, at
`π = σ`, is the graded superdimension of `HOM(E_b 1_ν, E_a 1_ν)` at `π = σ`. -/
theorem evalSeries_pairing_blockClass (μ ν : X) (a b : List (SKM.Letter I))
    (ha : SKM.wt Q.toSKM ν a = μ) (hb : SKM.wt Q.toSKM ν b = μ) (σ : ℤ) (hσ : σ * σ = 1) :
    let _ := SKM.UGr.degreeHomFinite Q.skmSymmetrizer cs hS hf (weightObj Q hS μ) (weightObj Q hS ν)
    evalSeries σ hσ (GSKar.pairing k
      (SKM.UGr.homBoundedBelow Q.skmSymmetrizer cs hS hf (weightObj Q hS μ) (weightObj Q hS ν))
      (GSKar.of k (SKM.K0Relations.word S Q.skmSymmetrizer hS μ ν b hb) 0 0)
      (blockClass S Q.skmSymmetrizer hS μ ν a ha 0 0)) =
      SKM.homDimension Q.skmSymmetrizer cs hS hf ν b a σ := by
  let _ := SKM.UGr.degreeHomFinite Q.skmSymmetrizer cs hS hf (weightObj Q hS μ) (weightObj Q hS ν)
  ext z
  rw [coeff_evalSeries, SKM.homDimension_coeff, GSKar.coeff_pairing]
  change ((Zπ.eval σ hσ (GSKar.superCoeff k (GSKar.of k _ 0 0) z
    (K₀.mk (GSKar.of k (SKM.K0Relations.word S Q.skmSymmetrizer hS μ ν a ha) 0 0))) : ℤ) : ℚ) = _
  rw [GSKar.superCoeff_of, map_add, map_mul, map_natCast, map_natCast, Zπ.eval_π]
  have hsum : ∀ f : ZMod 2 → ℚ, ∑ p : ZMod 2, f p = f 0 + f 1 := fun f => Fin.sum_univ_two f
  rw [hsum]
  have hfin : ∀ p : ZMod 2, SKM.wordHomComponent Q.skmSymmetrizer S ν b a (z, p) =
      (SKM.pres Q.toSKM S).homDeg (SKM.gdeg Q.toSKM Q.skmSymmetrizer) (SKM.ob Q.toSKM ν b)
        (SKM.ob Q.toSKM ν a) z ⊓ (SKM.pres Q.toSKM S).homDeg
          (StringDiagrams.Presentation.parityDeg (SKM.sig Q.toSKM)) (SKM.ob Q.toSKM ν b)
          (SKM.ob Q.toSKM ν a) p := fun p => by
    rw [SKM.wordHomComponent, SKM.homPar_eq_homDeg Q.skmSymmetrizer cs]
  have hfin' : ∀ p : ZMod 2,
      (Module.finrank k ↥(SKM.wordHomComponent Q.skmSymmetrizer S ν b a (z, p)) : ℚ) =
      Module.finrank k ↥((SKM.pres Q.toSKM S).homDeg (SKM.gdeg Q.toSKM Q.skmSymmetrizer)
        (SKM.ob Q.toSKM ν b) (SKM.ob Q.toSKM ν a) z ⊓ (SKM.pres Q.toSKM S).homDeg
          (StringDiagrams.Presentation.parityDeg (SKM.sig Q.toSKM)) (SKM.ob Q.toSKM ν b)
          (SKM.ob Q.toSKM ν a) p) := fun p => by rw [hfin p]
  rw [hfin' 0, hfin' 1]
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul]
  push_cast
  exact congrArg₂ (· + ·) rfl (mul_comm _ _)

/-! ### The coefficient series is nonzero -/

theorem wordBidegree_eq_zero_iff {D : SKM.Datum I X} (sy : SKM.Symmetrizer D)
    (l : List (SKM.SYMGen D)) (p : ZMod 2) :
    SKM.SYM.wordBidegree sy l = (0, p) ↔ l = [] ∧ p = 0 := by
  constructor
  · intro h
    cases l with
    | nil =>
      refine ⟨rfl, ?_⟩
      have := congrArg Prod.snd h
      simpa [SKM.SYM.wordBidegree] using this.symm
    | cons g l =>
      exfalso
      have h1 := congrArg Prod.fst h
      simp only [SKM.SYM.wordBidegree, List.map_cons, List.sum_cons] at h1
      have hn : 0 ≤ (l.map (SKM.symGenDegree D sy)).sum :=
        List.sum_nonneg (fun x hx => by
          obtain ⟨g', _, rfl⟩ := List.mem_map.mp hx
          exact (SKM.symGenDegree_pos sy g').le)
      have := SKM.symGenDegree_pos sy g
      omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The augmentation `SYM → k` killing every generator. -/
def symAugmentation (D : SKM.Datum I X) (K : Type*) [Field K] : SKM.SYM D K →ₐ[K] K :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K 0, by rintro _ _ ⟨⟩ <;> simp⟩

theorem symDimension_coeff_zero {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) (K : Type*)
    [Field K] (σ : ℚ) : (SKM.symDimension sy K σ).coeff 0 = 1 := by
  rw [SKM.symDimension_coeff]
  have hsum : ∀ f : ZMod 2 → ℚ, ∑ p : ZMod 2, f p = f 0 + f 1 := fun f => Fin.sum_univ_two f
  have hc : ∀ p : ZMod 2, SKM.SYM.component sy K (0, p) =
      if p = 0 then Submodule.span K {(1 : SKM.SYM D K)} else ⊥ := by
    intro p
    have hset : {l | SKM.SYM.wordBidegree sy l = (0, p)} =
        if p = 0 then {([] : List (SKM.SYMGen D))} else ∅ := by
      ext l
      simp only [Set.mem_ofPred_eq, wordBidegree_eq_zero_iff]
      split_ifs with hp <;> simp [hp]
    rw [SKM.SYM.component, hset]
    split_ifs
    · simp [SKM.SYM.word]
    · simp
  have h1 : (1 : SKM.SYM D K) ≠ 0 := fun h => by
    have := congrArg (symAugmentation D K) h
    simp at this
  rw [hsum, hc, hc]
  simp [finrank_span_singleton h1]

theorem symDimension_ne_zero {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) (K : Type*)
    [Field K] (σ : ℚ) : SKM.symDimension sy K σ ≠ 0 := fun h => by
  have := symDimension_coeff_zero sy K σ
  rw [h] at this
  simp at this

/-! ### Theorem 12.1 -/

theorem toGrBlock_injective (μ ν : X) :
    Function.Injective (toGrBlock (Sc := S) Q.skmSymmetrizer hS μ ν) := fun _ _ h =>
  K₀Ring.of_injective (weight S Q.skmSymmetrizer hS μ) (weight S Q.skmSymmetrizer hS ν)
    (MulOpposite.op_injective h)

section Injectivity

variable [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X]

attribute [local instance] SKM.K0Relations.homModule

omit [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X] in
/-- Weights of the mixed words of a weight block, read physically. -/
theorem blockWord_wt {μ ν : X} (t : {a : List (Bool × I) // ν + shift Q a = μ}) :
    SKM.wt Q.toSKM ν t.1 = μ :=
  (mixed_word_physical_weight Q ν t.1).trans t.2

omit [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X] in
include hf in
/-- **Vanishing classes give vanishing values of the form**: if an `ℒ`-combination of the classes
of the words of a weight block vanishes in `K₀`, then the form of Theorem 10.1 pairs every mixed
word of the block trivially with the same combination of mixed words in `U̇`. This is the
categorical input of BE2 Theorem 12.1 (the Hom dimensions of Theorem 10.3, given the
Nondegeneracy Conjecture). -/
theorem form_algebraWord_eq_zero (hN : SKM.NondegeneracyConjecture cs) (μ ν : X)
    (a : {a : List (Bool × I) // ν + shift Q a = μ} →₀ LaurentPolynomial Zπ)
    (hZ : (a.sum fun t r =>
      r • blockClass S Q.skmSymmetrizer hS μ ν t.1 (blockWord_wt Q t) 0 0) = 0)
    (Y' : modified Q Coefficients.q Coefficients.pi)
    (hY' : Y' = a.sum fun t r => CoveringQuantum.Coefficients.ofLaurentHom r •
      algebraWord Q ν t.1)
    (b : List (Bool × I)) (hbμ : ν + shift Q b = μ) :
    sesquilinearForm Q (algebraWord Q ν b) Y' = 0 := by
  have hb : SKM.wt Q.toSKM ν b = μ := (mixed_word_physical_weight Q ν b).trans hbμ
  let _ := SKM.UGr.degreeHomFinite Q.skmSymmetrizer cs hS hf (weightObj Q hS μ) (weightObj Q hS ν)
  set P := GSKar.pairing k
    (SKM.UGr.homBoundedBelow Q.skmSymmetrizer cs hS hf (weightObj Q hS μ) (weightObj Q hS ν))
    (GSKar.of k (SKM.K0Relations.word S Q.skmSymmetrizer hS μ ν b hb) 0 0)
  have hP : ∀ σ : ℤ, ∀ hσ : σ * σ = 1, evalSeries σ hσ (P (a.sum fun t r =>
      r • blockClass S Q.skmSymmetrizer hS μ ν t.1 (blockWord_wt Q t) 0 0)) =
      signLaurent (σ : ℚ) (sq_eq_one_of_mul_self hσ) (sesquilinearForm Q
        (algebraWord Q ν b) Y') * SKM.symDimension Q.skmSymmetrizer k σ := by
    intro σ hσ
    rw [hY']
    simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hab : SKM.wt Q.toSKM 0 b = SKM.wt Q.toSKM 0 t.1 := by
      rw [mixed_word_physical_weight, mixed_word_physical_weight]
      have h1 := (mixed_word_physical_weight Q ν b).symm.trans hb
      have h2 := (mixed_word_physical_weight Q ν t.1).symm.trans (blockWord_wt Q t)
      rw [add_left_cancel (h1.trans h2.symm)]
    erw [GSKar.pairing_smul]
    rw [map_mul, evalSeries_laurentToSeries, evalSeries_pairing_blockClass,
      SKM.hom_dimension_eq_form_mul_sym Q cs hS hf hN ν b t.1 hab, mul_assoc]
    · rfl
    · exact hf
  apply Coefficients.eq_zero_of_signLaurent
  intro σ hσ'
  have hσ : σ * σ = 1 := by
    have : ((σ * σ : ℤ) : ℚ) = 1 := by push_cast; rw [← pow_two]; exact hσ'
    exact_mod_cast this
  have h := hP σ hσ
  rw [hZ, map_zero, map_zero] at h
  exact (mul_eq_zero.1 h.symm).resolve_right (symDimension_ne_zero _ k σ)

omit [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X] in
/-- An element of a weight block of `U̇` that pairs trivially with every mixed word of the block
pairs trivially with all of `U̇`. -/
theorem form_eq_zero_of_mem_block (μ ν : X) (Y' : modified Q Coefficients.q Coefficients.pi)
    (hY'B : (Y' : 𝕌) ∈ block Q Coefficients.q Coefficients.pi μ ν)
    (hform : ∀ b : List (Bool × I), ν + shift Q b = μ →
      sesquilinearForm Q (algebraWord Q ν b) Y' = 0)
    (z : modified Q Coefficients.q Coefficients.pi) : sesquilinearForm Q z Y' = 0 := by
  have hspan : Submodule.span Coefficients.Ring (Set.range (MixedWordSpan.blockWords Q μ ν)) ≤
      (modified Q Coefficients.q Coefficients.pi).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact (algebraWord Q ν t.1).2
  have hspanForm : ∀ w (hw : w ∈ Submodule.span Coefficients.Ring
      (Set.range (MixedWordSpan.blockWords Q μ ν))),
      sesquilinearForm Q ⟨w, hspan hw⟩ Y' = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, rfl⟩ := hw
      exact hform t.1 t.2
    | zero =>
      rw [show (⟨0, hspan (Submodule.zero_mem _)⟩ : modified Q Coefficients.q Coefficients.pi) = 0
        from rfl, map_zero, LinearMap.zero_apply]
    | add u v hu hv ihu ihv =>
      rw [show (⟨u + v, hspan (Submodule.add_mem _ hu hv)⟩ :
          modified Q Coefficients.q Coefficients.pi) = ⟨u, hspan hu⟩ + ⟨v, hspan hv⟩ from rfl,
        map_add, LinearMap.add_apply, ihu, ihv, add_zero]
    | smul r u hu ih =>
      rw [show (⟨r • u, hspan (Submodule.smul_mem _ r hu)⟩ :
          modified Q Coefficients.q Coefficients.pi) = r • ⟨u, hspan hu⟩ from rfl,
        LinearMap.map_smulₛₗ, LinearMap.smul_apply, ih, smul_zero]
  obtain ⟨f, hf, hfz⟩ := (mem_modified_iff Q Coefficients.q Coefficients.pi z.1).1 z.2
  have hz : z = ∑ b ∈ f.support, (⟨f b, block_le_modified _ _ _ b.1 b.2 (hf b)⟩ :
      modified Q Coefficients.q Coefficients.pi) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum, ← hfz]
    rfl
  rw [hz, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : b = (μ, ν)
  · subst hb
    have hfb : f (μ, ν) = blockProj Q Coefficients.q Coefficients.pi μ ν z.1 := by
      rw [← hfz, blockProj_sum _ _ _ f hf (μ, ν)]
    exact hspanForm _ (hfb ▸ MixedWordSpan.blockProj_mem_span_blockWords Q μ ν z.1)
  · apply sesquilinearForm_orthogonal Q b.1 b.2 μ ν _ Y' (hf b) hY'B
    by_contra hne
    push Not at hne
    exact hb (Prod.ext hne.1 hne.2)

/-- An element of `U̇` pairing trivially with all of `U̇` vanishes (Theorem 10.1). -/
theorem eq_zero_of_form_eq_zero (hD : Q.toSuperCartanDatum.BarConsistent)
    (hα : LinearIndependent ℤ Q.α) (hh : LinearIndependent ℤ Q.cd.coroot)
    (Y' : modified Q Coefficients.q Coefficients.pi)
    (hall : ∀ z, sesquilinearForm Q z Y' = 0) : Y' = 0 := by
  have hψ : psiModified Q Y' = 0 := by
    apply FiniteWeightForm.sesquilinearForm_nondegenerate Q hD hα hh
    intro w
    rw [sesquilinearForm_psi_comm, psiModified_psiModified]
    exact hall _
  rw [← psiModified_psiModified Q Y', hψ, map_zero]

/-- The block step of Theorem 12.1. -/
theorem blockProj_eq_zero (hN : SKM.NondegeneracyConjecture cs)
    (hD : Q.toSuperCartanDatum.BarConsistent) (hα : LinearIndependent ℤ Q.α)
    (hh : LinearIndependent ℤ Q.cd.coroot) (x : Λ) (hx : gammaInt Q hS cs hf x = 0) (μ ν : X) :
    blockProj Q Coefficients.q Coefficients.pi μ ν (x : 𝕌) = 0 := by
  obtain ⟨y, hy_def⟩ : ∃ y, y = blockProj Q Coefficients.q Coefficients.pi μ ν (x : 𝕌) :=
    ⟨_, rfl⟩
  rw [← hy_def]
  have hyL : y ∈ Λ := by
    rw [hy_def, blockProj_apply]
    exact mul_mem (mul_mem (one_mem_lForm _ _ _ _ μ) x.2) (one_mem_lForm _ _ _ _ ν)
  have hγy : gammaInt Q hS cs hf ⟨y, hyL⟩ = 0 := by
    have : (⟨y, hyL⟩ : Λ) = ⟨_, one_mem_lForm Q Coefficients.q Coefficients.pi _ μ⟩ * x *
        ⟨_, one_mem_lForm Q Coefficients.q Coefficients.pi _ ν⟩ :=
      Subtype.ext (by simp [hy_def, blockProj_apply])
    rw [this, map_mul, map_mul, hx, mul_zero, zero_mul]
  -- `y` is a `𝕃`-combination of the mixed words of the block; clear denominators
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (MixedWordSpan.blockProj_mem_span_blockWords Q μ ν (x : 𝕌))
  obtain ⟨d, hd, a, had⟩ := Coefficients.exists_integral_combination
    (MixedWordSpan.blockWords Q μ ν) c
  rw [hc, ← hy_def] at had
  have hyB : y ∈ block Q Coefficients.q Coefficients.pi μ ν := hy_def ▸ blockProj_mem _ _ _ μ ν _
  -- the `ℒ`-combination in the `ℒ`-form
  obtain ⟨Y, hYdef⟩ : ∃ Y : Λ,
      Y = a.sum fun t r => r • (⟨_, MixedWordSpan.algebraWord_mem_lForm Q _ ν t.1⟩ : Λ) :=
    ⟨_, rfl⟩
  have hYval : (Y : 𝕌) = a.sum fun t r =>
      CoveringQuantum.Coefficients.ofLaurentHom r • MixedWordSpan.blockWords Q μ ν t := by
    simp only [hYdef, Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact (algebraMap_smul CoveringQuantum.Coefficients.Ring (a t) _).symm
  have hY0 : gammaInt Q hS cs hf Y = 0 := by
    have : Y = d • (⟨y, hyL⟩ : Λ) := Subtype.ext (by
      rw [hYval, had, SetLike.val_smul]
      exact algebraMap_smul CoveringQuantum.Coefficients.Ring d y)
    rw [this, map_smul, hγy, smul_zero]
  -- the classes of the weight block
  have hZ : (a.sum fun t r =>
      r • blockClass S Q.skmSymmetrizer hS μ ν t.1 (blockWord_wt Q t) 0 0) = 0 := by
    refine toGrBlock_injective Q hS μ ν (Eq.trans ?_ (hY0.trans (map_zero _).symm))
    rw [hYdef]
    simp only [Finsupp.sum, map_sum, map_smul, toGrBlock_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    exact (gammaInt_algebraWord_of_eq Q hS cs hf ν μ t.1 (blockWord_wt Q t)).symm
  -- the form vanishes on the element of `U̇`, so it vanishes
  have hYm : (Y : 𝕌) ∈ block Q Coefficients.q Coefficients.pi μ ν := by
    rw [hYval, had]
    exact Submodule.smul_mem _ _ hyB
  have hY' : (⟨(Y : 𝕌), block_le_modified _ _ _ μ ν hYm⟩ :
      modified Q Coefficients.q Coefficients.pi) = 0 := by
    refine eq_zero_of_form_eq_zero Q hD hα hh _ (form_eq_zero_of_mem_block Q μ ν _ hYm ?_)
    refine form_algebraWord_eq_zero Q hS cs hf hN μ ν a hZ _ (Subtype.ext ?_)
    rw [hYval]
    simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rfl
  have hdy : CoveringQuantum.Coefficients.ofLaurentHom d • y = 0 := by
    rw [← had, ← hYval]
    exact congrArg Subtype.val hY'
  exact (Coefficients.isUnit_ofLaurentHom hd).smul_left_cancel.1 (hdy.trans (smul_zero _).symm)

/-- **BE2 Theorem 12.1** (Brundan–Ellis, arXiv:1701.04133v2): if the Nondegeneracy Conjecture
holds, the homomorphism `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` of Theorem 11.7 is injective.

Route hypotheses (README): `DegreeLocallyFinite` (from Theorem 11.7), and for nondegeneracy of the
form of Theorem 10.1, finitely many colours, a free finitely generated weight lattice, linearly
independent roots and coroots, and bar-consistent data. -/
theorem theorem_12_1 (hN : SKM.NondegeneracyConjecture cs)
    (hD : Q.toSuperCartanDatum.BarConsistent) (hα : LinearIndependent ℤ Q.α)
    (hh : LinearIndependent ℤ Q.cd.coroot) :
    Function.Injective (gammaInt Q hS cs hf) := by
  suffices h0 : ∀ x : Λ, gammaInt Q hS cs hf x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.1 (h0 _ (by rw [map_sub, hxy, sub_self]))
  intro x hx
  have hxm := MixedWordSpan.lForm_le_modified Q (LaurentPolynomial Zπ) x.2
  obtain ⟨f, hf', hfx⟩ := (mem_modified_iff Q Coefficients.q Coefficients.pi _).1 hxm
  have hf0 : f = 0 := by
    ext b
    rw [← blockProj_sum _ _ _ f hf' b, hfx]
    exact blockProj_eq_zero Q hS cs hf hN hD hα hh x hx b.1 b.2
  apply Subtype.ext
  rw [← hfx, hf0]
  simp

end Injectivity

end SerreComplex

end OddMath.QuiverHecke
