/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.TwoStrandShifts
import Mathlib.CategoryTheory.Idempotents.Biproducts
import StringDiagrams.Super.KrullSchmidtLaurent

/-!
# Summands of a 1-morphism cut out by a homogeneous splitting

For a 1-morphism `w` of the graded SKM 2-category and a splitting of its identity
`1 = ∑_j σ_j λ_j`, `λ_i σ_j = δ_{ij} e`, by even homogeneous 2-morphisms with
`deg σ_j = m_j = -deg λ_j` and `e` even of degree zero, the completed hom category has
`w ≅ ⨁_j Q^{m_j} (w, e)`; hence `[w] = ∑_j q^{m_j} [(w, e)]` in split `K₀`.
This is the categorical step in Brundan–Ellis, arXiv:1701.04133v2, proof of Lemma 11.5.

## Main declarations

* `Summands.shifted`, `Summands.lift`, `Summands.raw`, `Summands.whole`.
* `Summands.class_whole`: `[w] = ∑_j [raw e (m j)]`.
* `Summands.class_raw_shift`: `T n • [raw e m] = [raw e (m + n)]`.
-/

noncomputable section

namespace OddMath.SKM.Summands

open CategoryTheory StringDiagrams Presentation GradedSupercategory
open CategoryTheory.Idempotents CategoryTheory.Limits

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous} {a b : UGr D Sc sy hc}

variable (a b) in
/-- The hom category before taking the additive Karoubi envelope. -/
abbrev Base := GUnderlying k (QPiEnvelope k (a ⟶ b))

/-- The formal degree shift of a 1-morphism. -/
def shifted (f : a ⟶ b) (n : ℤ) : Base a b := ⟨⟨⟨0, ⟨n, f⟩⟩⟩⟩

variable {f : a ⟶ b}

/-- A homogeneous even endomorphism, viewed between its appropriate shifts. -/
def lift {m n : ℤ} (g : f ⟶ f) (hd : g ∈ degree (R := k) f f (m - n))
    (hp : g ∈ Supercategory.parity (R := k) f f 0) : shifted f m ⟶ shifted f n :=
  ⟨⟨g, by change g ∈ degree (R := k) _ _ (0 + (m - n)); simpa using hd⟩,
    by change g ∈ Supercategory.parity (R := k) _ _ (0 + (0 + 0)); simpa using hp⟩

theorem lift_ext {m n : ℤ} {g g' : f ⟶ f} {hd hp hd' hp'} (h : g = g') :
    (lift (m := m) (n := n) g hd hp) = lift g' hd' hp' := by
  subst h; rfl

theorem lift_comp {l m n : ℤ} (g g' : f ⟶ f) (hd hp hd' hp')
    (hd'' : g ≫ g' ∈ degree (R := k) f f (l - n))
    (hp'' : g ≫ g' ∈ Supercategory.parity (R := k) f f 0) :
    lift (m := l) (n := m) g hd hp ≫ lift (m := m) (n := n) g' hd' hp' =
      lift (g ≫ g') hd'' hp'' := rfl

theorem lift_zero {m n : ℤ} (hd hp) : lift (m := m) (n := n) (0 : f ⟶ f) hd hp = 0 := rfl

theorem lift_id {m : ℤ} (hd hp) : lift (m := m) (n := m) (𝟙 f) hd hp = 𝟙 _ := rfl

/-- The underlying 2-morphism, additively. -/
def val (m n : ℤ) : (shifted f m ⟶ shifted f n) →+ (f ⟶ f) where
  toFun x := x.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_injective (m n : ℤ) : Function.Injective (val (f := f) m n) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

variable {e : f ⟶ f} (he : e ≫ e = e) (hd0 : e ∈ degree (R := k) f f 0)
  (hp0 : e ∈ Supercategory.parity (R := k) f f 0)

/-- The idempotent `e` on the shift `Q^n f`. -/
def projector (n : ℤ) : End (shifted f n) := lift e (by simpa using hd0) hp0

include he in
theorem projector_idem (n : ℤ) :
    projector hd0 hp0 n ≫ projector hd0 hp0 n = projector hd0 hp0 n :=
  (lift_comp _ _ _ _ _ _ (by rw [he]; simpa using hd0) (by rw [he]; exact hp0)).trans
    (lift_ext he)

include he in
/-- The summand `(Q^n f, e)` of the completed hom category. -/
def raw (n : ℤ) : Karoubi (Mat_ (Base a b)) where
  X := (Mat_.embedding _).obj (shifted f n)
  p := (Mat_.embedding _).map (projector hd0 hp0 n)
  idem := by rw [← Functor.map_comp, projector_idem he]

variable (f) in
/-- The unsplit 1-morphism in the completed hom category. -/
def whole : Karoubi (Mat_ (Base a b)) := (toKaroubi _).obj ((Mat_.embedding _).obj (shifted f 0))

private theorem q_projector (n : ℤ) :
    (QPiCategory.Q (R := k) (C := Base a b)).map (projector hd0 hp0 n) =
      projector hd0 hp0 (n + 1) := by
  apply Subtype.ext; apply Subtype.ext
  change 𝟙 _ ≫ (e ≫ 𝟙 _) = e
  simp only [Category.id_comp, Category.comp_id]

private theorem qinv_projector (n : ℤ) :
    (QPiCategory.Qinv (R := k) (C := Base a b)).map (projector hd0 hp0 n) =
      projector hd0 hp0 (n - 1) := by
  apply Subtype.ext; apply Subtype.ext
  change 𝟙 _ ≫ (e ≫ 𝟙 _) = e
  simp only [Category.id_comp, Category.comp_id]

private def projectorIso {C : Type*} [Category C] (V : C) (p q : End V)
    (hp : p ≫ p = p) (hq : q ≫ q = q) (h : p = q) :
    (⟨V, p, hp⟩ : Karoubi C) ≅ ⟨V, q, hq⟩ where
  hom := ⟨q, by change p ≫ q ≫ q = q; rw [h, hq, hq]⟩
  inv := ⟨q, by change q ≫ q ≫ p = q; rw [h, hq, hq]⟩
  hom_inv_id := by apply Karoubi.hom_ext; exact hq.trans h.symm
  inv_hom_id := by apply Karoubi.hom_ext; exact hq

include he in
/-- `Q` shifts the summand by one. -/
def qRawIso (n : ℤ) :
    (QPiCategory.Q (R := k) (C := Karoubi (Mat_ (Base a b)))).obj (raw he hd0 hp0 n) ≅
      raw he hd0 hp0 (n + 1) :=
  projectorIso _ _ _
    ((QPiCategory.Q (R := k) (C := Karoubi (Mat_ (Base a b)))).obj (raw he hd0 hp0 n)).idem
    (raw he hd0 hp0 (n + 1)).idem (by
      change (Mat_.embedding (Base a b)).map
        ((QPiCategory.Q (R := k)).map (projector hd0 hp0 n)) = _
      rw [q_projector]
      rfl)

include he in
/-- `Q⁻¹` shifts the summand by minus one. -/
def qinvRawIso (n : ℤ) :
    (QPiCategory.Qinv (R := k) (C := Karoubi (Mat_ (Base a b)))).obj (raw he hd0 hp0 n) ≅
      raw he hd0 hp0 (n - 1) :=
  projectorIso _ _ _
    ((QPiCategory.Qinv (R := k) (C := Karoubi (Mat_ (Base a b)))).obj (raw he hd0 hp0 n)).idem
    (raw he hd0 hp0 (n - 1)).idem (by
      change (Mat_.embedding (Base a b)).map
        ((QPiCategory.Qinv (R := k)).map (projector hd0 hp0 n)) = _
      rw [qinv_projector]
      rfl)

include he in
/-- Every integer shift acts through the Laurent-module structure on split `K₀`. -/
theorem class_raw_shift (m n : ℤ) :
    letI := K₀.moduleLaurent k (Karoubi (Mat_ (Base a b)))
    (LaurentPolynomial.T n : LaurentPolynomial Zπ) • K₀.mk (raw he hd0 hp0 m) =
      K₀.mk (raw he hd0 hp0 (m + n)) := by
  let := K₀.moduleLaurent k (Karoubi (Mat_ (Base a b)))
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by omega, LaurentPolynomial.T_add, mul_smul, ih,
      K₀.T_smul_mk, K₀.mk_eq_mk_of_iso (qRawIso he hd0 hp0 (m + n))]
    congr 2
    omega
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega,
      LaurentPolynomial.T_add, mul_smul, ih,
      K₀.T_neg_one_smul_mk, K₀.mk_eq_mk_of_iso (qinvRawIso he hd0 hp0 (m + -(n : ℤ)))]
    congr 2
    omega

include he in
/-- The same, for the `ℤ[q^±]`-module structure. -/
theorem class_raw_shift_int (m n : ℤ) :
    letI := K₀.moduleLaurentInt k (Karoubi (Mat_ (Base a b)))
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • K₀.mk (raw he hd0 hp0 m) =
      K₀.mk (raw he hd0 hp0 (m + n)) := by
  have h : AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (LaurentPolynomial.T n) =
      (LaurentPolynomial.T n : LaurentPolynomial Zπ) := by
    rw [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
    rfl
  let := K₀.moduleLaurent k (Karoubi (Mat_ (Base a b)))
  change AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (LaurentPolynomial.T n) •
    K₀.mk (raw he hd0 hp0 m) = _
  rw [h]
  exact class_raw_shift he hd0 hp0 m n

/-! ### Finite biproducts in split `K₀` -/

section Biproduct

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]

private def biproductSplitIso {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → C) (x : ι) :
    ⨁ g ≅ g x ⊞ ⨁ (fun j : {j // j ≠ x} => g j) where
  hom := biprod.lift (biproduct.π g x) (biproduct.lift fun j => biproduct.π g j.1)
  inv := biprod.desc (biproduct.ι g x) (biproduct.desc fun j => biproduct.ι g j.1)
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct.lift_desc, ← biproduct.total (f := g),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    congr 1
    exact (Finset.sum_subtype (p := fun y => y ≠ x) (Finset.univ.erase x) (fun y => by simp)
      (fun j => biproduct.π g j ≫ biproduct.ι g j)).symm
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inl_fst, biproduct.ι_π_self]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        apply biproduct.hom_ext
        intro j
        rw [Category.assoc, biproduct.lift_π, biproduct.ι_π_ne _ (Ne.symm j.2), zero_comp]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
        apply biproduct.hom_ext'
        intro j
        rw [biproduct.ι_desc_assoc, biproduct.ι_π_ne _ j.2, comp_zero]
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        apply biproduct.hom_ext'
        intro j
        apply biproduct.hom_ext
        intro j'
        rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id]
        by_cases h : j = j'
        · subst h
          rw [biproduct.ι_π_self, biproduct.ι_π_self]
        · rw [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ (fun h' => h (Subtype.ext h'))]

omit [HasFiniteBiproducts C] in
private theorem mk_isZero {Z : C} (hZ : IsZero Z) : K₀.mk Z = 0 := by
  have h := K₀.mk_biprod Z Z
  rw [K₀.mk_eq_mk_of_iso (((biprod_isZero_iff Z Z).2 ⟨hZ, hZ⟩).iso hZ)] at h
  simpa using h

private theorem mk_biproduct_aux : ∀ (n : ℕ) (ι : Type) [Fintype ι] (g : ι → C),
    Fintype.card ι = n → K₀.mk (⨁ g) = ∑ j, K₀.mk (g j) := by
  intro n
  induction n with
  | zero =>
    intro ι _ g hn
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine mk_isZero ?_
    rw [IsZero.iff_id_eq_zero, ← biproduct.total]
    simp
  | succ n ih =>
    intro ι _ g hn
    classical
    obtain ⟨x⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hcard : Fintype.card {j // j ≠ x} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hn]
      rfl
    rw [K₀.mk_eq_mk_of_iso (biproductSplitIso g x), K₀.mk_biprod, ih _ _ hcard,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    congr 1
    exact (Finset.sum_subtype (p := fun y => y ≠ x) (Finset.univ.erase x) (fun y => by simp)
      (fun j => K₀.mk (g j))).symm

/-- A finite splitting `1_W = ∑_j p_j i_j` with `i_j p_l = δ_{jl}` gives
`[W] = ∑_j [Y_j]` in split `K₀`. -/
theorem mk_of_total {ι : Type} [Fintype ι] [DecidableEq ι] {W : C} (Y : ι → C)
    (p : ∀ j, W ⟶ Y j) (i : ∀ j, Y j ⟶ W)
    (hself : ∀ j, i j ≫ p j = 𝟙 (Y j)) (hne : ∀ j l, j ≠ l → i j ≫ p l = 0)
    (htotal : ∑ j, p j ≫ i j = 𝟙 W) :
    K₀.mk W = ∑ j, K₀.mk (Y j) := by
  have e : W ≅ ⨁ Y :=
    { hom := biproduct.lift p
      inv := biproduct.desc i
      hom_inv_id := by rw [biproduct.lift_desc, htotal]
      inv_hom_id := by
        apply biproduct.hom_ext'
        intro j
        apply biproduct.hom_ext
        intro l
        rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id]
        by_cases h : j = l
        · subst h; rw [hself, biproduct.ι_π_self]
        · rw [hne j l h, biproduct.ι_π_ne _ h] }
  rw [K₀.mk_eq_mk_of_iso e]
  exact mk_biproduct_aux _ ι Y rfl

end Biproduct

/-! ### The splitting -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℤ) (σ lam : ι → (f ⟶ f))
  (hσd : ∀ j, σ j ∈ degree (R := k) f f (m j))
  (hσp : ∀ j, σ j ∈ Supercategory.parity (R := k) f f 0)
  (hld : ∀ j, lam j ∈ degree (R := k) f f (-m j))
  (hlp : ∀ j, lam j ∈ Supercategory.parity (R := k) f f 0)
  (hsum : ∑ j, lam j ≫ σ j = 𝟙 f)
  (horth : ∀ j l, σ j ≫ lam l = if j = l then e else 0)
  (hσe : ∀ j, e ≫ σ j = σ j) (hle : ∀ j, lam j ≫ e = lam j)

include he hσd hσp hld hlp hsum horth hσe hle in
/-- **The categorical splitting.** `[f] = ∑_j [Q^{m_j} (f, e)]` in split `K₀`. -/
theorem class_whole : K₀.mk (whole f) = ∑ j, K₀.mk (raw he hd0 hp0 (m j)) := by
  refine mk_of_total (W := whole f) (fun j => raw he hd0 hp0 (m j))
    (fun j => Karoubi.Hom.mk ((Mat_.embedding _).map (lift (m := 0) (n := m j) (lam j)
      (by simpa using hld j) (hlp j))) ?_)
    (fun j => Karoubi.Hom.mk ((Mat_.embedding _).map (lift (m := m j) (n := 0) (σ j)
      (by simpa using hσd j) (hσp j))) ?_) ?_ ?_ ?_
  · change 𝟙 _ ≫ _ ≫ (Mat_.embedding _).map (projector hd0 hp0 (m j)) = _
    rw [Category.id_comp, ← Functor.map_comp]
    exact congrArg _ (val_injective _ _ (hle j))
  · change (Mat_.embedding _).map (projector hd0 hp0 (m j)) ≫ _ ≫ 𝟙 _ = _
    rw [Category.comp_id, ← Functor.map_comp]
    exact congrArg _ (val_injective _ _ (hσe j))
  · intro j
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = (Mat_.embedding _).map _
    rw [← Functor.map_comp]
    refine congrArg _ (val_injective _ _ ?_)
    exact (horth j j).trans (ite_eq_left rfl)
  · intro j l h
    apply Karoubi.hom_ext
    change (Mat_.embedding (Base a b)).map _ ≫ (Mat_.embedding (Base a b)).map _ =
      (0 : (Mat_.embedding (Base a b)).obj (shifted f (m j)) ⟶
        (Mat_.embedding (Base a b)).obj (shifted f (m l)))
    rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding (Base a b))]
    exact congrArg _ (val_injective _ _ ((horth j l).trans (ite_eq_right h)))
  · apply Karoubi.hom_ext
    rw [Karoubi.sum_hom, Karoubi.id_f]
    change ∑ j, (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 𝟙 _
    simp_rw [← Functor.map_comp]
    rw [← Functor.map_sum, ← (Mat_.embedding (Base a b)).map_id]
    refine congrArg _ ?_
    apply val_injective
    rw [map_sum]
    exact hsum

end OddMath.SKM.Summands
