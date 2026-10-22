/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KarOf
import OddMath.SKM.IdempotentSummands

/-!
# Horizontal composites of summands in `Kar B`

For a bicategory `B` with preadditive hom categories, a 1-morphism `f` with an idempotent
`e : f ⟶ f` gives the summand `(f, e)` of the additive Karoubi envelope `Kar B`
(Brundan–Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.5 and the end of §6). The
horizontal composite of `(f, e)` and `(g, e')` is the summand `(f ≫ g, e ⋆ e')` cut out by the
horizontal composite of the idempotents (`Kar.summandCompIso`), so in the Grothendieck ring
`[(g, e')] · [(f, e)] = [(f ≫ g, e ⋆ e')]` (`K₀Ring.mk_summand_mul_mk_summand`).

For a graded 2-supercategory `𝔄` and homogeneous even idempotents `e`, `e'` of degree zero, the
summands `Q^n Π^p (f, e)` of `GSKAR(𝔄)` (`OddMath.SKM.Summands.raw`) multiply by adding the
shifts: `[Q^{n'} Π^{p'} (g, e')] · [Q^n Π^p (f, e)] = [Q^{n+n'} Π^{p+p'} (f ≫ g, e ⋆ e')]`
(`OddMath.SKM.Summands.mk_raw_mul_mk_raw`). The sign of Definition 6.10 on the horizontal
composite of the two idempotents is `1`, since both are even.

This is how products of divided powers are computed in `K₀(𝔘̇_{q,π}(𝔤))` (Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 11.6).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Idempotents

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] {a b c : B}

namespace Kar

omit [∀ a b : B, Preadditive (a ⟶ b)] [PreadditiveBicategory B] in
theorem hcomp₂_idem {f : a ⟶ b} {g : b ⟶ c} {e : f ⟶ f} {e' : g ⟶ g} (he : e ≫ e = e)
    (he' : e' ≫ e' = e') : hcomp₂ e e' ≫ hcomp₂ e e' = hcomp₂ e e' := by
  rw [← hcomp₂_comp, he, he']

/-- The summand `(f, e)` of `Kar B`. -/
def summand (f : a ⟶ b) (e : f ⟶ f) (he : e ≫ e = e) : mkObj a ⟶ mkObj b :=
  ⟨MatBicat.single f, (Mat_.embedding (a ⟶ b)).map e, by rw [← Functor.map_comp, he]⟩

omit [PreadditiveBicategory B] in
theorem permMat_punitProd_apply {f : a ⟶ c} (x : PUnit.{1} × PUnit.{1}) (y : PUnit.{1}) :
    Mat_.permMat (D := a ⟶ c) (X := fun _ => f) (Y := fun _ => f) (Equiv.punitProd PUnit)
      (fun _ => 𝟙 f) x y = 𝟙 f := by
  cases y
  exact Mat_.permMat_apply_self (D := a ⟶ c) (X := fun _ => f) (Y := fun _ => f)
    (Equiv.punitProd PUnit) (fun _ => 𝟙 f) x

set_option backward.isDefEq.respectTransparency false in
theorem summand_comp_comm (f : a ⟶ b) (g : b ⟶ c) {e : f ⟶ f} {e' : g ⟶ g} (he : e ≫ e = e)
    (he' : e' ≫ e' = e') :
    (summand f e he ≫ summand g e' he').p ≫ (MatBicat.singleCompIso (Iso.refl (f ≫ g))).hom =
      (MatBicat.singleCompIso (Iso.refl (f ≫ g))).hom ≫
        (summand (f ≫ g) (hcomp₂ e e') (hcomp₂_idem he he')).p := by
  rw [KarBicat.comp_p, hcomp₂, MatBicat.whiskerLeft_eq, MatBicat.whiskerRight_eq,
    ← MatBicat.hcomp_comp, Category.comp_id, Category.id_comp]
  let _ : Unique ((summand f e he ≫ summand g e' he').X.ι) :=
    ⟨⟨(PUnit.unit, PUnit.unit)⟩, fun _ => rfl⟩
  let _ : Unique ((summand (f ≫ g) (hcomp₂ e e') (hcomp₂_idem he he')).X.ι) :=
    inferInstanceAs (Unique PUnit)
  apply CategoryTheory.Mat_.hom_ext
  intro x y
  rw [CategoryTheory.Mat_.comp_apply, CategoryTheory.Mat_.comp_apply, Fintype.sum_unique,
    Fintype.sum_unique]
  simp [summand, MatBicat.singleCompIso_hom, Mat_.embedding, MatBicat.hcomp_apply,
    permMat_punitProd_apply]

theorem summand_congr (f : a ⟶ b) {e₁ e₂ : f ⟶ f} (h : e₁ = e₂) (h₁ : e₁ ≫ e₁ = e₁)
    (h₂ : e₂ ≫ e₂ = e₂) : summand f e₁ h₁ = summand f e₂ h₂ := by
  subst h; rfl

/-- **The horizontal composite of two summands**: `(f, e) ≫ (g, e') ≅ (f ≫ g, e ⋆ e')`. -/
def summandCompIso (f : a ⟶ b) (g : b ⟶ c) {e : f ⟶ f} {e' : g ⟶ g} (he : e ≫ e = e)
    (he' : e' ≫ e' = e') :
    summand f e he ≫ summand g e' he' ≅ summand (f ≫ g) (hcomp₂ e e') (hcomp₂_idem he he') :=
  Karoubi.mkIso (MatBicat.singleCompIso (Iso.refl (f ≫ g))) (summand_comp_comm f g he he')

end Kar

namespace K₀Ring

/-- **Products of summands**: `[(g, e')] · [(f, e)] = [(f ≫ g, e ⋆ e')]`. -/
theorem mk_summand_mul_mk_summand (f : a ⟶ b) (g : b ⟶ c) {e : f ⟶ f} {e' : g ⟶ g}
    (he : e ≫ e = e) (he' : e' ≫ e' = e') :
    mk (Kar.summand g e' he') * mk (Kar.summand f e he) =
      mk (Kar.summand (f ≫ g) (hcomp₂ e e') (Kar.hcomp₂_idem he he')) := by
  rw [mk_mul_mk]
  exact mk_eq_mk_of_iso (Kar.summandCompIso f g he he')

end K₀Ring

end StringDiagrams

/-! ### Shifted summands in `GSKAR(𝔄)` -/

namespace OddMath.SKM.Summands

open CategoryTheory StringDiagrams GradedSupercategory Supercategory

universe w₂ w₃ v₂ u₂

variable {k : Type w₃} [CommRing k] {B : Type u₂} [BicategoryStruct.{w₂, v₂} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [∀ a b : B, GradedSupercategory k (a ⟶ b)]
  [TwoSupercategory k B] [GradedTwoSupercategory k B]

/-- An object of `B` in `𝔄̲_{q,π}`; its hom categories are the categories `Base k (a ⟶ b)`. -/
abbrev pt (a : B) : GUnderlying2 k (QPiTwoEnvelope k B) := ⟨⟨⟨⟨a⟩⟩⟩⟩

/-- The shifted 1-morphism `Q^n Π^p f` of `𝔄_{q,π}`. -/
abbrev sh1 {a b : B} (f : a ⟶ b) (n : ℤ) (p : ZMod 2) :
    (⟨⟨a⟩⟩ : QPiTwoEnvelope k B) ⟶ ⟨⟨b⟩⟩ := (shifted (k := k) f n p).obj.obj

variable {a b c : B} {f : a ⟶ b} {g : b ⟶ c} {e : f ⟶ f} {e' : g ⟶ g}

omit [∀ a b : B, GradedSupercategory k (a ⟶ b)] [GradedTwoSupercategory k B] in
theorem hcomp_idem (he : e ≫ e = e) (he' : e' ≫ e' = e')
    (hp : e ∈ parity (R := k) f f 0) (hp' : e' ∈ parity (R := k) g g 0) :
    TwoSupercategory.hcomp e e' ≫ TwoSupercategory.hcomp e e' = TwoSupercategory.hcomp e e' := by
  rw [TwoSupercategory.hcomp_comp_hcomp (R := k) e e e' e' (pu := 0) (py := 0) hp hp',
    koszulSign_zero_left, one_smul, he, he']

theorem hcomp_mem_degree_zero (hd0 : e ∈ degree (R := k) f f 0)
    (hd0' : e' ∈ degree (R := k) g g 0) :
    TwoSupercategory.hcomp e e' ∈ degree (R := k) (f ≫ g) (f ≫ g) 0 := by
  simpa using GradedTwoSupercategory.hcomp_mem_degree (R := k) hd0 hd0'

omit [∀ a b : B, GradedSupercategory k (a ⟶ b)] [GradedTwoSupercategory k B] in
theorem hcomp_mem_parity_zero (hp0 : e ∈ parity (R := k) f f 0)
    (hp0' : e' ∈ parity (R := k) g g 0) :
    TwoSupercategory.hcomp e e' ∈ parity (R := k) (f ≫ g) (f ≫ g) 0 := by
  simpa using TwoSupercategory.hcomp_mem (R := k) hp0 hp0'

/-- The horizontal composite of the shifted idempotents is the shifted horizontal composite: the
sign `(-1)^{b|x| + |y|c + bc + ab}` of Definition 6.10 is `1` on even endomorphisms. -/
theorem hcomp₂_projector (hd0 : e ∈ degree (R := k) f f 0) (hp0 : e ∈ parity (R := k) f f 0)
    (hd0' : e' ∈ degree (R := k) g g 0) (hp0' : e' ∈ parity (R := k) g g 0)
    (n n' : ℤ) (p p' : ZMod 2) :
    hcomp₂ (B := GUnderlying2 k (QPiTwoEnvelope k B)) (a := pt a) (b := pt b) (c := pt c)
      (f := shifted (k := k) f n p) (h := shifted (k := k) g n' p')
      (projector hd0 hp0 n p) (projector hd0' hp0' n' p') =
    projector (hcomp_mem_degree_zero hd0 hd0') (hcomp_mem_parity_zero hp0 hp0') (n + n')
      (p + p') := by
  apply Subtype.ext; apply Subtype.ext
  change TwoSupercategory.hcomp (B := QPiTwoEnvelope k B) (a := ⟨⟨a⟩⟩) (b := ⟨⟨b⟩⟩)
    (c := ⟨⟨c⟩⟩) (f := sh1 f n p) (g := sh1 f n p) (h := sh1 g n' p') (i := sh1 g n' p')
    (projector hd0 hp0 n p).1.1 (projector hd0' hp0' n' p').1.1 = _
  apply Envelope.hom_ext; apply QEnvelope.hom_ext
  refine (QPiTwoEnvelope.toHom_hcomp (R := k) (B := B) (f := sh1 f n p) (h := sh1 f n p)
    (g := sh1 g n' p') (k := sh1 g n' p') (x := (projector hd0 hp0 n p).1.1)
    (y := (projector hd0' hp0' n' p').1.1) (px := 0) (py := 0) hp0 hp0').trans ?_
  rw [show (sh1 (k := k) g n' p').par * 0 + 0 * (sh1 (k := k) f n p).par +
      (sh1 (k := k) g n' p').par * (sh1 (k := k) f n p).par +
      (sh1 (k := k) f n p).par * (sh1 (k := k) g n' p').par = 0 by
        rw [mul_zero, zero_mul, zero_add, zero_add, mul_comm (sh1 (k := k) f n p).par,
          zmod2_add_self], sign_zero, one_smul]
  rfl

/-- **Products of shifted summands in `K₀(GSKAR(𝔄))`**:
`[Q^{n'} Π^{p'} (g, e')] · [Q^n Π^p (f, e)] = [Q^{n+n'} Π^{p+p'} (f ≫ g, e ⋆ e')]`, in the
multiplication order of `K₀Ring` (horizontal composites in diagrammatic order). -/
theorem mk_raw_mul_mk_raw (he : e ≫ e = e) (hd0 : e ∈ degree (R := k) f f 0)
    (hp0 : e ∈ parity (R := k) f f 0) (he' : e' ≫ e' = e') (hd0' : e' ∈ degree (R := k) g g 0)
    (hp0' : e' ∈ parity (R := k) g g 0) (n n' : ℤ) (p p' : ZMod 2) :
    K₀Ring.mk (B := GSKAR k B) (a := GSKAR.mkObj k B b) (b := GSKAR.mkObj k B c)
        (raw he' hd0' hp0' n' p') *
      K₀Ring.mk (B := GSKAR k B) (a := GSKAR.mkObj k B a) (b := GSKAR.mkObj k B b)
        (raw he hd0 hp0 n p) =
    K₀Ring.mk (B := GSKAR k B) (a := GSKAR.mkObj k B a) (b := GSKAR.mkObj k B c)
      (raw (hcomp_idem he he' hp0 hp0') (hcomp_mem_degree_zero hd0 hd0')
        (hcomp_mem_parity_zero hp0 hp0') (n + n') (p + p')) := by
  have h := K₀Ring.mk_summand_mul_mk_summand (a := pt (k := k) a) (b := pt (k := k) b)
    (c := pt (k := k) c) (shifted (k := k) f n p) (shifted (k := k) g n' p')
    (projector_idem he hd0 hp0 n p) (projector_idem he' hd0' hp0' n' p')
  rw [Kar.summand_congr _ (hcomp₂_projector hd0 hp0 hd0' hp0' n n' p p') _
    (projector_idem (hcomp_idem he he' hp0 hp0') _ _ _ _)] at h
  exact h

end OddMath.SKM.Summands
