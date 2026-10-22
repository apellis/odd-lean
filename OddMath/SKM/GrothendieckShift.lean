/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianK0
import StringDiagrams.Super.K0Ring
import StringDiagrams.Super.KarBicategory

/-!
# The grading shift of the Grothendieck ring is the entrywise shift

Brundan–Ellis, arXiv:1701.04133v2, end of §6 and §11 (the Laurentian input of Theorem 11.7).
The Grothendieck ring `K₀(GSKAR(𝔄))` of a graded 2-supercategory is a `ℤ[q, q⁻¹, π]`-module with
`q` acting on `1_μ K₀ 1_λ` by `[F] ↦ [F q_μ]` (`StringDiagrams.K₀Ring.moduleLaurent`, through the
`(Q, Π)`-structure `- ≫ q_μ` of each hom category). Each hom category is also the graded super
Karoubi envelope `GSKar(Hom_𝔄(λ, μ))`, whose own grading shift `Q` acts entrywise on matrices of
shifted 1-morphisms. BE2 identifies the two; here this is proved.

* `rightQIso`: `f ≫ q_μ ≅ Q f` for a shifted 1-morphism `f`, from the right unitor of `𝔄`,
  natural in `f` (`rightQIso_naturality`).
* `rightShiftIso`: the same entrywise on matrices; `karRightQIso` on idempotents.
* `qEnd_eq`, `laurentEnd_int_eq`: the two actions of `ℤ[q, q⁻¹]` on `K₀(Hom(λ, μ))` agree.
* `SKM.UDot.int_smul_eq_zero`: in the completed super Kac–Moody 2-category the Grothendieck
  ring has no `ℤ[q, q⁻¹]`-torsion, by the Laurent bases of `SKM.UDot.k0_free_laurentInt`. This is
  the faithfulness of rational localization used in the existence part of Theorem 11.7.

The first part is stated for every graded 2-supercategory; it belongs with the generic
Grothendieck ring construction.
-/

noncomputable section
namespace OddMath.GrothendieckShift
open CategoryTheory StringDiagrams
open CategoryTheory.Idempotents Supercategory GradedSupercategory

universe w v u w₁
variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

section Karoubi

variable {D : Type*} [Category D]

/-- The inverse of an isomorphism commuting with the idempotents commutes with them. -/
theorem karoubi_inv_comm {P Q : Karoubi D} (φ : P.X ≅ Q.X) (h : P.p ≫ φ.hom = φ.hom ≫ Q.p) :
    Q.p ≫ φ.inv = φ.inv ≫ P.p := by
  rw [← cancel_epi φ.hom, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- An isomorphism of underlying objects commuting with the idempotents is an isomorphism in
the Karoubi envelope. -/
def karoubiIsoOfComm {P Q : Karoubi D} (φ : P.X ≅ Q.X) (h : P.p ≫ φ.hom = φ.hom ≫ Q.p) : P ≅ Q where
  hom := ⟨P.p ≫ φ.hom, by
    rw [Category.assoc, h.symm]
    simp only [← Category.assoc, P.idem]⟩
  inv := ⟨Q.p ≫ φ.inv, by
    rw [Category.assoc, (karoubi_inv_comm φ h).symm]
    simp only [← Category.assoc, Q.idem]⟩
  hom_inv_id := by
    apply Karoubi.hom_ext
    rw [Karoubi.comp_f, Karoubi.id_f, Category.assoc, ← Category.assoc φ.hom, ← h,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, P.idem]
  inv_hom_id := by
    apply Karoubi.hom_ext
    rw [Karoubi.comp_f, Karoubi.id_f, Category.assoc, ← Category.assoc φ.inv,
      ← karoubi_inv_comm φ h,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Q.idem]

end Karoubi

section MatBicat
open Bicategory StringDiagrams.Mat_ StringDiagrams.MatBicat

section RightShift

variable {C : Type*} [Bicategory C] [∀ a b : C, Preadditive (a ⟶ b)] [PreadditiveBicategory C]
  {a b : MatBicat C} {q : b.obj ⟶ b.obj} {F : (a.obj ⟶ b.obj) ⥤ (a.obj ⟶ b.obj)} [F.Additive]
  (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ F.obj f)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `M ≫ q ≅ F M` of the additive envelope determined entrywise by
isomorphisms `f ≫ q ≅ F f`. -/
@[simps]
def rightShiftIso (M : a ⟶ b) : M ≫ single q ≅ F.mapMat_.obj M where
  hom := permMat (Equiv.prodPUnit M.ι) fun x => (e (M.X x.1)).hom
  inv := permMat (X := fun i => F.obj (M.X i)) (Y := fun x : M.ι × PUnit => M.X x.1 ≫ q)
    (Equiv.prodPUnit M.ι).symm fun i => (e (M.X i)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

set_option backward.isDefEq.respectTransparency false in
theorem rightShiftIso_naturality
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ F.map η = η ▷ q ≫ (e g).hom)
    {M N : a ⟶ b} (η : M ⟶ N) :
    (rightShiftIso e M).hom ≫ F.mapMat_.map η = η ▷ single q ≫ (rightShiftIso e N).hom := by
  refine hom_ext_equiv (Equiv.prodPUnit N.ι) fun m i => ?_
  rw [rightShiftIso_hom, rightShiftIso_hom]
  refine (permMat_comp_apply (X := fun x : M.ι × PUnit => M.X x.1 ≫ q)
    (Y := fun i => F.obj (M.X i)) (Equiv.prodPUnit M.ι)
    (fun x => (e (M.X x.1)).hom) (F.mapMat_.map η) m _).trans ?_
  refine Eq.trans ?_ (comp_permMat_apply (X := fun x : N.ι × PUnit => N.X x.1 ≫ q)
    (Y := fun i => F.obj (N.X i)) (Equiv.prodPUnit N.ι)
    (fun x => (e (N.X x.1)).hom) (η ▷ single q) m i).symm
  obtain ⟨m, ⟨⟩⟩ := m
  obtain ⟨i, ⟨⟩⟩ := i
  rw [whiskerRight_eq, hcomp_apply]
  change (e (M.X m)).hom ≫ F.map (η m i) =
    hcomp₂ (η m i) ((𝟙 (single q)) PUnit.unit PUnit.unit) ≫ (e (N.X i)).hom
  rw [id_apply_self]
  simp only [hcomp₂, Bicategory.whiskerLeft_id, Category.comp_id]
  exact he (η m i)

end RightShift
end MatBicat

section GSKAR

variable {a b : GUnderlying2 R (QPiTwoEnvelope R B)}

variable (R) in
/-- The hom category `a ⟶ b` of the underlying 2-category of `𝔄_{q,π}`, as the underlying category
of the `(Q, Π)`-envelope of a hom category of `𝔄`, with its entrywise grading shift. -/
abbrev BaseHom (a b : GUnderlying2 R (QPiTwoEnvelope R B)) :=
  GUnderlying R (QPiEnvelope R (a.obj.as.as.as ⟶ b.obj.as.as.as))

open QPiEnvelope in
/-- The base isomorphism `f ≫ q ≅ Q f`, from the right unitor of `B`. -/
def rightQIso (f : a ⟶ b) :
    f ≫ QPiTwoCategory.q (R := R) b ≅
      (QPiCategory.Q (R := R) (C := BaseHom R a b)).obj f :=
  GUnderlying.isoU (R := R)
    (Envelope.isoOfIso (QEnvelope.isoOfIso (BicategoryStruct.rightUnitor f.obj.obj.obj.obj)))
    (by
      have h := QPiEnvelope.ofHom_mem (R := R)
        (X := (f ≫ QPiTwoCategory.q (R := R) b).obj.obj)
        (Y := ((QPiCategory.Q (R := R) (C := BaseHom R a b)).obj f).obj.obj)
        (TwoSupercategory.rightUnitor_hom_mem (R := R) f.obj.obj.obj.obj)
      have e : (0 : ZMod 2) + (f.obj.obj.par + 0) + f.obj.obj.par = 0 := by
        rw [zero_add, add_zero, zmod2_add_self]
      change _ ∈ parity _ _ (0 + (f.obj.obj.par + 0) + f.obj.obj.par) at h
      rw [e] at h
      exact h)
    (by
      have h := QPiEnvelope.ofHom_mem_degree (R := R)
        (X := (f ≫ QPiTwoCategory.q (R := R) b).obj.obj)
        (Y := ((QPiCategory.Q (R := R) (C := BaseHom R a b)).obj f).obj.obj)
        (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) f.obj.obj.obj.obj)
      have e : (0 : ℤ) + (f.obj.obj.obj.shift + 1) - (f.obj.obj.obj.shift + 1) = 0 := by ring
      change _ ∈ degree _ _ (0 + (f.obj.obj.obj.shift + 1) - (f.obj.obj.obj.shift + 1)) at h
      rw [e] at h
      exact h)

theorem rightQIso_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    (rightQIso f).hom ≫ (QPiCategory.Q (R := R) (C := BaseHom R a b)).map η =
      Bicategory.whiskerRight η (QPiTwoCategory.q (R := R) b) ≫ (rightQIso g).hom := by
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  have h1 : Envelope.toHom (Bicategory.whiskerRight η (QPiTwoCategory.q (R := R) b)).1.1 =
      BicategoryStruct.whiskerRight (Envelope.toHom η.1.1)
        (QPiTwoEnvelope.q (R := R) b.obj.as).obj :=
    TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl
  change (BicategoryStruct.rightUnitor f.obj.obj.obj.obj).hom ≫
      (𝟙 _ ≫ QPiEnvelope.toHom η.1.1 ≫ 𝟙 _) =
    QEnvelope.toHom (Envelope.toHom (Bicategory.whiskerRight η (QPiTwoCategory.q (R := R) b)).1.1) ≫
      (BicategoryStruct.rightUnitor g.obj.obj.obj.obj).hom
  rw [h1]
  change _ = BicategoryStruct.whiskerRight (QPiEnvelope.toHom η.1.1) (𝟙 b.obj.as.as.as) ≫ _
  rw [TwoSupercategory.whiskerRight_id (R := R)]
  simp only [Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id]

variable {x y : GSKAR R B}

variable (R) in
/-- The hom category `x ⟶ y` of `GSKAR(𝔄)` as `GSKar(Hom_𝔄(λ, μ))`, with its entrywise grading
shift. -/
abbrev HomKar (x y : GSKAR R B) := GSKar R (x.obj.obj.obj.as.as.as ⟶ y.obj.obj.obj.as.as.as)

set_option backward.isDefEq.respectTransparency false in
/-- `P ≫ q_μ ≅ Q P` in the hom categories of `GSKAR(𝔄)`: whiskering by `q_μ` agrees with the
entrywise grading shift of `GSKar(Hom_𝔄(λ, μ))`. -/
def karRightQIso (P : x ⟶ y) :
    P ≫ QPiTwoCategory.q (R := R) y ≅
      (QPiCategory.Q (R := R) (C := HomKar R x y)).obj P :=
  karoubiIsoOfComm (rightShiftIso (rightQIso (a := x.obj.obj) (b := y.obj.obj)) P.X)
    (by
      have h := rightShiftIso_naturality (rightQIso (a := x.obj.obj) (b := y.obj.obj))
        (fun η => rightQIso_naturality η) P.p
      change hcomp₂ P.p (𝟙 _) ≫ _ = _
      erw [h]
      rw [hcomp₂, Bicategory.whiskerLeft_id, Category.comp_id]
      rfl)

variable (x y) in
/-- On each summand `K₀(Hom(λ, μ))`, the grading shift of the `(Q, Π)`-2-category `GSKAR(𝔄)`
(whiskering by `q_μ`) and the entrywise grading shift of `GSKar(Hom_𝔄(λ, μ))` induce the same
endomorphism. -/
theorem qEnd_eq : K₀.qEnd R (x ⟶ y) =
    K₀.qEnd R (HomKar R x y) := by
  apply K₀.hom_ext
  intro P
  exact K₀.mk_eq_mk_of_iso (karRightQIso P)

variable (x y) in
theorem qUnit_eq : K₀.qUnit R (x ⟶ y) =
    K₀.qUnit R (HomKar R x y) :=
  Units.ext (qEnd_eq x y)

open LaurentPolynomial in
variable (x y) in
/-- The two Laurent actions on `K₀(Hom(λ, μ))` agree on `T n`. -/
theorem laurentEnd_T_eq (n : ℤ) : K₀.laurentEnd R (x ⟶ y) (T n) =
    K₀.laurentEnd R (HomKar R x y) (T n) := by
  exact (K₀.laurentEnd_T _ _ n).trans ((congrArg
    (fun u => ((u ^ n : (AddMonoid.End (K₀ (x ⟶ y)))ˣ) :
    AddMonoid.End (K₀ (x ⟶ y)))) (qUnit_eq x y)).trans (K₀.laurentEnd_T _ _ n).symm)

open LaurentPolynomial in
private theorem map_C_mul_T {M : Type*} [Ring M] (φ : LaurentPolynomial Zπ →+* M) (a : ℤ) (n : ℤ) :
    φ (AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (C a * T n)) = (a : M) * φ (T n) := by
  have hT : AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (T n : LaurentPolynomial ℤ) =
      T n := by
    rw [T, AddMonoidAlgebra.mapRingHom_single, map_one]; rfl
  rw [show (C a : LaurentPolynomial ℤ) = (a : LaurentPolynomial ℤ) from map_intCast C a, map_mul,
    map_intCast, map_mul, map_intCast, hT]

open LaurentPolynomial in
variable (x y) in
/-- The two Laurent actions on `K₀(Hom(λ, μ))` agree on `ℤ[q, q⁻¹]`. -/
theorem laurentEnd_int_eq (p : LaurentPolynomial ℤ) :
    K₀.laurentEnd R (x ⟶ y) (AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) p) =
    K₀.laurentEnd R (HomKar R x y)
      (AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' =>
    rw [map_add]
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hp hp').trans (map_add _ _ _).symm)
  | C_mul_T n a =>
    exact (map_C_mul_T _ a n).trans ((congrArg (fun φ => (a : AddMonoid.End (K₀ (x ⟶ y))) * φ)
      (laurentEnd_T_eq x y n)).trans (map_C_mul_T _ a n).symm)

end GSKAR

end OddMath.GrothendieckShift

namespace OddMath.SKM
open CategoryTheory StringDiagrams LaurentPolynomial

universe u' v' w'
variable {I : Type u'} {X : Type v'} [AddCommGroup X] {D : Datum I X}
  {k : Type w'} [Field k] {Sc : Scalars D k} (sy : Symmetrizer D)
  (cs : CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)

include cs hf in
/-- **The Grothendieck ring has no `ℤ[q, q⁻¹]`-torsion.** In the completed super Kac–Moody
2-category, a nonzero `p ∈ ℤ[q, q⁻¹]` acts injectively on `K₀(U̇)` with its `ℤ[q, q⁻¹, π]`-module
structure of BE2 §6. -/
theorem UDot.int_smul_eq_zero (p : LaurentPolynomial ℤ) (hp : p ≠ 0)
    (x : K₀Ring (UDot D Sc sy hc))
    (h : (letI := GSKAR.moduleLaurent k (UGr D Sc sy hc)
      AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) p • x) = 0) : x = 0 := by
  apply DirectSum.ext
  rintro ⟨⟨⟨⟨⟨⟨⟨a⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨b⟩⟩⟩⟩⟩⟩⟩
  have h' := congrArg
    (fun y : K₀Ring (UDot D Sc sy hc) => y (GSKAR.mkObj k _ a, GSKAR.mkObj k _ b)) h
  change K₀Ring.laurentEnd k _ x _ = 0 at h'
  rw [K₀Ring.laurentEnd_apply, GrothendieckShift.laurentEnd_int_eq] at h'
  let := K₀.moduleLaurentInt k (GSKAR.mkObj k (UGr D Sc sy hc) a ⟶ GSKAR.mkObj k (UGr D Sc sy hc) b)
  have := UDot.k0_free_laurentInt sy cs hc hf a b
  have h'' : p • x (GSKAR.mkObj k _ a, GSKAR.mkObj k _ b) = 0 := h'
  exact (smul_eq_zero.mp h'').resolve_left hp

end OddMath.SKM
