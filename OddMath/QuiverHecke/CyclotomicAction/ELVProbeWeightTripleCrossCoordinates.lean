/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCrossPathCoordinates

/-! # The independently whiskered OLD weight crossings in triple coordinates

Brundan–Ellis (1.9): retain the chosen prefix and suffix crossings, their
bicategorical associators, and every intermediate stored content. Each
component is compared with its prescribed evaluated append-to map.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u v w z

private theorem prefix_conjugate {C A : Type v} [Category.{w} C] [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ N₀ N₁ : C} (hM : M₀ = M₁) (hN : N₀ = N₁)
    {V W : A} (hV : V = G.obj M₀) (hW : W = G.obj N₀)
    (hV' : V = G.obj M₁) (hW' : W = G.obj N₁) (f : M₁ ⟶ N₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ f ≫ eqToHom hN.symm) ≫ eqToHom hW.symm =
      eqToHom hV' ≫ G.map f ≫ eqToHom hW'.symm := by
  cases hM
  cases hN
  cases hV
  cases hW
  cases hV'
  cases hW'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem suffix_conjugate {k : Type u} [CommRing k]
    {C A : Type v} [Category.{w} C] [Category.{z} A] [Preadditive A] [Linear k A]
    (c : k) (F G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V W : A}
    (hV : V = F.obj M₀) (hW : W = G.obj M₀)
    (hV' : V = F.obj M₁) (hW' : W = G.obj M₁)
    (f : F.obj M₀ ⟶ G.obj M₀) (f' : F.obj M₁ ⟶ G.obj M₁) (hf : HEq f f') :
    eqToHom hV ≫ (c • f) ≫ eqToHom hW.symm =
      eqToHom hV' ≫ (c • f') ≫ eqToHom hW'.symm := by
  cases hM
  have h : f = f' := eq_of_heq hf
  cases h
  rfl

private theorem dependent_apply_heq {A : Sort*} {B : A → Sort*}
    (f : ∀ a, B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem reassociated_prefix_total
    {k : Type u} [CommRing k] {A B B' C E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (F' : A ⟶ B') (G' : B' ⟶ C)
    (H : C ⟶ E) (t : F ≫ G ⟶ F' ≫ G') (M : A) :
    ((associator F G H).inv ≫ t ▷ H ≫ (associator F' G' H).hom).total M =
      H.map (t.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  change H.map (t.app 0 M) + H.map (t.app 1 M) = H.map (t.app 0 M + t.app 1 M)
  exact H.toFunctor.map_add.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
section Prefix
variable (i j l : I) (Λ : X) {a bl bj c d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj)
  (hlj : bl + D.α j = c) (hjl : bj + D.α l = c) (hd : c + D.α i = d)
local notation "El" => probeOldE D Sc m l Λ hal
local notation "Ej" => probeOldE D Sc m j Λ haj
local notation "Uj" => probeOldE D Sc m j Λ hlj
local notation "Ul" => probeOldE D Sc m l Λ hjl
local notation "Ei" => probeOldE D Sc m i Λ hd

/-- The chosen first-pair crossing with its source and target associators retained. -/
abbrev probeOldWeightCrossPrefix : El ≫ Uj ≫ Ei ⟶ Ej ≫ Ul ≫ Ei :=
  (associator El Uj Ei).inv ≫
    probeOldActionCross D Sc m Λ j l hal hlj haj hjl ▷ Ei ≫ (associator Ej Ul Ei).hom

theorem probeOldWeightCrossPrefix_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightCrossPrefix D Sc m i j l Λ hal haj hlj hjl hd).total M ε =
      (probeOldInductionComponent D Sc m i Λ hd ε).map
        ((probeOldActionCross D Sc m Λ j l hal hlj haj hjl).total M) :=
  congrFun (reassociated_prefix_total El Uj Ej Ul Ei
    (probeOldActionCross D Sc m Λ j l hal hlj haj hjl) M) ε

/-- The independent first-pair crossing uses the same two prescribed triple coordinates. -/
theorem probeOldWeightCrossPrefix_via_total (β : WeightBlocks D Λ a)
    (δl : WeightBlocks D Λ bl) (δj : WeightBlocks D Λ bj)
    (δ : WeightBlocks D Λ c) (ε : WeightBlocks D Λ d)
    (hδl : blockSucc D Λ l hal β = δl) (hδj : blockSucc D Λ j haj β = δj)
    (hδs : blockSucc D Λ j hlj δl = δ) (hδt : blockSucc D Λ l hjl δj = δ)
    (hε : blockSucc D Λ i hd δ = ε) (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightCrossPrefix D Sc m i j l Λ hal haj hlj hjl hd).total M ε =
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hd β δl δ ε hδl hδs hε M) ≫
        (probeOldBlockIndTo D Sc m i Λ hd δ ε hε).map
          ((if j = l then (-1 : k) else 1) • probeAppendToCrossComponent D Sc m β.1.toList l j
            (probeOldBlockTarget_perm D j Λ haj β δj hδj)
            (probeOldBlockTarget_perm D l Λ hal β δl hδl)
            (probeOldBlockTarget_perm D l Λ hjl δj δ hδt)
            (probeOldBlockTarget_perm D j Λ hlj δl δ hδs) (M β)) ≫
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m i l j Λ haj hjl hd β δj δ ε hδj hδt hε M).symm := by
  rw [probeOldWeightCrossPrefix_total, probeOldInductionComponent_map_of D Sc m i Λ hd δ ε hε,
    probeOldActionCross_via_total D Sc m j l Λ hal hlj haj hjl β δl δj δ hδl hδj hδs hδt]
  exact prefix_conjugate (probeOldBlockIndTo D Sc m i Λ hd δ ε hε).toFunctor
    (probeOldWeightPairVia_obj_eq D Sc m j l Λ hal hlj β δl δ hδl hδs M)
    (probeOldWeightPairVia_obj_eq D Sc m l j Λ haj hjl β δj δ hδj hδt M)
    (probeOldInductionComponent_obj_of D Sc m i Λ hd δ ε hε ((El ≫ Uj).obj M))
    (probeOldInductionComponent_obj_of D Sc m i Λ hd δ ε hε ((Ej ≫ Ul).obj M))
    (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hd β δl δ ε hδl hδs hε M)
    (probeOldWeightTripleVia_obj_eq D Sc m i l j Λ haj hjl hd β δj δ ε hδj hδt hε M) _
end Prefix

section Suffix
variable (i j l : I) (Λ : X) {a b cj ci d : X}
  (hal : a + D.α l = b) (hlj : b + D.α j = cj) (hli : b + D.α i = ci)
  (hji : cj + D.α i = d) (hij : ci + D.α j = d)
local notation "El" => probeOldE D Sc m l Λ hal
local notation "Ej" => probeOldE D Sc m j Λ hlj
local notation "Ei" => probeOldE D Sc m i Λ hli
local notation "Ui" => probeOldE D Sc m i Λ hji
local notation "Uj" => probeOldE D Sc m j Λ hij

/-- The chosen last-pair crossing after the independently chosen first induction. -/
abbrev probeOldWeightCrossSuffix : El ≫ Ej ≫ Ui ⟶ El ≫ Ei ≫ Uj :=
  El ◁ probeOldActionCross D Sc m Λ i j hlj hji hli hij

theorem probeOldWeightCrossSuffix_total (M : ProbeOldWeightProduct D Sc m Λ a)
    (ε : WeightBlocks D Λ d) :
    (probeOldWeightCrossSuffix D Sc m i j l Λ hal hlj hli hji hij).total M ε =
      (probeOldActionCross D Sc m Λ i j hlj hji hli hij).total ((El).obj M) ε := rfl

/-- The independent last-pair crossing uses the same two prescribed triple coordinates. -/
theorem probeOldWeightCrossSuffix_via_total (β : WeightBlocks D Λ a)
    (δl : WeightBlocks D Λ b) (δj : WeightBlocks D Λ cj) (δi : WeightBlocks D Λ ci)
    (ε : WeightBlocks D Λ d) (hδl : blockSucc D Λ l hal β = δl)
    (hδj : blockSucc D Λ j hlj δl = δj) (hδi : blockSucc D Λ i hli δl = δi)
    (hεs : blockSucc D Λ i hji δj = ε) (hεt : blockSucc D Λ j hij δi = ε)
    (M : ProbeOldWeightProduct D Sc m Λ a) :
    (probeOldWeightCrossSuffix D Sc m i j l Λ hal hlj hli hji hij).total M ε =
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hji β δl δj ε hδl hδj hεs M) ≫
        ((if i = j then (-1 : k) else 1) • probeAppendToCrossComponent D Sc m δl.1.toList j i
          (probeOldBlockTarget_perm D i Λ hli δl δi hδi)
          (probeOldBlockTarget_perm D j Λ hlj δl δj hδj)
          (probeOldBlockTarget_perm D j Λ hij δi ε hεt)
          (probeOldBlockTarget_perm D i Λ hji δj ε hεs)
          ((probeOldBlockIndTo D Sc m l Λ hal β δl hδl).obj (M β))) ≫
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc m j i l Λ hal hli hij β δl δi ε hδl hδi hεt M).symm := by
  rw [probeOldWeightCrossSuffix_total,
    probeOldActionCross_via_total D Sc m i j Λ hlj hji hli hij δl δj δi ε hδj hδi hεs hεt]
  apply suffix_conjugate (if i = j then (-1 : k) else 1)
    (probeOldBlockPairVia D Sc m i j Λ hlj hji δl δj ε hδj hεs).toFunctor
    (probeOldBlockPairVia D Sc m j i Λ hli hij δl δi ε hδi hεt).toFunctor
    (probeOldInductionComponent_obj_of D Sc m l Λ hal β δl hδl M)
    (probeOldWeightPairVia_obj_eq D Sc m i j Λ hlj hji δl δj ε hδj hεs ((El).obj M))
    (probeOldWeightPairVia_obj_eq D Sc m j i Λ hli hij δl δi ε hδi hεt ((El).obj M))
    (probeOldWeightTripleVia_obj_eq D Sc m i j l Λ hal hlj hji β δl δj ε hδl hδj hεs M)
    (probeOldWeightTripleVia_obj_eq D Sc m j i l Λ hal hli hij β δl δi ε hδl hδi hεt M)
  exact dependent_apply_heq
    (probeAppendToCrossComponent D Sc m δl.1.toList j i
      (probeOldBlockTarget_perm D i Λ hli δl δi hδi)
      (probeOldBlockTarget_perm D j Λ hlj δl δj hδj)
      (probeOldBlockTarget_perm D j Λ hij δi ε hεt)
      (probeOldBlockTarget_perm D i Λ hji δj ε hεs))
    (probeOldInductionComponent_obj_of D Sc m l Λ hal β δl hδl M)
end Suffix
end OddMath.QuiverHecke
