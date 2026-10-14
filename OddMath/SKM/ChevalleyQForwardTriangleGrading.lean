/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardTriangle

/-!
# Grading of the first triangle of `ω_q`

Both modifications of `chevalleyQForwardTriangleIso` are even of degree zero.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
  BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "B" => TwoSOp k A
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "O" a:max => (⟨a⟩ : A)

theorem qForwardUnitComparison_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qForwardUnitComparison p).hom ∈ parity (R := k) _ _ 0 ∧
      (qForwardUnitComparison p).hom ∈ degree (R := k) _ _ 0 := by
  subst a'
  refine ⟨inv_mem ((F).mapId (O a)) ((F).mapId_hom_mem (O a)), ?_⟩
  change ((F).mapId (O a)).inv ∈
    degree (R := k) (C := (F).obj (O a) ⟶ (F).obj (O a)) _ _ 0
  simpa only [neg_zero] using inv_mem_degree (C := (F).obj (O a) ⟶ (F).obj (O a))
    ((F).mapId (O a)) (chevalleyQTwo_isGraded.mapId_hom_mem_degree (O a))

theorem qTriangleIsoOfRaw_homogeneous {S T : TwoSuperfunctor k A B} (θ ψ : TwoNatTrans S T)
    (U V : ∀ a, S.obj a ⟶ T.obj a)
    (x : ∀ {a b : A} (f : a ⟶ b), S.map f ≫ U b ⟶ U a ≫ T.map f)
    (y : ∀ {a b : A} (f : a ⟶ b), S.map f ≫ V b ⟶ V a ≫ T.map f)
    (hU : θ.X = U) (hV : ψ.X = V)
    (hx : ∀ {a b : A} (f : a ⟶ b), HEq (θ.x f) (x f))
    (hy : ∀ {a b : A} (f : a ⟶ b), HEq (ψ.x f) (y f))
    (e : ∀ a, U a ≅ V a)
    (hn : ∀ {a b : A} (f : a ⟶ b),
      x f ≫ (e a).hom ▷ T.map f = S.map f ◁ (e b).hom ≫ y f)
    (he : ∀ a, (e a).hom ∈ parity (R := k) _ _ 0 ∧
      (e a).hom ∈ degree (R := k) _ _ 0) :
    (qTriangleIsoOfComponents θ ψ U V x y hU hV hx hy e hn).hom.IsHomogeneous 0 0 := by
  subst U V
  exact he

theorem chevalleyQForwardUnitComparisonIso_homogeneous :
    (chevalleyQForwardUnitComparisonIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 := by
  apply qTriangleIsoOfRaw_homogeneous
  · intro a b f
    have h := qForwardUnitComparison_naturality _ _ f
      ((chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)).map ((F).map f))
      (qUnitHomCounit f) (chevalleyQReverseHomCounit ((F).map f)) (qUnitHomCounit_image f)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => ((F).mapComp f (chevalleyQGlobalUnit.X b)).hom ≫ z)
        (Category.assoc _ _ _)).trans h)
  · intro a
    exact qForwardUnitComparison_homogeneous _

theorem qTriangleEqToIso_homogeneous {S T : TwoSuperfunctor k A B}
    {θ ψ : TwoNatTrans S T} (p : θ = ψ) : (eqToIso p).hom.IsHomogeneous 0 0 := by
  cases p
  intro a
  exact ⟨id_mem (R := k) _, id_mem_degree (R := k) _⟩

theorem qTriangleIsoTrans_homogeneous {S T : TwoSuperfunctor k A B}
    {θ ψ φ : TwoNatTrans S T} (e : θ ≅ ψ) (f : ψ ≅ φ)
    (he : e.hom.IsHomogeneous 0 0) (hf : f.hom.IsHomogeneous 0 0) :
    (e ≪≫ f).hom.IsHomogeneous 0 0 := by
  intro a
  change e.hom.app a ≫ f.hom.app a ∈
    parity (R := k) (C := S.obj a ⟶ T.obj a) _ _ 0 ∧
    e.hom.app a ≫ f.hom.app a ∈ degree (R := k) (C := S.obj a ⟶ T.obj a) _ _ 0
  exact ⟨by simpa only [add_zero] using
      comp_mem (C := S.obj a ⟶ T.obj a) (he a).1 (hf a).1,
    by simpa only [add_zero] using
      comp_mem_degree (C := S.obj a ⟶ T.obj a) (he a).2 (hf a).2⟩

theorem qTriangleTransportIso_homogeneous {S T S' T' : TwoSuperfunctor k A B}
    (p : S = S') (q : T = T') {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ)
    (he : e.hom.IsHomogeneous 0 0) :
    (qTriangleTransportIso p q e).hom.IsHomogeneous 0 0 := by
  cases p
  cases q
  exact he

theorem qTriangleWhiskerRightIso_homogeneous {S T U : TwoSuperfunctor k A B}
    {θ θ' : TwoNatTrans S T} (e : θ ≅ θ') (ψ : TwoNatTrans T U)
    (he : e.hom.IsHomogeneous 0 0) :
    (qTriangleWhiskerRightIso e ψ).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨whiskerRight_mem (ψ.X a) (he a).1,
    GradedTwoSupercategory.whiskerRight_mem_degree (ψ.X a) (he a).2⟩

theorem chevalleyQForwardCounitPairIso_homogeneous :
    (chevalleyQForwardCounitPairIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 := by
  apply qTriangleIsoTrans_homogeneous
  · exact qTriangleEqToIso_homogeneous _
  · apply qTriangleIsoTrans_homogeneous
    · apply qTriangleTransportIso_homogeneous
      exact TwoNatTrans.precomposeModification_isHomogeneous (F)
        chevalleyQGlobalCounitInvCompIso_homogeneous
    · exact qTriangleEqToIso_homogeneous _

/-- The forward triangle modification is even and of integer degree zero. -/
theorem chevalleyQForwardTriangleIso_homogeneous :
    (chevalleyQForwardTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 :=
  qTriangleIsoTrans_homogeneous _ _
    (qTriangleWhiskerRightIso_homogeneous _ _ chevalleyQForwardUnitComparisonIso_homogeneous)
    chevalleyQForwardCounitPairIso_homogeneous

def qTriangleModificationComponent {S T : TwoSuperfunctor k A B}
    {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ) (a : A) : θ.X a ≅ ψ.X a where
  hom := e.hom.app a
  inv := e.inv.app a
  hom_inv_id := congrArg (fun α => α.app a) e.hom_inv_id
  inv_hom_id := congrArg (fun α => α.app a) e.inv_hom_id

/-- The inverse modification has the same parity and degree. -/
theorem chevalleyQForwardTriangleIso_inv_homogeneous :
    (chevalleyQForwardTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv.IsHomogeneous
      0 0 := by
  intro a
  let e := qTriangleModificationComponent
    (chevalleyQForwardTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)) a
  have h := chevalleyQForwardTriangleIso_homogeneous (D := D) (Sc := Sc) (sy := sy) (hc := hc) a
  refine ⟨inv_mem e h.1, ?_⟩
  change e.inv ∈ degree (R := k) (C := (F).obj a ⟶ (F).obj a) _ _ 0
  simpa only [neg_zero] using inv_mem_degree (C := (F).obj a ⟶ (F).obj a) e h.2
end OddMath.SKM
