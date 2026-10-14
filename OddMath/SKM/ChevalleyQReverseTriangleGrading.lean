/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTriangle

/-!
# Grading of the second triangle of `ω_q`

Both modifications of `chevalleyQReverseTriangleIso` are even of degree zero.

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
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "O" a:max => (⟨⟨a⟩⟩ : B)

theorem qReverseCounitComparison_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qReverseCounitComparison p).hom ∈ parity (R := k) _ _ 0 ∧
      (qReverseCounitComparison p).hom ∈ degree (R := k) _ _ 0 := by
  subst a'
  refine ⟨inv_mem ((G).mapId (O a)) ((G).mapId_hom_mem (O a)), ?_⟩
  change ((G).mapId (O a)).inv ∈
    degree (R := k) (C := (G).obj (O a) ⟶ (G).obj (O a)) _ _ 0
  simpa only [neg_zero] using inv_mem_degree (C := (G).obj (O a) ⟶ (G).obj (O a))
    ((G).mapId (O a)) (chevalleyQReverseTwo_isGraded.mapId_hom_mem_degree (O a))

theorem qReverseIsoOfRaw_homogeneous {S T : TwoSuperfunctor k B A} (θ ψ : TwoNatTrans S T)
    (U V : ∀ a, S.obj a ⟶ T.obj a)
    (x : ∀ {a b : B} (f : a ⟶ b), S.map f ≫ U b ⟶ U a ≫ T.map f)
    (y : ∀ {a b : B} (f : a ⟶ b), S.map f ≫ V b ⟶ V a ≫ T.map f)
    (hU : θ.X = U) (hV : ψ.X = V)
    (hx : ∀ {a b : B} (f : a ⟶ b), HEq (θ.x f) (x f))
    (hy : ∀ {a b : B} (f : a ⟶ b), HEq (ψ.x f) (y f))
    (e : ∀ a, U a ≅ V a)
    (hn : ∀ {a b : B} (f : a ⟶ b),
      x f ≫ (e a).hom ▷ T.map f = S.map f ◁ (e b).hom ≫ y f)
    (he : ∀ a, (e a).hom ∈ parity (R := k) _ _ 0 ∧
      (e a).hom ∈ degree (R := k) _ _ 0) :
    (qReverseIsoOfComponents θ ψ U V x y hU hV hx hy e hn).hom.IsHomogeneous 0 0 := by
  subst U V
  exact he

theorem qReverseCompareIso_homogeneous (P : TwoSuperfunctor k B A)
    (Q : TwoSuperfunctor k A B)
    (θ : TwoNatTrans (P.comp Q) (TwoSuperfunctor.id k B))
    (ψ : TwoNatTrans (Q.comp P) (TwoSuperfunctor.id k A))
    (e : ∀ b, P.map (θ.X b) ≅ ψ.X (P.obj b))
    (hn : ∀ {a b : B} (f : a ⟶ b),
      TwoNatTrans.postcomposeCell P θ f ≫ (e a).hom ▷ P.map f =
        P.map (Q.map (P.map f)) ◁ (e b).hom ≫ ψ.x (P.map f))
    (he : ∀ b, (e b).hom ∈ parity (R := k) _ _ 0 ∧
      (e b).hom ∈ degree (R := k) _ _ 0) :
    (qReverseCompareIso P Q θ ψ e hn).hom.IsHomogeneous 0 0 := by
  unfold qReverseCompareIso
  apply qReverseIsoOfRaw_homogeneous
  · intro a b f
    exact qReverseTransport_x_heq _ _ _ f
  · exact he

theorem chevalleyQReverseCounitComparisonIso_homogeneous :
    (chevalleyQReverseCounitComparisonIso (D := D) (Sc := Sc)
      (sy := sy) (hc := hc)).hom.IsHomogeneous 0 0 := by
  unfold chevalleyQReverseCounitComparisonIso
  apply qReverseCompareIso_homogeneous
  intro b
  exact qReverseCounitComparison_homogeneous _

theorem qReverseEqToIso_homogeneous {S T : TwoSuperfunctor k B A}
    {θ ψ : TwoNatTrans S T} (p : θ = ψ) : (eqToIso p).hom.IsHomogeneous 0 0 := by
  cases p
  intro a
  exact ⟨id_mem (R := k) _, id_mem_degree (R := k) _⟩

theorem qReverseIsoTrans_homogeneous {S T : TwoSuperfunctor k B A}
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

theorem qReverseTransportIso_homogeneous {S T S' T' : TwoSuperfunctor k B A}
    (p : S = S') (q : T = T') {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ)
    (he : e.hom.IsHomogeneous 0 0) :
    (qReverseTransportIso p q e).hom.IsHomogeneous 0 0 := by
  cases p
  cases q
  exact he

theorem qReverseWhiskerLeftIso_homogeneous {S T U : TwoSuperfunctor k B A}
    (θ : TwoNatTrans S T) {ψ ψ' : TwoNatTrans T U} (e : ψ ≅ ψ')
    (he : e.hom.IsHomogeneous 0 0) :
    (qReverseWhiskerLeftIso θ e).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨whiskerLeft_mem (θ.X a) (he a).1,
    GradedTwoSupercategory.whiskerLeft_mem_degree (θ.X a) (he a).2⟩

theorem chevalleyQReverseUnitPairIso_homogeneous :
    (chevalleyQReverseUnitPairIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 := by
  apply qReverseIsoTrans_homogeneous
  · exact qReverseEqToIso_homogeneous _
  · apply qReverseIsoTrans_homogeneous
    · apply qReverseTransportIso_homogeneous
      exact TwoNatTrans.precomposeModification_isHomogeneous (G)
        chevalleyQGlobalUnitCompIso_homogeneous
    · exact qReverseEqToIso_homogeneous _

/-- The reverse triangle modification is even and degree zero. -/
theorem chevalleyQReverseTriangleIso_homogeneous :
    (chevalleyQReverseTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 :=
  qReverseIsoTrans_homogeneous _ _
    (qReverseWhiskerLeftIso_homogeneous _ _ chevalleyQReverseCounitComparisonIso_homogeneous)
    chevalleyQReverseUnitPairIso_homogeneous

def qReverseModificationComponent {S T : TwoSuperfunctor k B A}
    {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ) (a : B) : θ.X a ≅ ψ.X a where
  hom := e.hom.app a
  inv := e.inv.app a
  hom_inv_id := congrArg (fun α => α.app a) e.hom_inv_id
  inv_hom_id := congrArg (fun α => α.app a) e.inv_hom_id

/-- Its inverse modification is also even and degree zero. -/
theorem chevalleyQReverseTriangleIso_inv_homogeneous :
    (chevalleyQReverseTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv.IsHomogeneous
      0 0 := by
  intro a
  let e := qReverseModificationComponent
    (chevalleyQReverseTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)) a
  have h := chevalleyQReverseTriangleIso_homogeneous (D := D) (Sc := Sc) (sy := sy) (hc := hc) a
  refine ⟨inv_mem e h.1, ?_⟩
  change e.inv ∈ degree (R := k) (C := (G).obj a ⟶ (G).obj a) _ _ 0
  simpa only [neg_zero] using inv_mem_degree (C := (G).obj a ⟶ (G).obj a) e h.2

end OddMath.SKM
