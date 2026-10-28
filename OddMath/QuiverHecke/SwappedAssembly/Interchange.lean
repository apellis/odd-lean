/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.LayerEntries

/-! # The super interchange law in the swapped layer representation

A 2-representation of the Kac–Moody 2-supercategory must respect the super interchange law
(Brundan–Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (1.4)–(1.5), used for the
Kac–Moody 2-supercategories of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5): two generators `g` and `g'` placed side by side may be
applied in either order, at the cost of the Koszul sign `(-1)^{|g||g'|}`.

This file proves `InterchangeLaw` for the swapped layer representation of
`OddMath/QuiverHecke/SwappedAssembly/Matrices.lean` from the supernaturality of the generator
images (`GeneratorsSupernatural`): every matrix entry `gens.image g p p'` is a homogeneous
supernatural transformation, of the parity of `g`, between the path functors of `p` and `p'`
(`docs/Nondegeneracy/SwappedActionAssembly.md`, end of §3: "each local entry is supernatural of
its declared parity").

The entry of either composite at an output path `pu · qa · pm · qb · pr` is a double sum over
the paths `pa`, `pb` of the bottom boundaries of `g` and `g'`. Termwise, the two composites
differ by moving the component `F_{pm}(η)` of `g'` past the component `γ` of `g`, which is the
supernaturality of `γ` (`eqToHom_map_comp_exchange`). When one of the four layers is ill
formed, so is a layer of the other composite (`valid_interchange_of_valid`), and both sides
vanish.

Main declarations: `valid_interchange_of_valid`, `eqToHom_map_comp_exchange`,
`ProbeReservoir.GeneratorsSupernatural`, `ProbeReservoir.interchangeLaw`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u

section Valid

variable {S : Signature.{u, u, u}}

/-- Exchanging the boundaries of two generators separated by `m` preserves well-formedness of
the two layers. -/
theorem valid_interchange_of_valid {s : S.Region} {l m r : List S.Colour} {g g' : S.Gen}
    {A A' B B' : List S.Colour}
    (hA' : S.ok (S.left g) A' ∧ S.endR (S.left g) A' = S.right g)
    (hB' : S.ok (S.left g') B' ∧ S.endR (S.left g') B' = S.right g')
    (hA : S.endR (S.left g) A = S.right g)
    (h1 : (⟨s, l, g, m ++ (B ++ r)⟩ : Layer S).Valid)
    (h2 : (⟨s, l ++ (A ++ m), g', r⟩ : Layer S).Valid) :
    (⟨s, l, g, m ++ (B' ++ r)⟩ : Layer S).Valid ∧
      (⟨s, l ++ (A' ++ m), g', r⟩ : Layer S).Valid := by
  obtain ⟨h1lo, h1le, h1do, h1de, h1co, h1ce, h1ro⟩ := h1
  obtain ⟨h2lo, h2le, h2do, h2de, h2co, h2ce, h2ro⟩ := h2
  simp only [Signature.ok_append, Signature.endR_append] at *
  refine ⟨⟨h1lo, h1le, h1do, h1de, h1co, h1ce, ?_⟩, ⟨?_, ?_, h2do, h2de, h2co, h2ce, h2ro⟩⟩
  all_goals
    dsimp only
    rw [h1le, hA] at h2le h2lo
    simp only [Signature.ok_append, Signature.endR_append, h1le, hA', h2le, hB'.2, h1lo,
      h1ro.1, h2ro, hB'.1, and_self]

end Valid

section Entry

variable {k : Type*} [CommRing k]

/-- **Exchange of two homogeneous transformations at different heights**, up to the transports
along equalities of functors and objects that occur in the swapped layer representation:
`γ` is supernatural of parity `p`, `η` homogeneous of parity `q`, and `Fm` (the functor of the
strands between them) preserves parities, so moving `η` below `γ` costs `(-1)^{pq}`. -/
theorem eqToHom_map_comp_exchange {C₀ C₁ C₂ C₃ C₄ : Type*} [Category C₀] [Category C₁]
    [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₀] [Linear k C₀] [Preadditive C₁] [Linear k C₁] [Supercategory k C₁]
    [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    [Preadditive C₃] [Linear k C₃] [Supercategory k C₃]
    (Fu : C₁ ⥤ C₀) (Fa Fa' : C₂ ⥤ C₁) (Fm : C₃ ⥤ C₂) (Fb Fb' : C₄ ⥤ C₃) (Z : C₄)
    {γ : ∀ W, Fa.obj W ⟶ Fa'.obj W} {η : Fb.obj Z ⟶ Fb'.obj Z} {p q : ZMod 2}
    (hγ : IsSupernatural k p γ) (hη : η ∈ parity (R := k) _ _ q)
    (hFu : ∀ {X Y : C₁} (c : k) (f : X ⟶ Y), Fu.map (c • f) = c • Fu.map f)
    (hFm : ∀ {X Y : C₃} {f : X ⟶ Y}, f ∈ parity (R := k) X Y q →
      Fm.map f ∈ parity (R := k) _ _ q)
    (G₁ G₂ : C₃ ⥤ C₀) (hG₁ : G₁ = Fm ⋙ Fa ⋙ Fu) (hG₂ : G₂ = Fm ⋙ Fa' ⋙ Fu)
    (W₁ W₂ : C₂) (hW₁ : W₁ = Fm.obj (Fb.obj Z)) (hW₂ : W₂ = Fm.obj (Fb'.obj Z)) {A B : C₀}
    (e₁ : A = Fu.obj (Fa.obj W₁)) (e₂ : Fu.obj (Fa'.obj W₁) = G₂.obj (Fb.obj Z))
    (e₃ : G₂.obj (Fb'.obj Z) = B)
    (f₁ : A = G₁.obj (Fb.obj Z)) (f₂ : G₁.obj (Fb'.obj Z) = Fu.obj (Fa.obj W₂))
    (f₃ : Fu.obj (Fa'.obj W₂) = B) :
    eqToHom e₁ ≫ Fu.map (γ W₁) ≫ eqToHom e₂ ≫ G₂.map η ≫ eqToHom e₃ =
      sign k (p * q) • (eqToHom f₁ ≫ G₁.map η ≫ eqToHom f₂ ≫ Fu.map (γ W₂) ≫ eqToHom f₃) := by
  subst hG₁ hG₂ hW₁ hW₂ e₁ f₃
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map,
    Functor.comp_obj]
  rw [← Fu.map_comp, ← Fu.map_comp, hγ.naturality (hFm hη), hFu, smul_smul,
    Supercategory.sign_mul_self, one_smul]

end Entry

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc} {Gs Ys : ∀ s, P.H s}

/-- An ill-formed layer acts by zero. -/
theorem layerMap_of_not_valid (gens : P.Generators) {L : Layer (SKM.sig D)} (hL : ¬ L.Valid) :
    layerMap (Gs := Gs) (Ys := Ys) gens L = 0 := by
  ext x
  funext sl sr q
  simp only [layerMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  unfold layerFun
  split_ifs
  rfl

omit [AddCommGroup X] in
/-- Reassociation of a concatenation of five paths. -/
theorem heq_assoc₁ {l a m b r : List (Col I X)} {s₀ s₁ s₂ s₃ s₄ s₅ : Sector I}
    (pu : SPath l s₀ s₁) (pa : SPath a s₁ s₂) (pm : SPath m s₂ s₃) (pb : SPath b s₃ s₄)
    (pr : SPath r s₄ s₅) :
    HEq (((pu.append (pa.append pm)).append pb).append pr)
      (pu.append (pa.append (pm.append (pb.append pr)))) :=
  (SPath.append_assoc_heq _ pb pr).trans ((SPath.append_assoc_heq pu _ _).trans
    (SPath.append_heq_right pu (by simp) (SPath.append_assoc_heq pa pm _)))

omit [AddCommGroup X] in
/-- Reassociation of a concatenation of five paths. -/
theorem heq_assoc₂ {l a m b r : List (Col I X)} {s₀ s₁ s₂ s₃ s₄ s₅ : Sector I}
    (pu : SPath l s₀ s₁) (pa : SPath a s₁ s₂) (pm : SPath m s₂ s₃) (pb : SPath b s₃ s₄)
    (pr : SPath r s₄ s₅) :
    HEq ((pu.append pa).append (pm.append (pb.append pr)))
      (((pu.append (pa.append pm)).append pb).append pr) :=
  (SPath.append_assoc_heq pu pa _).trans (heq_assoc₁ pu pa pm pb pr).symm

/-- The Koszul sign of an interchange is the parity sign of the product of the parities. -/
theorem interchange_sign (s : (SKM.sig D).Region) (g g' : (SKM.sig D).Gen)
    (m : List (SKM.sig D).Colour) :
    (((⟨s, g, m, g'⟩ : InterchangeData (SKM.sig D)).sign : ℤ) : k) =
      sign k (g.1.parity D * g'.1.parity D) := by
  simp only [InterchangeData.sign, SKM.sig]
  rcases parity_eq_zero_or_one (g.1.parity D) with h | h <;>
    rcases parity_eq_zero_or_one (g'.1.parity D) with h' | h' <;>
    simp [h, h', sign]

theorem layerRep_act (gens : P.Generators) (L : Layer (SKM.sig D)) :
    (P.layerRep Gs Ys gens).act L = layerMap gens L := rfl

/-- Every matrix entry of every generator image is a homogeneous supernatural transformation,
of the parity of the generator, between the functors of the two summand paths. -/
def GeneratorsSupernatural (gens : P.Generators) : Prop :=
  ∀ (g : (SKM.sig D).Gen) {t s : Sector I} (p : SPath (wd D g.2 g.1.dom) t s)
    (p' : SPath (wd D g.2 g.1.cod) t s),
    IsSupernatural k (g.1.parity D) (fun Z => gens.image g p p' Z)

variable (Gs Ys) in
/-- **The super interchange law for the swapped layer representation**, from the
supernaturality of the generator images. -/
theorem interchangeLaw {gens : P.Generators} (hs : GeneratorsSupernatural gens) :
    InterchangeLaw (P.layerRep Gs Ys gens) := by
  intro x hx u v _
  refine (P.layerRep Gs Ys gens).toLocal.evalW_interchange_eq_zero
    (fun s l m r g g' => LinearMap.ext fun y => ?_) x hx u v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LayerRep.toLocal_κ]
  rw [LayerRep.res_op_op_ext _ _ _ (by simp [Layer.dom]) (by simp [Layer.dom, Layer.cod])
      (by simp [Layer.cod]),
    LayerRep.res_op_op_ext _ _ _ (by simp [Layer.dom]) (by simp [Layer.dom, Layer.cod])
      (by simp [Layer.cod])]
  by_cases hv : (⟨s, l, g, m ++ ((SKM.sig D).dom g' ++ r)⟩ : Layer (SKM.sig D)).Valid ∧
      (⟨s, l ++ ((SKM.sig D).cod g ++ m), g', r⟩ : Layer (SKM.sig D)).Valid
  swap
  · have hv' : ¬ ((⟨s, l, g, m ++ ((SKM.sig D).cod g' ++ r)⟩ : Layer (SKM.sig D)).Valid ∧
        (⟨s, l ++ ((SKM.sig D).dom g ++ m), g', r⟩ : Layer (SKM.sig D)).Valid) :=
      fun ⟨h1, h2⟩ => hv (valid_interchange_of_valid ⟨h1.cod_ok, h1.cod_end⟩
        ⟨h2.dom_ok, h2.dom_end⟩ h1.dom_end h1 h2)
    rw [not_and_or] at hv hv'
    rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;>
    · have h0 : (P.layerRep Gs Ys gens).act _ = 0 := layerMap_of_not_valid gens hv
      have h0' : (P.layerRep Gs Ys gens).act _ = 0 := layerMap_of_not_valid gens hv'
      simp only [h0, h0', LinearMap.zero_apply]
      repeat (first
        | erw [LayerRep.cast_zero (P.layerRep Gs Ys gens)]
        | erw [map_zero]
        | erw [smul_zero])
      all_goals simp [Layer.cod, Layer.dom]
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h1', h2'⟩ : (⟨s, l, g, m ++ ((SKM.sig D).cod g' ++ r)⟩ : Layer (SKM.sig D)).Valid ∧
      (⟨s, l ++ ((SKM.sig D).dom g ++ m), g', r⟩ : Layer (SKM.sig D)).Valid :=
    valid_interchange_of_valid ⟨h1.dom_ok, h1.dom_end⟩ ⟨h2.cod_ok, h2.cod_end⟩ h1.cod_end h1 h2
  funext s0 t q
  dsimp only [LayerRep.toLocal_κ] at q t
  obtain ⟨t1, pu, q1, rfl⟩ := SPath.exists_eq_append l q
  obtain ⟨t2, qa, q2, rfl⟩ := SPath.exists_eq_append _ q1
  obtain ⟨t3, pm, q3, rfl⟩ := SPath.exists_eq_append m q2
  obtain ⟨t4, qb, pr, rfl⟩ := SPath.exists_eq_append _ q3
  erw [Mod.cast_apply (by simp [Layer.cod]) _ s0 t _
    (((pu.append (qa.append pm)).append qb).append pr)
    (heq_assoc₁ pu qa pm qb pr)]
  rw [layerRep_act]
  erw [layerMap_apply_append gens _ h2 _ (pu.append (qa.append pm)) qb pr]
  conv_lhs =>
    enter [1, 2, pb]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.cod, Layer.dom]) _ s0 _ _
      ((pu.append qa).append (pm.append (pb.append pr))) (heq_assoc₂ pu qa pm pb pr)]
    rw [layerRep_act]
    erw [layerMap_apply_append gens _ h1 _ pu qa (pm.append (pb.append pr))]
    enter [1, 1, 2, pa]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.dom]) _ s0 _ _
      (pu.append (pa.append (pm.append (pb.append pr))))
      (SPath.append_assoc_heq pu pa _).symm]
  refine Eq.trans ?_ (Mod.smul_apply (P := P) (Gs := Gs) (Ys := Ys)
    (a := ⟨s, l ++ ((SKM.sig D).cod g ++ (m ++ ((SKM.sig D).cod g' ++ r)))⟩) _ _ _ _ _).symm
  erw [Mod.cast_apply (by simp [Layer.cod]) _ s0 t _
    ((pu.append qa).append (pm.append (qb.append pr))) (SPath.append_assoc_heq pu qa _)]
  rw [layerRep_act]
  erw [layerMap_apply_append gens _ h1' _ pu qa (pm.append (qb.append pr))]
  conv_rhs =>
    enter [2, 1, 2, pa]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.cod, Layer.dom]) _ s0 _ _
      (((pu.append (pa.append pm)).append qb).append pr) (heq_assoc₂ pu pa pm qb pr).symm]
    rw [layerRep_act]
    erw [layerMap_apply_append gens _ h2' _ (pu.append (pa.append pm)) qb pr]
    enter [1, 1, 2, pb]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.dom]) _ s0 _ _
      (pu.append (pa.append (pm.append (pb.append pr)))) (heq_assoc₁ pu pa pm pb pr).symm]
  simp only [Preadditive.sum_comp, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pa _ => Finset.sum_congr rfl fun pb _ => ?_
  rw [← Linear.comp_smul, interchange_sign]
  congr 1
  exact eqToHom_map_comp_exchange (P.pathFunctor pu) (P.pathFunctor pa) (P.pathFunctor qa)
    (P.pathFunctor pm) (P.pathFunctor pb) (P.pathFunctor qb) ((P.pathFunctor pr).obj (Ys t))
    (hs g pa qa) ((hs g' pb qb).mem _) (P.pathFunctor_map_smul pu) (P.pathFunctor_map_mem pm)
    _ _ (by rw [pathFunctor_append, pathFunctor_append]; rfl)
    (by rw [pathFunctor_append, pathFunctor_append]; rfl)
    _ _ (by rw [pathFunctor_append, pathFunctor_append]; rfl)
    (by rw [pathFunctor_append, pathFunctor_append]; rfl) _ _ _ _ _ _

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
