/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.DownwardImage
import OddMath.QuiverHecke.TopSummand

/-!
# The class of the top summand

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity. For even degree-zero
idempotents `z`, `z′` of `E_s`, `E_t`, the top idempotent `α′(z′) α(z)` of `E_s F_t 1_{-ν}` is
the horizontal composite of `α(z)` and `α′(z′)` (`topEps_heq_hcomp`), so the class of its image
is the product of the classes `[α_{ν'}](z)` and `[α′_ν](z′)` (`cls_topRaw`), and lies in the image
of `γ` (`topRaw_mem_gammaRange`).
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands MonoidalCategory

namespace OddMath.QuiverHecke

variable {I : Type*} {X : Type*} [AddCommGroup X] {D : SKM.Datum I X} {k : Type*} [Field k]
  {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D} {hc : Sc.Homogeneous}

theorem wordCast_heq {μ : X} {s t s' t' : List (SKM.Letter I)} (hs : s = s') (ht : t = t')
    (f : (SKM.pres D Sc).obj (SKM.ob D μ s) ⟶ (SKM.pres D Sc).obj (SKM.ob D μ t)) :
    HEq (SKM.wordCast (Sc := Sc) μ hs ht f) f := by
  subst hs ht; rfl

theorem plcL_heq_whisk (μ : X) (u v s : List (SKM.Letter I))
    (f : (SKM.pres D Sc).obj (SKM.ob D (SKM.wt D μ v) s) ⟶
      (SKM.pres D Sc).obj (SKM.ob D (SKM.wt D μ v) s)) :
    HEq (SKM.plcL D Sc μ u v s s f)
      ((SKM.pres D Sc).whisk f (SKM.ob D (SKM.wt D (SKM.wt D μ v) s) u) (SKM.wd D μ v)) := by
  rw [SKM.plcL, dite_eq_left rfl]
  simp only [SKM.plc, LinearMap.coe_mk, AddHom.coe_mk]
  exact heq_conj (C := (SKM.pres D Sc).Presented) _ _ _

open BicategoryStruct in
/-- **The top idempotent is a horizontal composite**: `α′(z′) α(z)` on `E_s F_t 1_{-ν}` is
`α_{ν'}(z) ⋆ α′_ν(z′)`, `ν' = wt_{-ν}(F_t)`. -/
theorem topEps_heq_hcomp (ν : X) (s t : List I) {μ : X}
    (h : SKM.wt D (SKM.wt D (-ν) (SKM.dnWord t)) (upWord s) = μ)
    (z : End (hObj D Sc sy hc s)) (z' : End (hObj D Sc sy hc t)) :
    HEq (SKM.topEps (Sc := Sc) sy hc ν s t z z')
      (TwoSupercategory.hcomp (upProj (sy := sy) (hc := hc) h z)
        (show SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.dnWord t) rfl ⟶
            SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.dnWord t) rfl from SKM.dnE₀ Sc ν t z')) := by
  have hobj : (SKM.pres D Sc).obj (SKM.ob D (-ν) (upWord s ++ SKM.dnWord t)) =
      (SKM.pres D Sc).obj (SKM.K0Relations.word Sc sy hc μ _ (upWord s) h ≫
        SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.dnWord t) rfl).obj := by
    rw [SerreComplex.word_comp]; rfl
  simp only [TwoSupercategory.hcomp]
  change HEq (SKM.upMap sy hc ν s t z ≫ SKM.dnMap sy hc ν s t z') _
  refine heq_comp (C := (SKM.pres D Sc).Presented) hobj hobj hobj ?_ ?_
  · change HEq (SKM.plcL D Sc (-ν) [] (SKM.dnWord t) (upWord s) (upWord s)
      ((alpha D Sc (SKM.wt D (-ν) (SKM.dnWord t))).map z)) _
    refine (plcL_heq_whisk (-ν) [] (SKM.dnWord t) (upWord s) _).trans ?_
    refine HEq.symm ((whiskerRight_heq D Sc sy hc _ _).trans ?_)
    refine whisk_heq _ rfl rfl HEq.rfl ?_ rfl
    exact Obj.ext h.symm rfl
  · change HEq (SKM.wordCast (Sc := Sc) (-ν) (List.append_nil _) (List.append_nil _)
      (SKM.plcL D Sc (-ν) (upWord s) [] (SKM.dnWord t) (SKM.dnWord t) (SKM.dnE₀ Sc ν t z'))) _
    refine (wordCast_heq _ _ _).trans
      ((plcL_heq_whisk (-ν) (upWord s) [] (SKM.dnWord t) _).trans ?_)
    refine HEq.symm ((whiskerLeft_heq D Sc sy hc _ _).trans ?_)
    exact whisk_heq _ rfl rfl HEq.rfl rfl rfl

/-- Idempotence, degree zero and parity zero transport along a change of 1-morphism. -/
theorem summand_props_transport {μ μ' ν : X} (h : μ = μ')
    {f : (show SKM.UGr D Sc sy hc from ⟨μ⟩) ⟶ ⟨ν⟩} {f' : (show SKM.UGr D Sc sy hc from ⟨μ'⟩) ⟶ ⟨ν⟩}
    (hobj : f.obj = f'.obj)
    {y : (SKM.pres D Sc).obj f.obj ⟶ (SKM.pres D Sc).obj f.obj}
    {y' : (SKM.pres D Sc).obj f'.obj ⟶ (SKM.pres D Sc).obj f'.obj} (hy : HEq y y')
    (he : (y : f ⟶ f) ≫ (y : f ⟶ f) = y)
    (hd : (y : f ⟶ f) ∈ GradedSupercategory.degree (R := k) f f 0)
    (hp : (y : f ⟶ f) ∈ Supercategory.parity (R := k) f f 0) :
    (y' : f' ⟶ f') ≫ (y' : f' ⟶ f') = y' ∧
      (y' : f' ⟶ f') ∈ GradedSupercategory.degree (R := k) f' f' 0 ∧
      (y' : f' ⟶ f') ∈ Supercategory.parity (R := k) f' f' 0 := by
  subst h
  obtain rfl : f = f' := Presentation.Bicat.Hom.ext hobj
  obtain rfl := eq_of_heq hy
  exact ⟨he, hd, hp⟩

/-- `α′(z′)` on `F_t 1_{-ν}`, as a 2-morphism of `𝔘(𝔤)` from `wt_{-ν}(F_t)` to `-ν`. -/
abbrev dnProj (ν : X) {t : List I} (z' : End (hObj D Sc sy hc t)) :
    SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.dnWord t) rfl ⟶
      SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.dnWord t) rfl :=
  SKM.dnE₀ Sc ν t z'

theorem dnProj_heq (ν : X) {t : List I} (z' : End (hObj D Sc sy hc t)) :
    HEq (SOp.unsop ((SKM.chevHom (sy := sy) (hc := hc) _ _).map
      (upProj (sy := sy) (hc := hc) (rfl : SKM.wt D ν (upWord t) = _) z')))
      (dnProj (sy := sy) (hc := hc) ν z') :=
  (heq_conj (C := (SKM.pres D Sc).Presented) _ _ _).symm

theorem dnProj_props (ν : X) {t : List I} {z' : End (hObj D Sc sy hc t)} (hz' : z' ≫ z' = z')
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) :
    dnProj (sy := sy) (hc := hc) ν z' ≫ dnProj ν z' = dnProj ν z' ∧
      dnProj (sy := sy) (hc := hc) ν z' ∈ GradedSupercategory.degree (R := k) _ _ 0 ∧
      dnProj (sy := sy) (hc := hc) ν z' ∈ Supercategory.parity (R := k) _ _ 0 :=
  let G := SKM.chevHom (show SKM.UGr D Sc sy hc from ⟨(show X from SKM.wt D ν (upWord t))⟩)
    (show SKM.UGr D Sc sy hc from ⟨ν⟩)
  summand_props_transport (SKM.wt_flipW D ν _).symm (SKM.chevMap_obj D ν _) (dnProj_heq ν z')
    (SplitComplex.unsop_map_idem G (upProj_idem rfl hz') (alpha_mem_parity D Sc ν hz0'.2))
    (GradedSupercategory.IsGradedSuperfunctor.map_mem_degree (R := k) (F := G)
      (alpha_mem_degree D Sc sy ν hz0'.1))
    (chevHom_mem sy hc (alpha_mem_parity D Sc ν hz0'.2))

theorem word_up_dn (ν : X) (s t : List I) {μ : X}
    (h : SKM.wt D (SKM.wt D (-ν) (SKM.dnWord t)) (upWord s) = μ)
    (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ) :
    SKM.K0Relations.word Sc sy hc μ _ (upWord s) h ≫
        SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.dnWord t) rfl =
      SKM.K0Relations.word Sc sy hc μ (-ν) (upWord s ++ SKM.dnWord t) hw := by
  rw [SerreComplex.word_comp]

/-- The top idempotent `α′(z′) α(z)` as a 2-morphism of `𝔘(𝔤)` on `E_s F_t 1_{-ν}`. -/
abbrev topProj (ν : X) (s t : List I) {μ : X}
    (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ)
    (z : End (hObj D Sc sy hc s)) (z' : End (hObj D Sc sy hc t)) :
    SKM.K0Relations.word Sc sy hc μ (-ν) _ hw ⟶ SKM.K0Relations.word Sc sy hc μ (-ν) _ hw :=
  SKM.topEps (Sc := Sc) sy hc ν s t z z'

theorem wt_up_dn {ν : X} {s t : List I} {μ : X}
    (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ) :
    SKM.wt D (SKM.wt D (-ν) (SKM.dnWord t)) (upWord s) = μ := by
  rw [← SKM.wt_append]; exact hw

theorem topProj_props (ν : X) (s t : List I) {μ : X}
    (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ)
    {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)} (hz : z ≫ z = z)
    (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) :
    topProj ν s t hw z z' ≫ topProj ν s t hw z z' = topProj ν s t hw z z' ∧
      topProj ν s t hw z z' ∈ GradedSupercategory.degree (R := k) _ _ 0 ∧
      topProj ν s t hw z z' ∈ Supercategory.parity (R := k) _ _ 0 := by
  have h := wt_up_dn hw
  obtain ⟨he', hd', hp'⟩ := dnProj_props (sy := sy) (hc := hc) ν hz' hz0'
  exact summand_props_transport rfl (congrArg Presentation.Bicat.Hom.obj (word_up_dn ν s t h hw))
    (topEps_heq_hcomp ν s t h z z').symm
    (SKM.Summands.hcomp_idem (upProj_idem h hz) he' (alpha_mem_parity D Sc _ hz0.2) hp')
    (SKM.Summands.hcomp_mem_degree_zero (alpha_mem_degree D Sc sy _ hz0.1) hd')
    (SKM.Summands.hcomp_mem_parity_zero (alpha_mem_parity D Sc _ hz0.2) hp')

/-- **The class of the top summand**: `[Q^m Π^a (E_s F_t 1_{-ν}, α′(z′) α(z))] =
[Q^m Π^a (E_s 1_{ν'}, α(z))] · [(F_t 1_{-ν}, α′(z′))]`, the factors being the images of
`[Q^m Π^a (s, z)]` and `[(t, z′)]` under the class maps `[α_{ν'}]` and `[α′_ν]`. -/
theorem cls_topProj (ν : X) (s t : List I) {μ : X}
    (hw : SKM.wt D (-ν) (upWord s ++ SKM.dnWord t) = μ)
    {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)} (hz : z ≫ z = z)
    (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) (m : ℤ) (a : ZMod 2) :
    SerreComplex.rcls sy hc (topProj_props ν s t hw hz hz' hz0 hz0').1
        (topProj_props ν s t hw hz hz' hz0 hz0').2.1
        (topProj_props ν s t hw hz hz' hz0 hz0').2.2 m a =
      upK0 Sc sy hc μ (SKM.wt D (-ν) (SKM.dnWord t)) (K₀.mk (raw hz hz0.1 hz0.2 m a)) *
        downK0 Sc sy hc (SKM.wt D ν (upWord t)) ν (K₀.mk (raw hz' hz0'.1 hz0'.2 0 0)) := by
  have h := wt_up_dn hw
  obtain ⟨he', hd', hp'⟩ := dnProj_props (sy := sy) (hc := hc) ν hz' hz0'
  rw [upK0_raw _ _ _ m a h, downK0_raw _ _ _ 0 0 rfl, neg_zero]
  refine Eq.trans ?_ (congrArg (_ * ·) (SerreComplex.rcls_transport sy hc
    (SKM.wt_flipW D ν _).symm (SKM.chevMap_obj D ν _) _ _ (dnProj_heq ν z') _ _ _ he' hd' hp'
    0 0).symm)
  rw [SerreComplex.rcls, SerreComplex.rcls, SerreComplex.rcls, ← MulOpposite.op_mul,
    SKM.Summands.mk_raw_mul_mk_raw]
  congr 2
  rw [add_zero, add_zero]
  exact SerreComplex.raw_congr (k := k) (word_up_dn ν s t h hw).symm
    (topEps_heq_hcomp ν s t h z z') _ _ _ _ _ _ _ _

section Image

variable {k' : Type*} [Field k'] {Q : CoveringQuantum.RootDatum I X} {S : SKM.Scalars Q.toSKM k'}
  {hS : S.Homogeneous} {cs : SKM.CScalars S} {hf : Q.skmSymmetrizer.DegreeLocallyFinite}

/-- The class of the top summand lies in the image of `γ`. -/
theorem topProj_mem_gammaRange (ν : X) (s t : List I) {μ : X}
    (hw : SKM.wt Q.toSKM (-ν) (upWord s ++ SKM.dnWord t) = μ)
    {z : End (hObj Q.toSKM S Q.skmSymmetrizer hS s)}
    {z' : End (hObj Q.toSKM S Q.skmSymmetrizer hS t)} (hz : z ≫ z = z) (hz' : z' ≫ z' = z')
    (hz0 : z ∈ homPiece Q.toSKM S Q.skmSymmetrizer hS s s 0 0)
    (hz0' : z' ∈ homPiece Q.toSKM S Q.skmSymmetrizer hS t t 0 0) (m : ℤ) (a : ZMod 2) :
    SerreComplex.rcls Q.skmSymmetrizer hS (topProj_props ν s t hw hz hz' hz0 hz0').1
        (topProj_props ν s t hw hz hz' hz0 hz0').2.1
        (topProj_props ν s t hw hz hz' hz0 hz0').2.2 m a ∈ gammaRange Q hS cs hf := by
  rw [cls_topProj ν s t hw hz hz' hz0 hz0']
  exact gammaRange.mul_mem (upK0_mem_gammaRange _ _ _) (downK0_mem_gammaRange _ _ _)

end Image

end OddMath.QuiverHecke
