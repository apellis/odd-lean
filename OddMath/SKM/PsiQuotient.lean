/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiKernel
import OddMath.SKM.ChevalleyGradedHom
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The homwise quotient maps for ψ

The homwise linear descent in the proof of Brundan–Ellis,
*Super Kac–Moody 2-categories*, Proposition 9.4. The seven-generator evaluator
kills the existing presentation ideal, and therefore descends to its presented
Hom spaces. No relation-preservation assumption is imposed.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The presentation class map's kernel is killed by the seven-generator evaluator. -/
theorem psiLin_ker (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    LinearMap.ker ((pres D Sc).linMap (ob D μ s) (ob D μ r)) ≤
      LinearMap.ker (psiLin (sy := sy) (hc := hc) t cs ν μ hs hr) := by
  intro x hx
  apply psiLin_ideal t ht cs ν μ hs hr
  have h : (pres D Sc).lin x = (pres D Sc).lin 0 := by
    simpa only [LinearMap.mem_ker, Presentation.linMap_apply, Presentation.lin_zero] using hx
  simpa only [sub_zero] using ((pres D Sc).lin_eq_iff x 0).mp h

/-- The linear ψ map on the existing presented Hom space between signed words. -/
def psiQuotient (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)) →ₗ[k]
      (psiAt (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr) :=
  let q := (pres D Sc).linMap (ob D μ s) (ob D μ r)
  ((LinearMap.ker q).liftQ (psiLin t cs ν μ hs hr) (psiLin_ker t ht cs ν μ hs hr)).comp
    (q.quotKerEquivOfSurjective (fun x => (pres D Sc).lin_surjective x)).symm.toLinearMap

/-- Computation on an arbitrary linear diagram representative. -/
@[simp] theorem psiQuotient_lin (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : LinDiagram k (ob D μ s) (ob D μ r)) :
    psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hr ((pres D Sc).lin x) =
      psiLin t cs ν μ hs hr x := by
  change (LinearMap.ker _).liftQ _ (psiLin_ker t ht cs ν μ hs hr)
    ((((pres D Sc).linMap _ _).quotKerEquivOfSurjective _).symm
      (((pres D Sc).linMap _ _) x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- Computation on an arbitrary diagram in the original syntax. -/
@[simp] theorem psiQuotient_diag (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (d : ob D μ s ⟶ ob D μ r) :
    psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hr ((pres D Sc).diag d) =
      psiDiagram t cs ν μ hs hr d := by
  change psiQuotient t ht cs ν μ hs hr ((pres D Sc).lin (Finsupp.single d 1)) = _
  rw [psiQuotient_lin, psiLin_single, one_smul]

/-- Vertical identities are preserved after quotient descent. -/
@[simp] theorem psiQuotient_id (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s : List (Letter I)} (hs : wt D μ s = ν) :
    psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hs (𝟙 _) = 𝟙 _ := by
  rw [← (pres D Sc).diag_id, psiQuotient_diag, psiDiagram_id]

/-- Vertical composition is preserved on all presented Hom spaces. -/
theorem psiQuotient_comp (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r))
    (y : (pres D Sc).obj (ob D μ r) ⟶ (pres D Sc).obj (ob D μ q)) :
    psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hq (x ≫ y) =
      psiQuotient t ht cs ν μ hs hr x ≫ psiQuotient t ht cs ν μ hr hq y := by
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
  obtain ⟨y, rfl⟩ := (pres D Sc).lin_surjective y
  rw [← Presentation.lin_comp, psiQuotient_lin, psiQuotient_lin, psiQuotient_lin]
  exact psiLin_comp t cs ν μ hs hr hq x y

/-- Quotient descent preserves the parity of every homogeneous morphism. -/
theorem psiQuotient_mem_parity (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {p : ZMod 2} {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    (hx : x ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ p) :
    psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hr x ∈ parity (R := k) _ _ p := by
  refine Presentation.homDeg_induction
    (motive := fun x => psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hr x ∈
      parity (R := k) _ _ p) ?_ ?_ ?_ ?_ hx
  · intro d hd
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [degree_parity_mkD] at hd
    rw [psiQuotient_diag, psiDiagram_mkD, ← hd]
    exact psiRaw_mem_parity t cs ν μ L hs hr hL
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- Quotient descent preserves the integer degree of every homogeneous morphism. -/
theorem psiQuotient_mem_degree (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {n : ℤ} {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    (hx : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ n) :
    psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hr x ∈
      GradedSupercategory.degree (R := k) _ _ n := by
  refine Presentation.homDeg_induction
    (motive := fun x => psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs hr x ∈
      GradedSupercategory.degree (R := k) _ _ n) ?_ ?_ ?_ ?_ hx
  · intro d hd
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [degree_gdeg_mkD] at hd
    rw [psiQuotient_diag, psiDiagram_mkD, ← hd]
    exact psiRaw_mem_degree t cs ν μ L hs hr hL
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- The signed word underlying an arbitrary 1-morphism has its specified start weight. -/
theorem psiWordAt_weight {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    wt D b.region (f.obj.word.map Col.l) = a.region := by
  exact (congrArg Obj.start (homObj_normal f)).symm.trans f.start_eq

/-- Every 1-morphism equals its signed-word normal form in its existing Hom category. -/
theorem psiWordAt_normal {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    f = psiWordAt (D := D) (Sc := Sc) a.region b.region (f.obj.word.map Col.l) (psiWordAt_weight f) := by
  exact Presentation.Bicat.Hom.ext (homObj_normal f)

private def psiMap₂Transport {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (ef : f = f') (eg : g = g')
    (L : (f' ⟶ g') →ₗ[k] (psiMap f' ⟶ psiMap g')) :
    (f ⟶ g) →ₗ[k] (psiMap f ⟶ psiMap g) := by
  cases ef; cases eg; exact L

/-- The linear map on arbitrary 2-morphisms of `UGr`, using the existing presentation quotient. -/
def psiMap₂ (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (psiMap f ⟶ psiMap g) := by
  have ef := psiWordAt_normal f
  have eg := psiWordAt_normal g
  let Q := psiQuotient (sy := sy) (hc := hc) t ht cs a.region b.region
    (psiWordAt_weight f) (psiWordAt_weight g)
  exact psiMap₂Transport ef eg Q

private theorem psiMap₂Transport_wordAt (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν)
    (es : s = s') (er : r = r')
    (ef : psiWordAt (Sc := Sc) ν μ s hs = psiWordAt ν μ s' hs')
    (eg : psiWordAt (Sc := Sc) ν μ r hr = psiWordAt ν μ r' hr') :
    psiMap₂Transport ef eg (psiQuotient (sy := sy) (hc := hc) t ht cs ν μ hs' hr') =
      psiQuotient t ht cs ν μ hs hr := by
  cases es; cases er; rfl

/-- On signed words the map on `UGr` Hom spaces is exactly the quotient map. -/
@[simp] theorem psiMap₂_wordAt (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) =
      psiQuotient t ht cs ν μ hs hr := by
  exact psiMap₂Transport_wordAt t ht cs ν μ hs hr _ _
    (wd_map_l (D := D) μ s).symm (wd_map_l (D := D) μ r).symm _ _

/-- Every 1-morphism can be eliminated in favor of a signed word at the same boundaries. -/
theorem exists_psiWordAt {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    ∃ s : List (Letter I), ∃ h : wt D b.region s = a.region,
      f = psiWordAt (Sc := Sc) a.region b.region s h :=
  ⟨_, psiWordAt_weight f, psiWordAt_normal f⟩

/-- Computation of the `UGr` Hom map on an arbitrary linear representative. -/
@[simp] theorem psiMap₂_lin (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : LinDiagram k (ob D μ s) (ob D μ r)) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ s hs) (psiWordAt ν μ r hr)
      ((pres D Sc).lin x) = psiLin t cs ν μ hs hr x := by
  rw [psiMap₂_wordAt]
  exact psiQuotient_lin t ht cs ν μ hs hr x

/-- Computation of the `UGr` Hom map on an arbitrary diagram representative. -/
@[simp] theorem psiMap₂_diag (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (d : ob D μ s ⟶ ob D μ r) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ s hs) (psiWordAt ν μ r hr)
      ((pres D Sc).diag d) = psiDiagram t cs ν μ hs hr d := by
  rw [psiMap₂_wordAt]
  exact psiQuotient_diag t ht cs ν μ hs hr d

/-- Preservation of vertical identities on arbitrary `UGr` 1-morphisms. -/
@[simp] theorem psiMap₂_id (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    psiMap₂ t ht cs f f (𝟙 f) = 𝟙 (psiMap f) := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  rw [psiMap₂_wordAt]
  exact psiQuotient_id t ht cs a.region b.region hs

/-- Preservation of vertical composition on arbitrary `UGr` 2-morphisms. -/
theorem psiMap₂_comp (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g h : a ⟶ b} (x : f ⟶ g) (y : g ⟶ h) :
    psiMap₂ t ht cs f h (x ≫ y) = psiMap₂ t ht cs f g x ≫ psiMap₂ t ht cs g h y := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  obtain ⟨q, hq, rfl⟩ := exists_psiWordAt h
  simp only [psiMap₂_wordAt]
  exact psiQuotient_comp t ht cs a.region b.region hs hr hq x y

/-- Additivity on every `UGr` Hom space. -/
@[simp] theorem psiMap₂_add (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (x y : f ⟶ g) :
    psiMap₂ t ht cs f g (x + y) = psiMap₂ t ht cs f g x + psiMap₂ t ht cs f g y :=
  map_add _ _ _

/-- Scalar compatibility on every `UGr` Hom space. -/
@[simp] theorem psiMap₂_smul (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (c : k) (x : f ⟶ g) :
    psiMap₂ t ht cs f g (c • x) = c • psiMap₂ t ht cs f g x := map_smul _ _ _

/-- Parity preservation on every `UGr` Hom space. -/
theorem psiMap₂_mem_parity (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} {p : ZMod 2} {x : f ⟶ g}
    (hx : x ∈ parity (R := k) f g p) :
    psiMap₂ t ht cs f g x ∈ parity (R := k) (psiMap f) (psiMap g) p := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  rw [psiMap₂_wordAt]
  exact psiQuotient_mem_parity t ht cs a.region b.region hs hr hx

/-- Integer-degree preservation on every `UGr` Hom space. -/
theorem psiMap₂_mem_degree (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} {n : ℤ} {x : f ⟶ g}
    (hx : x ∈ GradedSupercategory.degree (R := k) f g n) :
    psiMap₂ t ht cs f g x ∈ GradedSupercategory.degree (R := k) (psiMap f) (psiMap g) n := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  rw [psiMap₂_wordAt]
  exact psiQuotient_mem_degree t ht cs a.region b.region hs hr hx

end OddMath.SKM
