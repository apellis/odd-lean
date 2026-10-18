import OddMath.SKM.Rho.Relations
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient Maps for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoTwo
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem homObj_normal {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    f.obj = ob D b.region (f.obj.word.map Col.l) := by
  obtain ⟨hw, hs⟩ := word_eq_wd (D := D) f.obj.start f.obj.word f.wf
  change f.obj.word = wd D f.obj.endR _ at hw
  change f.obj.start = wt D f.obj.endR _ at hs
  rw [f.endR_eq] at hw hs
  exact Obj.ext hs hw

theorem rhoLin_ker (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    LinearMap.ker ((pres D Sc).linMap (ob D μ s) (ob D μ r)) ≤
      LinearMap.ker (rhoLin (sy := sy) (hc := hc) t ν μ hs hr) := by
  intro x hx
  apply rhoLin_ideal t ht ν μ hs hr
  have h : (pres D Sc).lin x = (pres D Sc).lin 0 := by
    simpa only [LinearMap.mem_ker, Presentation.linMap_apply, Presentation.lin_zero] using hx
  simpa only [sub_zero] using ((pres D Sc).lin_eq_iff x 0).mp h

def rhoQuotient (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)) →ₗ[k]
      (rhoAt (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) :=
  let q := (pres D Sc).linMap (ob D μ s) (ob D μ r)
  ((LinearMap.ker q).liftQ (rhoLin t ν μ hs hr) (rhoLin_ker t ht ν μ hs hr)).comp
    (q.quotKerEquivOfSurjective (fun x => (pres D Sc).lin_surjective x)).symm.toLinearMap

@[simp] theorem rhoQuotient_lin (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : LinDiagram k (ob D μ s) (ob D μ r)) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr ((pres D Sc).lin x) =
      rhoLin t ν μ hs hr x := by
  change (LinearMap.ker _).liftQ _ (rhoLin_ker t ht ν μ hs hr)
    ((((pres D Sc).linMap _ _).quotKerEquivOfSurjective _).symm
      (((pres D Sc).linMap _ _) x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

@[simp] theorem rhoQuotient_diag (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (d : ob D μ s ⟶ ob D μ r) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr ((pres D Sc).diag d) =
      rhoDiagram t ν μ hs hr d := by
  change rhoQuotient t ht ν μ hs hr ((pres D Sc).lin (Finsupp.single d 1)) = _
  rw [rhoQuotient_lin, rhoLin_single, one_smul]

@[simp] theorem rhoQuotient_id (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s : List (Letter I)} (hs : wt D μ s = ν) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hs (𝟙 _) = 𝟙 _ := by
  rw [← (pres D Sc).diag_id, rhoQuotient_diag, rhoDiagram_id]

theorem rhoQuotient_comp (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r))
    (y : (pres D Sc).obj (ob D μ r) ⟶ (pres D Sc).obj (ob D μ q)) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hq (x ≫ y) =
      rhoQuotient t ht ν μ hs hr x ≫ rhoQuotient t ht ν μ hr hq y := by
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
  obtain ⟨y, rfl⟩ := (pres D Sc).lin_surjective y
  rw [← Presentation.lin_comp, rhoQuotient_lin, rhoQuotient_lin, rhoQuotient_lin]
  exact rhoLin_comp t ν μ hs hr hq x y

theorem rhoQuotient_mem_parity (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {p : ZMod 2} {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    (hx : x ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ p) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr x ∈ parity (R := k) _ _ p := by
  refine Presentation.homDeg_induction
    (motive := fun x => rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr x ∈
      parity (R := k) _ _ p) ?_ ?_ ?_ ?_ hx
  · intro d hd
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [degree_parity_mkD] at hd
    rw [rhoQuotient_diag, rhoDiagram_mkD, ← hd]
    exact rhoRaw_mem_parity t ν μ L hs hr hL
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem rhoQuotient_mem_degree (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {n : ℤ} {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    (hx : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ n) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr x ∈
      GradedSupercategory.degree (R := k) _ _ n := by
  refine Presentation.homDeg_induction
    (motive := fun x => rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr x ∈
      GradedSupercategory.degree (R := k) _ _ n) ?_ ?_ ?_ ?_ hx
  · intro d hd
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [degree_gdeg_mkD] at hd
    rw [rhoQuotient_diag, rhoDiagram_mkD, ← hd]
    exact rhoRaw_mem_degree t ν μ L hs hr hL
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem psiWordAt_weight {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    wt D b.region (f.obj.word.map Col.l) = a.region := by
  exact (congrArg Obj.start (homObj_normal f)).symm.trans f.start_eq

theorem psiWordAt_normal {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    f = psiWordAt (D := D) (Sc := Sc) a.region b.region (f.obj.word.map Col.l) (psiWordAt_weight f) := by
  exact Presentation.Bicat.Hom.ext (homObj_normal f)

private def rhoMap₂Transport {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (ef : f = f') (eg : g = g')
    (L : (f' ⟶ g') →ₗ[k] (rhoMap f' ⟶ rhoMap g')) :
    (f ⟶ g) →ₗ[k] (rhoMap f ⟶ rhoMap g) := by
  cases ef; cases eg; exact L

def rhoMap₂ (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (rhoMap f ⟶ rhoMap g) := by
  have ef := psiWordAt_normal f
  have eg := psiWordAt_normal g
  let Q := rhoQuotient (sy := sy) (hc := hc) t ht a.region b.region
    (psiWordAt_weight f) (psiWordAt_weight g)
  exact rhoMap₂Transport ef eg Q

private theorem rhoMap₂Transport_wordAt (t : k) (ht : t ^ 2 = -1)
    (ν μ : X) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν)
    (es : s = s') (er : r = r')
    (ef : psiWordAt (Sc := Sc) ν μ s hs = psiWordAt ν μ s' hs')
    (eg : psiWordAt (Sc := Sc) ν μ r hr = psiWordAt ν μ r' hr') :
    rhoMap₂Transport ef eg (rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs' hr') =
      rhoQuotient t ht ν μ hs hr := by
  cases es; cases er; rfl

@[simp] theorem rhoMap₂_wordAt (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    rhoMap₂ (sy := sy) (hc := hc) t ht (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) =
      rhoQuotient t ht ν μ hs hr := by
  exact rhoMap₂Transport_wordAt t ht ν μ hs hr _ _
    (wd_map_l (D := D) μ s).symm (wd_map_l (D := D) μ r).symm _ _

theorem exists_psiWordAt {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    ∃ s : List (Letter I), ∃ h : wt D b.region s = a.region,
      f = psiWordAt (Sc := Sc) a.region b.region s h :=
  ⟨_, psiWordAt_weight f, psiWordAt_normal f⟩

@[simp] theorem rhoMap₂_lin (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : LinDiagram k (ob D μ s) (ob D μ r)) :
    rhoMap₂ (sy := sy) (hc := hc) t ht (psiWordAt ν μ s hs) (psiWordAt ν μ r hr)
      ((pres D Sc).lin x) = rhoLin t ν μ hs hr x := by
  rw [rhoMap₂_wordAt]
  exact rhoQuotient_lin t ht ν μ hs hr x

@[simp] theorem rhoMap₂_diag (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (d : ob D μ s ⟶ ob D μ r) :
    rhoMap₂ (sy := sy) (hc := hc) t ht (psiWordAt ν μ s hs) (psiWordAt ν μ r hr)
      ((pres D Sc).diag d) = rhoDiagram t ν μ hs hr d := by
  rw [rhoMap₂_wordAt]
  exact rhoQuotient_diag t ht ν μ hs hr d

@[simp] theorem rhoMap₂_id (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    rhoMap₂ t ht f f (𝟙 f) = 𝟙 (rhoMap f) := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  rw [rhoMap₂_wordAt]
  exact rhoQuotient_id (D := D) (Sc := Sc) t ht a.region b.region hs

theorem rhoMap₂_comp (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g h : a ⟶ b} (x : f ⟶ g) (y : g ⟶ h) :
    rhoMap₂ t ht f h (x ≫ y) = rhoMap₂ t ht f g x ≫ rhoMap₂ t ht g h y := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  obtain ⟨q, hq, rfl⟩ := exists_psiWordAt h
  simp only [rhoMap₂_wordAt]
  exact rhoQuotient_comp (D := D) (Sc := Sc) t ht a.region b.region hs hr hq x y

@[simp] theorem rhoMap₂_add (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (x y : f ⟶ g) :
    rhoMap₂ t ht f g (x + y) = rhoMap₂ t ht f g x + rhoMap₂ t ht f g y :=
  map_add _ _ _

@[simp] theorem rhoMap₂_smul (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (c : k) (x : f ⟶ g) :
    rhoMap₂ t ht f g (c • x) = c • rhoMap₂ t ht f g x := map_smul _ _ _

theorem rhoMap₂_mem_parity (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} {p : ZMod 2} {x : f ⟶ g}
    (hx : x ∈ parity (R := k) f g p) :
    rhoMap₂ t ht f g x ∈ parity (R := k) (rhoMap f) (rhoMap g) p := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  rw [rhoMap₂_wordAt]
  exact rhoQuotient_mem_parity (D := D) (Sc := Sc) t ht a.region b.region hs hr hx

theorem rhoMap₂_mem_degree (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} {n : ℤ} {x : f ⟶ g}
    (hx : x ∈ GradedSupercategory.degree (R := k) f g n) :
    rhoMap₂ t ht f g x ∈ GradedSupercategory.degree (R := k) (rhoMap f) (rhoMap g) n := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  rw [rhoMap₂_wordAt]
  exact rhoQuotient_mem_degree (D := D) (Sc := Sc) t ht a.region b.region hs hr hx

end OddMath.SKM.RhoTwo
