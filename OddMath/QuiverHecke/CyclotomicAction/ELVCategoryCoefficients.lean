/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupport
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ModuleCoefficients

/-! # Coefficient image on exact-content ELV supermodules

Central families on the full exact-content source category act on all its
supermodules. The integer grading is transported only to this coefficient
image; no grading of arbitrary module morphisms is asserted. Finite-colour
source support yields a joint nilpotent coefficient ideal at each content.
Literal local-inverse reservoir closures and their residual identifications
remain separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)

abbrev ContentCoefficient :=
  Superfunctor.id k (ContentCategory D Sc cutoff N β) ⟶
    Superfunctor.id k (ContentCategory D Sc cutoff N β)

def contentRealize (c : ContentCoefficient D Sc cutoff N β) :
    Superfunctor.id k (ContentModules D Sc cutoff N β) ⟶
      Superfunctor.id k (ContentModules D Sc cutoff N β) where
  app p M := Superfunctor.whiskerRight (proj k p c) M
  app_mem p M := Superfunctor.whiskerRight_mem (proj_mem p c) M
  naturality p M L q f hf := by
    have he := Superfunctor.whisker_exchange (proj_mem p c) hf
    have he' := congrArg (fun z => koszulSign p q • z) he
    rw [koszulSign_smul_smul] at he'
    apply Superfunctor.hom_ext
    intro r v
    exact congrArg (fun t => t.app r v) he'.symm

theorem contentRealize_total (c : ContentCoefficient D Sc cutoff N β)
    (M : ContentModules D Sc cutoff N β) :
    (contentRealize D Sc cutoff N β c).total M = Superfunctor.whiskerRight c M := by
  change Superfunctor.whiskerRight (proj k 0 c) M +
    Superfunctor.whiskerRight (proj k 1 c) M = _
  rw [← Superfunctor.add_whiskerRight, proj_add_proj]

def contentRealizeLinear : ContentCoefficient D Sc cutoff N β →ₗ[k]
    (Superfunctor.id k (ContentModules D Sc cutoff N β) ⟶
      Superfunctor.id k (ContentModules D Sc cutoff N β)) where
  toFun := contentRealize D Sc cutoff N β
  map_add' c d := by
    apply Superfunctor.hom_ext
    intro p M
    change Superfunctor.whiskerRight (proj k p (c + d)) M = _
    rw [map_add, Superfunctor.add_whiskerRight]
    rfl
  map_smul' r c := by
    apply Superfunctor.hom_ext
    intro p M
    change Superfunctor.whiskerRight (proj k p (r • c)) M = _
    rw [map_smul, Superfunctor.smul_whiskerRight]
    rfl

private theorem contentTotal_ext
    {x y : Superfunctor.id k (ContentModules D Sc cutoff N β) ⟶
      Superfunctor.id k (ContentModules D Sc cutoff N β)}
    (h : ∀ M, x.total M = y.total M) : x = y := by
  apply Superfunctor.hom_ext
  intro p M
  have hp (t : Superfunctor.id k (ContentModules D Sc cutoff N β) ⟶
      Superfunctor.id k (ContentModules D Sc cutoff N β)) :
      proj k p (t.total M) = t.app p M := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (t.app_mem 0 M) (t.app_mem 1 M)
    · exact proj_eq_of_add (add_comm _ _) (t.app_mem 1 M) (by simpa using t.app_mem 0 M)
  rw [← hp x, ← hp y, h M]

theorem contentRealize_comp (c d : ContentCoefficient D Sc cutoff N β) :
    contentRealize D Sc cutoff N β (c ≫ d) =
      contentRealize D Sc cutoff N β c ≫ contentRealize D Sc cutoff N β d := by
  apply contentTotal_ext
  intro M
  rw [Superfunctor.comp_total, contentRealize_total, contentRealize_total, contentRealize_total]
  exact Superfunctor.comp_whiskerRight c d M

theorem contentRealize_mem {p : ZMod 2} {c : ContentCoefficient D Sc cutoff N β}
    (hc : c ∈ parity (R := k) _ _ p) :
    contentRealize D Sc cutoff N β c ∈ parity (R := k) _ _ p := by
  rw [Superfunctor.mem_parity_iff]
  funext M
  change Superfunctor.whiskerRight (proj k (p + 1) c) M = 0
  rw [proj_of_mem_ne hc (Ne.symm (zmod2_add_one_ne p))]
  exact Superfunctor.hom_ext fun q v => M.toFunctor.map_zero v v

theorem contentRealize_proj (p : ZMod 2) (c : ContentCoefficient D Sc cutoff N β) :
    contentRealize D Sc cutoff N β (proj k p c) =
      proj k p (contentRealize D Sc cutoff N β c) := by
  symm
  apply proj_eq_of_add (h := contentRealize D Sc cutoff N β (proj k (p + 1) c))
  · change contentRealizeLinear D Sc cutoff N β c =
      contentRealizeLinear D Sc cutoff N β (proj k p c) +
        contentRealizeLinear D Sc cutoff N β (proj k (p + 1) c)
    rw [← map_add, proj_add_proj_add_one]
  · exact contentRealize_mem D Sc cutoff N β (proj_mem _ _)
  · exact contentRealize_mem D Sc cutoff N β (proj_mem _ _)

theorem contentRealize_id : contentRealize D Sc cutoff N β (𝟙 _) = 𝟙 _ := by
  apply contentTotal_ext
  intro M
  rw [contentRealize_total, Superfunctor.id_whiskerRight]
  change 𝟙 M = 𝟙 M + 0
  exact (add_zero _).symm

def contentModulePiIso (M : ContentModules D Sc cutoff N β) :
    M.comp (PiSCat.piHom (PiSCat.of k (SVec.{u} k))) ≅ M where
  hom := Superfunctor.whiskerLeft M (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).hom
  inv := Superfunctor.whiskerLeft M (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).inv
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro p v
    exact congrArg (fun t => t.app p (M.obj v))
      (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).hom_inv_id
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p v
    have h := congrArg (fun t => t.app p (M.obj v))
      (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).inv_hom_id
    exact h

instance contentModulesPi : PiSupercategory k (ContentModules D Sc cutoff N β) :=
  PiSupercategory.ofIso _ (contentModulePiIso D Sc cutoff N β) (fun M =>
    Superfunctor.whiskerLeft_mem M
      (PiTwoSupercategory.ζ_hom_mem (R := k) (PiSCat.of k (SVec.{u} k))))

abbrev contentModuleTarget : PiSCat k := PiSCat.of k (ContentModules D Sc cutoff N β)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- Integer degrees of source central families; only these coefficients are graded. -/
def contentCoefficientDegree (n : ℤ) : Submodule k (ContentCoefficient D Sc cutoff N β) :=
  letI := contentGradedSupercategory D Sc cutoff N sy hc β
  GradedSuperfunctor.degNat
    (GradedSuperfunctor.id k (ContentCategory D Sc cutoff N β))
    (GradedSuperfunctor.id k (ContentCategory D Sc cutoff N β)) n

/-- The image of the source coefficient degree on the exact-content module target. -/
def contentModuleCoeffGrading :
    SwappedAssembly.ProbeWindow.CoeffGrading k (contentModuleTarget D Sc cutoff N β) where
  deg n := {t | ∃ c ∈ contentCoefficientDegree D Sc cutoff N β sy hc n,
    contentRealize D Sc cutoff N β c = t}
  id_mem := by
    let := contentGradedSupercategory D Sc cutoff N sy hc β
    refine ⟨_, ?_, contentRealize_id D Sc cutoff N β⟩
    intro p v
    change (if p = 0 then 𝟙 v else 0) ∈ GradedSupercategory.degree (R := k) v v 0
    split_ifs
    · exact GradedSupercategory.id_mem_degree v
    · exact Submodule.zero_mem _
  comp_mem := by
    let := contentGradedSupercategory D Sc cutoff N sy hc β
    rintro m n x y ⟨c, hc', rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c ≫ d, ?_, contentRealize_comp D Sc cutoff N β c d⟩
    intro p v
    change (c ≫ d).app p v ∈ GradedSupercategory.degree (R := k) v v (m + n)
    rw [Superfunctor.comp_app]
    exact Submodule.add_mem _ (GradedSupercategory.comp_mem_degree (hc' 0 v) (hd p v))
      (GradedSupercategory.comp_mem_degree (hc' 1 v) (hd _ v))
  proj_mem := by
    let := contentGradedSupercategory D Sc cutoff N sy hc β
    rintro n p x ⟨c, hc', rfl⟩
    refine ⟨proj k p c, ?_, contentRealize_proj D Sc cutoff N β p c⟩
    intro q v
    change (proj k p c).app q v ∈ GradedSupercategory.degree (R := k) v v n
    rw [Superfunctor.proj_app]
    split_ifs
    · exact hc' p v
    · exact Submodule.zero_mem _

/-- One threshold for all words of the fixed content, not for an entire weight fibre. -/
theorem contentCategory_end_bounded [Finite I] :
    ∃ K : ℕ, ∀ (v : ContentCategory D Sc cutoff N β) (n : ℤ), (K : ℤ) ≤ n →
      truncatedDegree D Sc cutoff sy hc N v.obj.word v.obj.word n = ⊥ := by
  classical
  choose B hB using fun v : List I => truncatedContent_bounded D Sc cutoff sy hc N v v
  let S := β.toList.permutations.toFinset
  refine ⟨S.sup B + 1, fun v n hn => hB v.obj.word n (Or.inr ?_)⟩
  have hv : v.obj.word ∈ S := by
    change v.obj.word ∈ β.toList.permutations.toFinset
    simp only [List.mem_toFinset, List.mem_permutations]
    apply Multiset.coe_eq_coe.mp
    exact v.content.trans (Multiset.coe_toList β).symm
  have hle := Finset.le_sup (f := B) hv
  have hle' : (B v.obj.word : ℤ) ≤ ((S.sup B : ℕ) : ℤ) := by exact_mod_cast hle
  omega

/-- Source support annihilates every high-degree central family simultaneously. -/
theorem contentCoefficient_eq_zero [Finite I] (n : ℤ)
    (hn : ((contentCategory_end_bounded D Sc cutoff N β sy hc).choose : ℤ) ≤ n)
    (c : ContentCoefficient D Sc cutoff N β)
    (h : c ∈ contentCoefficientDegree D Sc cutoff N β sy hc n) : c = 0 := by
  apply Superfunctor.hom_ext
  intro p v
  have hv := h p v
  change c.app p v ∈ truncatedDegree D Sc cutoff sy hc N v.obj.word v.obj.word n at hv
  rw [(contentCategory_end_bounded D Sc cutoff N β sy hc).choose_spec v n hn] at hv
  exact hv

/-- High-degree coefficients vanish on the same all-module category as content E and F. -/
theorem contentModule_coefficient_eq_zero [Finite I] (n : ℤ)
    (hn : ((contentCategory_end_bounded D Sc cutoff N β sy hc).choose : ℤ) ≤ n)
    (t : 𝟙 (contentModuleTarget D Sc cutoff N β) ⟶ 𝟙 (contentModuleTarget D Sc cutoff N β))
    (ht : t ∈ (contentModuleCoeffGrading D Sc cutoff N β sy hc).deg n) : t = 0 := by
  obtain ⟨c, hc', rfl⟩ := ht
  rw [contentCoefficient_eq_zero D Sc cutoff N β sy hc n hn c hc']
  exact (contentRealizeLinear D Sc cutoff N β).map_zero

/-- Jointly nilpotent coefficient ideal on functors into the exact-content module category. -/
def contentModuleCoefficientIdeal [Finite I] (T : PiSCat k) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal (T ⟶ contentModuleTarget D Sc cutoff N β) :=
  SwappedAssembly.ProbeWindow.reservoirCoefficientIdeal T
    (contentModuleCoeffGrading D Sc cutoff N β sy hc)
    (contentCategory_end_bounded D Sc cutoff N β sy hc).choose
    (contentModule_coefficient_eq_zero D Sc cutoff N β sy hc)

end OddMath.QuiverHecke.ELVOld
