/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.RegularCoefficientBound
import StringDiagrams.Super.FunctorCategory

/-! # Regular coefficients acting on module superfunctors

For `SwappedHomInversion.md` §4, realize regular-bimodule coefficients on the identity
superfunctor of `A-SMod-k`. The action retains the balanced tensor unitors and odd
supernaturality. This is a coefficient comparison, not a construction of the ELV action.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u
variable {k : Type u} [CommRing k]

/-- The ground ring as a purely even superalgebra. -/
abbrev scalarAlg : SuperAlg k where
  carrier := k
  grading := trivialGrading k

/-- The module category used for the coefficient realization. -/
abbrev Modules (A : GSuperAlg k) := scalarAlg (k := k) ⟶ A.toSuperAlg

variable (A : GSuperAlg k)

/-- The unit-conjugated coefficient action preserves parity. -/
theorem postCoeff_mem (M : Modules A) {p : ZMod 2}
    {c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg}
    (hc : c ∈ parity (R := k) _ _ p) :
    ProbeWindow.postCoeff M c ∈ parity (R := k) M M p := by
  change (SuperBimodule.leftUnitor M).inv ≫ SuperBimodule.whiskerRight c M ≫
    (SuperBimodule.leftUnitor M).hom ∈ parity (R := k) M M p
  simpa only [zero_add, add_zero] using
    comp_mem (inv_mem (SuperBimodule.leftUnitor M) (SuperBimodule.leftUnitor_hom_mem M))
      (comp_mem (SuperBimodule.whiskerRight_mem _ hc M)
        (SuperBimodule.leftUnitor_hom_mem M))

/-- Realize a coefficient on the identity module superfunctor. -/
def realize (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) :
    Superfunctor.id k (Modules A) ⟶ Superfunctor.id k (Modules A) where
  app p M := ProbeWindow.postCoeff M (proj k p c)
  app_mem p M := postCoeff_mem A M (proj_mem p c)
  naturality p M N q f hf := by
    exact (ProbeWindow.comp_postCoeff hf (proj_mem p c)).trans
      (by rw [koszulSign_comm]; rfl)

/-- The total component is the balanced tensor action with its unitors. -/
theorem realize_total (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) (M : Modules A) :
    (realize A c).total M = ProbeWindow.postCoeff M c := by
  change ProbeWindow.postCoeff M (proj k 0 c) + ProbeWindow.postCoeff M (proj k 1 c) = _
  rw [← ProbeWindow.postCoeff_add (k := k), proj_add_proj]

/-- The action on a module vector is left multiplication by the value at the unit. -/
theorem postCoeff_apply (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg)
    (M : Modules A) (x : M.toSVec) :
    (ProbeWindow.postCoeff M c).1 x = M.lact (c.1 (1 : A)) x := by
  change (SuperBimodule.leftUnitor M).hom.1
    ((SuperBimodule.whiskerRight c M).1
      (SuperBimodule.btmul (SuperBimodule.regular A.grading) M (1 : A) x)) = _
  exact (congrArg (fun y => (SuperBimodule.leftUnitor M).hom.1 y)
    (SuperBimodule.whiskerRight_btmul c M (1 : A) x)).trans
      (SuperBimodule.leftUnitorHom_btmul M _ _)

/-- The left regular module, with the right ground-ring action. -/
def regularModule : Modules A where
  toSVec := (SuperBimodule.regular A.grading).toSVec
  lact := (SuperBimodule.regular A.grading).lact
  ract :=
    { toFun := fun r => r • 𝟙 _
      map_add' := fun r s => add_smul r s _
      map_smul' := fun r s => mul_smul r s _ }
  lact_one := (SuperBimodule.regular A.grading).lact_one
  lact_mul := (SuperBimodule.regular A.grading).lact_mul
  ract_one := one_smul _ _
  ract_mul r s := by simp [Linear.comp_smul, smul_smul, mul_comm]
  lact_ract a r := by simp [Linear.smul_comp, Linear.comp_smul]
  lact_mem := (SuperBimodule.regular A.grading).lact_mem
  ract_mem p r hr := by
    by_cases hp : p = 0
    · subst p; exact Submodule.smul_mem _ r (id_mem _)
    · have hr0 : r = 0 := by simpa [scalarAlg, trivialGrading, hp] using hr
      subst r; simp

/-- Faithfulness of the coefficient realization is detected on the regular module at `1`. -/
theorem realize_injective : Function.Injective (realize A) := by
  intro c d h
  have htotal := congrArg (fun t => t.total (regularModule A)) h
  rw [realize_total, realize_total] at htotal
  have he := congrArg (fun f => f.1 (1 : A)) htotal
  have he := (postCoeff_apply A c (regularModule A) (1 : A)).symm.trans
    (he.trans (postCoeff_apply A d (regularModule A) (1 : A)))
  change (show A from c.1 (1 : A)) * 1 = (show A from d.1 (1 : A)) * 1 at he
  simp only [mul_one] at he
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro x
  exact (regular_apply A c x).trans
    ((congrArg (fun z : A => z * (show A from x)) he).trans (regular_apply A d x).symm)

private theorem total_ext
    {x y : Superfunctor.id k (Modules A) ⟶ Superfunctor.id k (Modules A)}
    (h : ∀ M, x.total M = y.total M) : x = y := by
  apply SuperNatTrans.ext
  funext p M
  have hp (t : Superfunctor.id k (Modules A) ⟶ Superfunctor.id k (Modules A)) :
      proj k p (t.total M) = t.app p M := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (t.app_mem 0 M) (t.app_mem 1 M)
    · exact proj_eq_of_add (add_comm _ _) (t.app_mem 1 M)
        (by simpa using t.app_mem 0 M)
  rw [← hp x, ← hp y, h M]

/-- Linear realization of regular coefficients as module supernatural transformations. -/
def realizeLinear : (𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) →ₗ[k]
    (Superfunctor.id k (Modules A) ⟶ Superfunctor.id k (Modules A)) where
  toFun := realize A
  map_add' c d := by
    apply SuperNatTrans.ext; funext p M
    change ProbeWindow.postCoeff M (proj k p (c + d)) = _
    rw [map_add, ProbeWindow.postCoeff_add (k := k)]
    rfl
  map_smul' r c := by
    apply SuperNatTrans.ext; funext p M
    change ProbeWindow.postCoeff M (proj k p (r • c)) = _
    rw [map_smul]
    change (SuperBimodule.leftUnitor M).inv ≫
      SuperBimodule.whiskerRight (r • proj k p c) M ≫ (SuperBimodule.leftUnitor M).hom =
      r • ((SuperBimodule.leftUnitor M).inv ≫
        SuperBimodule.whiskerRight (proj k p c) M ≫ (SuperBimodule.leftUnitor M).hom)
    rw [SuperBimodule.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

/-- Composition is transported with the original unitors, without an extra sign. -/
theorem realize_comp (c d : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) :
    realize A (c ≫ d) = realize A c ≫ realize A d := by
  apply total_ext A; intro M
  rw [Superfunctor.comp_total, realize_total, realize_total, realize_total]
  exact ProbeWindow.postCoeff_comp (k := k) _ _ _

/-- Homogeneous coefficients realize homogeneous supernatural transformations. -/
theorem realize_mem {p : ZMod 2} {c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg}
    (hc : c ∈ parity (R := k) _ _ p) :
    realize A c ∈ parity (R := k) _ _ p := by
  rw [Superfunctor.mem_parity_iff]
  funext M
  change ProbeWindow.postCoeff M (proj k (p + 1) c) = 0
  rw [proj_of_mem_ne hc (Ne.symm (zmod2_add_one_ne p))]
  exact ProbeWindow.postCoeff_zero (k := k) M

/-- Realization commutes with parity projection, including the odd component. -/
theorem realize_proj (p : ZMod 2) (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) :
    realize A (proj k p c) = proj k p (realize A c) := by
  symm
  apply proj_eq_of_add (h := realize A (proj k (p + 1) c))
  · change realizeLinear A c = realizeLinear A (proj k p c) +
      realizeLinear A (proj k (p + 1) c)
    rw [← map_add, proj_add_proj_add_one]
  · exact realize_mem A (proj_mem _ _)
  · exact realize_mem A (proj_mem _ _)

/-- Explicit algebra support forces high-degree realized module coefficients to vanish. -/
theorem realize_eq_zero_of_high_degree (K : ℕ)
    (hK : ∀ d : ℤ, (K : ℤ) ≤ d → A.degree d = ⊥) {d : ℤ}
    (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg)
    (hc : c ∈ (coeffGrading A).deg d) (hd : (K : ℤ) ≤ d) : realize A c = 0 := by
  rw [coefficient_eq_zero A K hK d hd c hc]
  exact (realizeLinear A).map_zero

instance modulePi : PiSupercategory k (Modules A) :=
  inferInstanceAs (PiSupercategory k (SuperBimodule A.grading (trivialGrading k)))

/-- The module target in the same `Π-SCat` used by the swapped Hom sectors. -/
abbrev moduleTarget : PiSCat k := PiSCat.of k (Modules A)

/-- Realization preserves the identity, with unitors retained in its definition. -/
theorem realize_id : realize A (𝟙 (𝟙 A.toSuperAlg)) = 𝟙 (Superfunctor.id k (Modules A)) := by
  apply total_ext A; intro M
  rw [realize_total, ProbeWindow.postCoeff_id (k := k)]
  change 𝟙 M = 𝟙 M + 0
  exact (add_zero _).symm

/-- The image grading of regular coefficients on the actual module identity superfunctor.
No grading of arbitrary superfunctors or surjectivity onto the whole center is assumed. -/
def moduleCoeffGrading : ProbeWindow.CoeffGrading k (moduleTarget A) where
  deg n := {t | ∃ c ∈ (coeffGrading A).deg n, realize A c = t}
  id_mem := ⟨_, (coeffGrading A).id_mem, realize_id A⟩
  comp_mem := by
    rintro m n x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c ≫ d, (coeffGrading A).comp_mem hc hd, realize_comp A c d⟩
  proj_mem := by
    rintro n p x ⟨c, hc, rfl⟩
    exact ⟨proj k p c, (coeffGrading A).proj_mem p hc, realize_proj A p c⟩

/-- Algebra support, rather than an assumed functor-coefficient bound, kills the image grading. -/
theorem module_coefficient_eq_zero (K : ℕ)
    (hK : ∀ d : ℤ, (K : ℤ) ≤ d → A.degree d = ⊥)
    (d : ℤ) (hd : (K : ℤ) ≤ d)
    (t : 𝟙 (moduleTarget A) ⟶ 𝟙 (moduleTarget A))
    (ht : t ∈ (moduleCoeffGrading A).deg d) : t = 0 := by
  obtain ⟨c, hc, rfl⟩ := ht
  exact realize_eq_zero_of_high_degree A K hK c hc hd

/-- A jointly nilpotent ideal on module **superfunctors** from any probe Π-supercategory.
This is the concrete bridge from regular bimodule support to the swapped action's target. -/
def moduleCoefficientIdeal (T : PiSCat k) (K : ℕ)
    (hK : ∀ d : ℤ, (K : ℤ) ≤ d → A.degree d = ⊥) :
    ProbeWindow.CoefficientIdeal (T ⟶ moduleTarget A) :=
  ProbeWindow.reservoirCoefficientIdeal T (moduleCoeffGrading A) K
    (module_coefficient_eq_zero A K hK)

end OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
