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

instance modulePi : PiSupercategory k (Modules A) :=
  inferInstanceAs (PiSupercategory k (SuperBimodule A.grading (trivialGrading k)))

end OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
