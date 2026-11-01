import OddMath.QuiverHecke.CyclotomicAction.ProbeHeightDotInverse
import OddMath.QuiverHecke.CyclotomicAction.SuperDot
import StringDiagrams.Super.Parity

/-! # Signed inverse of the probe induction dot at every height

This supplies the dot input of `docs/Nondegeneracy/InvertibleDotProbe.md`,
Section 5, equation (6), on the existing height action including the vacuum.

The right inverse in the append corner acts on the literal induction ideal.
The underlying inverse is right multiplication by X followed by the parity
sign. Its SVec isomorphism gives inverse parity through Supercategory.inv_mem;
the inverse then satisfies the actual superbimodule Hom equations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (m : I → ℕ)
  (ha : CyclotomicPolynomialParity D (probePolynomial (k := k) (probeDotExponent D) m)) (n : ℕ)
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "P" => heightInductionCorner D Sc i a ha n
local notation "GB" => heightParity D Sc a ha (n+1)
local notation "e" => heightAppend D Sc a i n 1
local notation "c" => heightLastDot D Sc a i n
local notation "Xinv" => Subtype.val (probeHeightAppendDotInverse D Sc i m n)
local notation "d" => D.parity i

private theorem probe_rightDot_mem (x : heightAlgebra D Sc a (n+1))
    (_hx : x ∈ heightInductionCornerSubmodule D Sc i a n) :
    x*c ∈ heightInductionCornerSubmodule D Sc i a n := by
  change (x*c)*e=x*c
  rw [mul_assoc, (heightLastDot_corner D Sc a i n).2]

private theorem probe_rightInv_mem (x : heightAlgebra D Sc a (n+1))
    (_hx : x ∈ heightInductionCornerSubmodule D Sc i a n) :
    x*Xinv ∈ heightInductionCornerSubmodule D Sc i a n := by
  have hX := ((Subsemigroup.mem_corner_iff (probeHeightAppendIdempotent D Sc i a n)).mp
    (probeHeightAppendDotInverse D Sc i m n).property).2
  change (x*Xinv)*e=x*Xinv
  rw [mul_assoc, hX]

private def probeRightDotLinear : (P).toSVec ⟶ (P).toSVec :=
  SVec.restrictHom ((SuperBimodule.regular GB).ract c) (probe_rightDot_mem D Sc i m n)

private def probeRightInvLinear : (P).toSVec ⟶ (P).toSVec :=
  SVec.restrictHom ((SuperBimodule.regular GB).ract Xinv) (probe_rightInv_mem D Sc i m n)

private theorem probeRightDot_inv : probeRightDotLinear D Sc i m ha n ≫
    probeRightInvLinear D Sc i m ha n = 𝟙 (P).toSVec := by
  apply SVec.hom_ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun z : ProbeHeightAppendCorner D Sc i a n => z.val)
    (probeHeightAppendLastDot_mul_inverse D Sc i m n)
  change c*Xinv=e at h
  change (x.val*c)*Xinv=x.val
  rw [mul_assoc, h]
  exact x.property

private theorem probeRightInv_dot : probeRightInvLinear D Sc i m ha n ≫
    probeRightDotLinear D Sc i m ha n = 𝟙 (P).toSVec := by
  apply SVec.hom_ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun z : ProbeHeightAppendCorner D Sc i a n => z.val)
    (probeHeightAppendLastDot_inverse_mul D Sc i m n)
  change Xinv*c=e at h
  change (x.val*Xinv)*c=x.val
  rw [mul_assoc, h]
  exact x.property

private theorem probeSign_sq :
    SVec.ofHom ((P).toSVec.sgn d) ≫ SVec.ofHom ((P).toSVec.sgn d) = 𝟙 (P).toSVec := by
  apply SVec.hom_ext
  intro x
  exact SVec.sgn_sgn_apply (P).toSVec d x

/-- The actual inverse applies right multiplication before the parity sign. -/
def probeHeightInductionDotInverseLinear : (P).toSVec ⟶ (P).toSVec :=
  probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom ((P).toSVec.sgn d)

def probeHeightInductionDotSVecIso : (P).toSVec ≅ (P).toSVec where
  hom := heightInductionDotLinear D Sc i a ha n
  inv := probeHeightInductionDotInverseLinear D Sc i m ha n
  hom_inv_id := by
    change (SVec.ofHom ((P).toSVec.sgn d) ≫ probeRightDotLinear D Sc i m ha n) ≫
      (probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom ((P).toSVec.sgn d)) = _
    calc
      _ = SVec.ofHom ((P).toSVec.sgn d) ≫
          ((probeRightDotLinear D Sc i m ha n ≫ probeRightInvLinear D Sc i m ha n) ≫
            SVec.ofHom ((P).toSVec.sgn d)) := by simp only [Category.assoc]
      _ = _ := by rw [probeRightDot_inv, Category.id_comp, probeSign_sq]
  inv_hom_id := by
    change (probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom ((P).toSVec.sgn d)) ≫
      (SVec.ofHom ((P).toSVec.sgn d) ≫ probeRightDotLinear D Sc i m ha n) = _
    calc
      _ = probeRightInvLinear D Sc i m ha n ≫
          ((SVec.ofHom ((P).toSVec.sgn d) ≫ SVec.ofHom ((P).toSVec.sgn d)) ≫
            probeRightDotLinear D Sc i m ha n) := by simp only [Category.assoc]
      _ = _ := by rw [probeSign_sq, Category.id_comp, probeRightInv_dot]

theorem probeHeightInductionDotInverse_parity :
    probeHeightInductionDotInverseLinear D Sc i m ha n ∈ SVec.parityHom (P).toSVec (P).toSVec d :=
  inv_mem (probeHeightInductionDotSVecIso D Sc i m ha n) (heightInductionDotLinear_parity D Sc i a ha n)

theorem probeHeightInductionDotInverse_isHom :
    SuperBimodule.IsHom P P (probeHeightInductionDotInverseLinear D Sc i m ha n) := by
  let E := probeHeightInductionDotSVecIso D Sc i m ha n
  have hf := (SuperBimodule.isHom_iff_of_mem (heightInductionDotLinear_parity D Sc i a ha n)).1
    (heightInductionDotLinear_isHom D Sc i a ha n)
  apply (SuperBimodule.isHom_iff_of_mem (probeHeightInductionDotInverse_parity D Sc i m ha n)).2
  constructor
  · intro p b hb
    change (P).lact b ≫ E.inv = sign k (p*d) • (E.inv ≫ (P).lact b)
    have hl : (P).lact b ≫ E.hom = sign k (p*d) • (E.hom ≫ (P).lact b) := hf.1 p b hb
    have hl' : E.hom ≫ (P).lact b = sign k (p*d) • ((P).lact b ≫ E.hom) := by
      rw [hl, smul_smul, Supercategory.sign_mul_self, one_smul]
    apply (cancel_epi E.hom).1
    calc
      E.hom ≫ ((P).lact b ≫ E.inv) = (E.hom ≫ (P).lact b) ≫ E.inv :=
        (Category.assoc _ _ _).symm
      _ = (sign k (p*d) • ((P).lact b ≫ E.hom)) ≫ E.inv := by rw [hl']
      _ = sign k (p*d) • ((P).lact b ≫ (E.hom ≫ E.inv)) := by
        rw [Linear.smul_comp, Category.assoc]
      _ = sign k (p*d) • (P).lact b := by rw [E.hom_inv_id, Category.comp_id]
      _ = E.hom ≫ (sign k (p*d) • (E.inv ≫ (P).lact b)) := by
        rw [Linear.comp_smul, ← Category.assoc, E.hom_inv_id, Category.id_comp]
  · intro r
    change (P).ract r ≫ E.inv = E.inv ≫ (P).ract r
    have hr : (P).ract r ≫ E.hom = E.hom ≫ (P).ract r := hf.2 r
    apply (cancel_epi E.hom).1
    calc
      E.hom ≫ ((P).ract r ≫ E.inv) = (E.hom ≫ (P).ract r) ≫ E.inv :=
        (Category.assoc _ _ _).symm
      _ = ((P).ract r ≫ E.hom) ≫ E.inv := by rw [← hr]
      _ = (P).ract r := by rw [Category.assoc, E.hom_inv_id, Category.comp_id]
      _ = E.hom ≫ (E.inv ≫ (P).ract r) := by
        rw [← Category.assoc, E.hom_inv_id, Category.id_comp]

/-- The existing signed induction dot has this actual superbimodule inverse. -/
def probeHeightInductionSuperDotIso : P ≅ P where
  hom := heightInductionSuperDot D Sc i a ha n
  inv := ⟨probeHeightInductionDotInverseLinear D Sc i m ha n,
    probeHeightInductionDotInverse_isHom D Sc i m ha n⟩
  hom_inv_id := Subtype.ext (probeHeightInductionDotSVecIso D Sc i m ha n).hom_inv_id
  inv_hom_id := Subtype.ext (probeHeightInductionDotSVecIso D Sc i m ha n).inv_hom_id

theorem probeHeightInductionSuperDotInverse_parity :
    (probeHeightInductionSuperDotIso D Sc i m ha n).inv ∈ parity (R := k) P P d :=
  SuperBimodule.mem_parity_iff.2 (probeHeightInductionDotInverse_parity D Sc i m ha n)

/-- On a homogeneous element the inverse is exactly the signed-right inverse,
including the additional colour parity sign in the odd case. -/
theorem probeHeightInductionSuperDotInverse_apply {p : ZMod 2} (x : (P).toSVec)
    (hx : x ∈ (P).toSVec.part p) :
    (((probeHeightInductionSuperDotIso D Sc i m ha n).inv).1 x).val =
      sign k (d + p*d) • (x.val * Xinv) := by
  have hRI : probeRightInvLinear D Sc i m ha n ∈ parity (R := k) (P).toSVec (P).toSVec d := by
    have h := comp_mem (probeHeightInductionDotInverse_parity D Sc i m ha n) (SVec.sgn_mem (P).toSVec d)
    have heq : probeHeightInductionDotInverseLinear D Sc i m ha n ≫
        SVec.ofHom ((P).toSVec.sgn d) = probeRightInvLinear D Sc i m ha n := by
      change (probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom ((P).toSVec.sgn d)) ≫
        SVec.ofHom ((P).toSVec.sgn d) = _
      rw [Category.assoc, probeSign_sq, Category.comp_id]
    rw [heq] at h
    simpa only [add_zero] using h
  have h := LinearMap.congr_fun (SVec.sgn_comp_of_mem hRI d) x
  change probeHeightInductionDotInverseLinear D Sc i m ha n x =
    sign k (d*d) • probeRightInvLinear D Sc i m ha n ((P).toSVec.sgn d x) at h
  rw [parity_sq] at h
  have hv := congrArg (fun z : (P).toSVec => z.val) h
  change (((probeHeightInductionSuperDotIso D Sc i m ha n).inv).1 x).val =
    sign k d • (((P).toSVec.sgn d x).val * Xinv) at hv
  rw [SVec.sgn_apply_of_mem d hx] at hv
  change (((probeHeightInductionSuperDotIso D Sc i m ha n).inv).1 x).val =
    sign k d • ((sign k (p*d) • x.val) * Xinv) at hv
  rw [smul_mul_assoc, smul_smul, ← sign_add] at hv
  exact hv


/-- The inverse as a supernatural transformation of the existing balanced
tensor induction functor. Only its induction-colour parity component is nonzero. -/
def probeHeightSuperDotInverse :
    SuperNatTrans k (heightSuperInduction D Sc i a ha n)
      (heightSuperInduction D Sc i a ha n) where
  app p M := if p=d then
    SuperBimodule.whiskerRight (probeHeightInductionSuperDotIso D Sc i m ha n).inv M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact SuperBimodule.whiskerRight_mem P
        (probeHeightInductionSuperDotInverse_parity D Sc i m ha n) M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    change SuperBimodule.whiskerLeft P f ≫
      (if p=d then SuperBimodule.whiskerRight
        (probeHeightInductionSuperDotIso D Sc i m ha n).inv N else 0) =
      koszulSign p q •
        ((if p=d then SuperBimodule.whiskerRight
          (probeHeightInductionSuperDotIso D Sc i m ha n).inv M else 0) ≫
          SuperBimodule.whiskerLeft P f)
    split_ifs with h
    · subst p
      rw [SuperBimodule.super_interchange P f
        (probeHeightInductionSuperDotInverse_parity D Sc i m ha n) hf,
        koszulSign_smul_smul]
    · simp

/-- The actual supernatural induction dot, with its prescribed signed inverse,
is an isomorphism on the whole existing module supercategory. -/
def probeHeightSuperDotIso :
    (⟨heightSuperInduction D Sc i a ha n⟩ :
      Superfunctor k (HeightModules D Sc a ha n)
        (HeightModules D Sc a ha (n+1))) ≅
    (⟨heightSuperInduction D Sc i a ha n⟩ :
      Superfunctor k (HeightModules D Sc a ha n)
        (HeightModules D Sc a ha (n+1))) where
  hom := heightSuperInductionDot D Sc i a ha n
  inv := probeHeightSuperDotInverse D Sc i m ha n
  hom_inv_id := by
    have hprod : heightInductionSuperDot D Sc i a ha n ≫
        (probeHeightInductionSuperDotIso D Sc i m ha n).inv = 𝟙 P :=
      (probeHeightInductionSuperDotIso D Sc i m ha n).hom_inv_id
    apply Superfunctor.hom_ext_parity
    · intro M
      rw [Superfunctor.comp_app_zero, Superfunctor.id_app_zero]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [heightSuperInductionDot, probeHeightSuperDotInverse, hd,
          ← SuperBimodule.comp_whiskerRight,
          hprod, SuperBimodule.id_whiskerRight] <;> rfl
    · intro M
      rw [Superfunctor.comp_app_one, Superfunctor.id_app_one]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [heightSuperInductionDot, probeHeightSuperDotInverse, hd]
  inv_hom_id := by
    have hprod : (probeHeightInductionSuperDotIso D Sc i m ha n).inv ≫
        heightInductionSuperDot D Sc i a ha n = 𝟙 P :=
      (probeHeightInductionSuperDotIso D Sc i m ha n).inv_hom_id
    apply Superfunctor.hom_ext_parity
    · intro M
      rw [Superfunctor.comp_app_zero, Superfunctor.id_app_zero]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [heightSuperInductionDot, probeHeightSuperDotInverse, hd,
          ← SuperBimodule.comp_whiskerRight,
          hprod, SuperBimodule.id_whiskerRight] <;> rfl
    · intro M
      rw [Superfunctor.comp_app_one, Superfunctor.id_app_one]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [heightSuperInductionDot, probeHeightSuperDotInverse, hd]


end OddMath.QuiverHecke.CyclotomicAction
