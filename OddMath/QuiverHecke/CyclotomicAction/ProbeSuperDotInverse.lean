import OddMath.QuiverHecke.CyclotomicAction.ProbeAppendDotInverse
import OddMath.QuiverHecke.CyclotomicAction.SuperDot
import StringDiagrams.Super.Parity

/-! # Signed inverse of the actual probe induction dot

The right inverse in the append corner acts on the literal induction ideal.
The underlying inverse is right multiplication by X followed by the parity
sign. Its SVec isomorphism gives inverse parity through Supercategory.inv_mem;
the inverse then satisfies the actual superbimodule Hom equations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (m : I → ℕ)
  (ha : CyclotomicPolynomialParity D (probePolynomial (probeDotExponent D) m)) (n : ℕ)
local notation "a" => probePolynomial (probeDotExponent D) m
local notation "P" => inductionCorner D Sc i a ha n
local notation "GB" => cyclotomicParity D Sc a ha (n+1)
local notation "e" => cyclotomicAppend D Sc i a n 1
local notation "c" => cyclotomicLastDot D Sc i a n
local notation "Xinv" => (probeAppendDotInverse D Sc i m n).val
local notation "d" => D.parity i

private theorem probe_rightDot_mem (x : CyclotomicAlgebra D Sc a (n+1))
    (_hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    x*c ∈ inductionCornerSubmodule D Sc i a n := by
  change (x*c)*e=x*c
  rw [mul_assoc, (cyclotomicLastDot_corner D Sc i a n).2]

private theorem probe_rightInv_mem (x : CyclotomicAlgebra D Sc a (n+1))
    (_hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    x*Xinv ∈ inductionCornerSubmodule D Sc i a n := by
  have hX := ((Subsemigroup.mem_corner_iff (probeAppendIdempotent D Sc i a n)).mp
    (probeAppendDotInverse D Sc i m n).property).2
  change (x*Xinv)*e=x*Xinv
  rw [mul_assoc, hX]

private def probeRightDotLinear : P.toSVec ⟶ P.toSVec :=
  SVec.restrictHom ((SuperBimodule.regular GB).ract c) (probe_rightDot_mem D Sc i m n)

private def probeRightInvLinear : P.toSVec ⟶ P.toSVec :=
  SVec.restrictHom ((SuperBimodule.regular GB).ract Xinv) (probe_rightInv_mem D Sc i m n)

private theorem probeRightDot_inv : probeRightDotLinear D Sc i m ha n ≫
    probeRightInvLinear D Sc i m ha n = 𝟙 P.toSVec := by
  apply SVec.hom_ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun z : ProbeAppendCorner D Sc i a n => z.val)
    (probeAppendLastDot_mul_inverse D Sc i m n)
  change c*Xinv=e at h
  change (x.val*c)*Xinv=x.val
  rw [mul_assoc, h]
  exact x.property

private theorem probeRightInv_dot : probeRightInvLinear D Sc i m ha n ≫
    probeRightDotLinear D Sc i m ha n = 𝟙 P.toSVec := by
  apply SVec.hom_ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun z : ProbeAppendCorner D Sc i a n => z.val)
    (probeAppendLastDot_inverse_mul D Sc i m n)
  change Xinv*c=e at h
  change (x.val*Xinv)*c=x.val
  rw [mul_assoc, h]
  exact x.property

private theorem probeSign_sq :
    SVec.ofHom (P.toSVec.sgn d) ≫ SVec.ofHom (P.toSVec.sgn d) = 𝟙 P.toSVec := by
  apply SVec.hom_ext
  intro x
  exact SVec.sgn_sgn_apply P.toSVec d x

/-- The actual inverse applies right multiplication before the parity sign. -/
def probeInductionDotInverseLinear : P.toSVec ⟶ P.toSVec :=
  probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom (P.toSVec.sgn d)

def probeInductionDotSVecIso : P.toSVec ≅ P.toSVec where
  hom := inductionDotLinear D Sc i a ha n
  inv := probeInductionDotInverseLinear D Sc i m ha n
  hom_inv_id := by
    change (SVec.ofHom (P.toSVec.sgn d) ≫ probeRightDotLinear D Sc i m ha n) ≫
      (probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom (P.toSVec.sgn d)) = _
    calc
      _ = SVec.ofHom (P.toSVec.sgn d) ≫
          ((probeRightDotLinear D Sc i m ha n ≫ probeRightInvLinear D Sc i m ha n) ≫
            SVec.ofHom (P.toSVec.sgn d)) := by simp only [Category.assoc]
      _ = _ := by rw [probeRightDot_inv, Category.id_comp, probeSign_sq]
  inv_hom_id := by
    change (probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom (P.toSVec.sgn d)) ≫
      (SVec.ofHom (P.toSVec.sgn d) ≫ probeRightDotLinear D Sc i m ha n) = _
    calc
      _ = probeRightInvLinear D Sc i m ha n ≫
          ((SVec.ofHom (P.toSVec.sgn d) ≫ SVec.ofHom (P.toSVec.sgn d)) ≫
            probeRightDotLinear D Sc i m ha n) := by simp only [Category.assoc]
      _ = _ := by rw [probeSign_sq, Category.id_comp, probeRightInv_dot]

theorem probeInductionDotInverse_parity :
    probeInductionDotInverseLinear D Sc i m ha n ∈ SVec.parityHom P.toSVec P.toSVec d :=
  inv_mem (probeInductionDotSVecIso D Sc i m ha n) (inductionDotLinear_parity D Sc i a ha n)

theorem probeInductionDotInverse_isHom :
    SuperBimodule.IsHom P P (probeInductionDotInverseLinear D Sc i m ha n) := by
  let E := probeInductionDotSVecIso D Sc i m ha n
  have hf := (SuperBimodule.isHom_iff_of_mem (inductionDotLinear_parity D Sc i a ha n)).1
    (inductionDotLinear_isHom D Sc i a ha n)
  apply (SuperBimodule.isHom_iff_of_mem (probeInductionDotInverse_parity D Sc i m ha n)).2
  constructor
  · intro p b hb
    change P.lact b ≫ E.inv = sign k (p*d) • (E.inv ≫ P.lact b)
    have hl : P.lact b ≫ E.hom = sign k (p*d) • (E.hom ≫ P.lact b) := hf.1 p b hb
    have hl' : E.hom ≫ P.lact b = sign k (p*d) • (P.lact b ≫ E.hom) := by
      rw [hl, smul_smul, sign_mul_self, one_smul]
    apply (cancel_epi E.hom).1
    calc
      E.hom ≫ (P.lact b ≫ E.inv) = (E.hom ≫ P.lact b) ≫ E.inv :=
        (Category.assoc _ _ _).symm
      _ = (sign k (p*d) • (P.lact b ≫ E.hom)) ≫ E.inv := by rw [hl']
      _ = sign k (p*d) • (P.lact b ≫ (E.hom ≫ E.inv)) := by
        rw [Linear.smul_comp, Category.assoc]
      _ = sign k (p*d) • P.lact b := by rw [E.hom_inv_id, Category.comp_id]
      _ = E.hom ≫ (sign k (p*d) • (E.inv ≫ P.lact b)) := by
        rw [Linear.comp_smul, ← Category.assoc, E.hom_inv_id, Category.id_comp]
  · intro r
    change P.ract r ≫ E.inv = E.inv ≫ P.ract r
    apply (cancel_epi E.hom).1
    calc
      E.hom ≫ (P.ract r ≫ E.inv) = (E.hom ≫ P.ract r) ≫ E.inv :=
        (Category.assoc _ _ _).symm
      _ = (P.ract r ≫ E.hom) ≫ E.inv := by rw [← hf.2 r]
      _ = P.ract r := by rw [Category.assoc, E.hom_inv_id, Category.comp_id]
      _ = E.hom ≫ (E.inv ≫ P.ract r) := by
        rw [← Category.assoc, E.hom_inv_id, Category.id_comp]

/-- The existing signed induction dot has this actual superbimodule inverse. -/
def probeInductionSuperDotIso : P ≅ P where
  hom := inductionSuperDot D Sc i a ha n
  inv := ⟨probeInductionDotInverseLinear D Sc i m ha n,
    probeInductionDotInverse_isHom D Sc i m ha n⟩
  hom_inv_id := Subtype.ext (probeInductionDotSVecIso D Sc i m ha n).hom_inv_id
  inv_hom_id := Subtype.ext (probeInductionDotSVecIso D Sc i m ha n).inv_hom_id

theorem probeInductionSuperDotInverse_parity :
    (probeInductionSuperDotIso D Sc i m ha n).inv ∈ parity (R := k) P P d :=
  SuperBimodule.mem_parity_iff.2 (probeInductionDotInverse_parity D Sc i m ha n)

/-- On a homogeneous element the inverse is exactly the signed-right inverse,
including the additional colour parity sign in the odd case. -/
theorem probeInductionSuperDotInverse_apply {p : ZMod 2} (x : P.toSVec)
    (hx : x ∈ P.toSVec.part p) :
    (((probeInductionSuperDotIso D Sc i m ha n).inv).1 x).val =
      sign k (d + p*d) • (x.val * Xinv) := by
  have hRI : probeRightInvLinear D Sc i m ha n ∈ parity (R := k) P.toSVec P.toSVec d := by
    have h := comp_mem (probeInductionDotInverse_parity D Sc i m ha n) (SVec.sgn_mem P.toSVec d)
    have heq : probeInductionDotInverseLinear D Sc i m ha n ≫
        SVec.ofHom (P.toSVec.sgn d) = probeRightInvLinear D Sc i m ha n := by
      change (probeRightInvLinear D Sc i m ha n ≫ SVec.ofHom (P.toSVec.sgn d)) ≫
        SVec.ofHom (P.toSVec.sgn d) = _
      rw [Category.assoc, probeSign_sq, Category.comp_id]
    rw [heq] at h
    simpa only [add_zero] using h
  have h := LinearMap.congr_fun (SVec.sgn_comp_of_mem hRI d) x
  change probeInductionDotInverseLinear D Sc i m ha n x =
    sign k (d*d) • probeRightInvLinear D Sc i m ha n (P.toSVec.sgn d x) at h
  rw [parity_sq] at h
  have hv := congrArg (fun z : P.toSVec => z.val) h
  change (((probeInductionSuperDotIso D Sc i m ha n).inv).1 x).val =
    sign k d • ((P.toSVec.sgn d x).val * Xinv) at hv
  rw [SVec.sgn_apply_of_mem d hx] at hv
  change (((probeInductionSuperDotIso D Sc i m ha n).inv).1 x).val =
    sign k d • ((sign k (p*d) • x.val) * Xinv) at hv
  rw [smul_mul_assoc, smul_smul, ← sign_add] at hv
  exact hv


/-- The inverse as a supernatural transformation of the existing balanced
tensor induction functor. Only its induction-colour parity component is nonzero. -/
def probeCyclotomicSuperDotInverse :
    SuperNatTrans k (cyclotomicSuperInduction D Sc i a ha n)
      (cyclotomicSuperInduction D Sc i a ha n) where
  app p M := if p=d then
    SuperBimodule.whiskerRight (probeInductionSuperDotIso D Sc i m ha n).inv M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact SuperBimodule.whiskerRight_mem P
        (probeInductionSuperDotInverse_parity D Sc i m ha n) M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    change SuperBimodule.whiskerLeft P f ≫
      (if p=d then SuperBimodule.whiskerRight
        (probeInductionSuperDotIso D Sc i m ha n).inv N else 0) =
      koszulSign p q •
        ((if p=d then SuperBimodule.whiskerRight
          (probeInductionSuperDotIso D Sc i m ha n).inv M else 0) ≫
          SuperBimodule.whiskerLeft P f)
    split_ifs with h
    · subst p
      rw [SuperBimodule.super_interchange P f
        (probeInductionSuperDotInverse_parity D Sc i m ha n) hf,
        koszulSign_smul_smul]
    · simp

/-- The actual supernatural induction dot, with its prescribed signed inverse,
is an isomorphism on the whole existing module supercategory. -/
def probeCyclotomicSuperDotIso :
    (⟨cyclotomicSuperInduction D Sc i a ha n⟩ :
      Superfunctor k (CyclotomicSupermodules D Sc a ha n)
        (CyclotomicSupermodules D Sc a ha (n+1))) ≅
    (⟨cyclotomicSuperInduction D Sc i a ha n⟩ :
      Superfunctor k (CyclotomicSupermodules D Sc a ha n)
        (CyclotomicSupermodules D Sc a ha (n+1))) where
  hom := cyclotomicSuperInductionDot D Sc i a ha n
  inv := probeCyclotomicSuperDotInverse D Sc i m ha n
  hom_inv_id := by
    apply Superfunctor.hom_ext_parity
    · intro M
      rw [Superfunctor.comp_app_zero, Superfunctor.id_app_zero]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [cyclotomicSuperInductionDot, probeCyclotomicSuperDotInverse, hd,
          ← SuperBimodule.whiskerRight_comp,
          (probeInductionSuperDotIso D Sc i m ha n).hom_inv_id,
          SuperBimodule.whiskerRight_id]
    · intro M
      rw [Superfunctor.comp_app_one, Superfunctor.id_app_one]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [cyclotomicSuperInductionDot, probeCyclotomicSuperDotInverse, hd]
  inv_hom_id := by
    apply Superfunctor.hom_ext_parity
    · intro M
      rw [Superfunctor.comp_app_zero, Superfunctor.id_app_zero]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [cyclotomicSuperInductionDot, probeCyclotomicSuperDotInverse, hd,
          ← SuperBimodule.whiskerRight_comp,
          (probeInductionSuperDotIso D Sc i m ha n).inv_hom_id,
          SuperBimodule.whiskerRight_id]
    · intro M
      rw [Superfunctor.comp_app_one, Superfunctor.id_app_one]
      rcases parity_eq_zero_or_one d with hd | hd <;>
        simp [cyclotomicSuperInductionDot, probeCyclotomicSuperDotInverse, hd]


end OddMath.QuiverHecke
