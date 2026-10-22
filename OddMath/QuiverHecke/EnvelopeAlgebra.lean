/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EnvelopeSerre
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.CoefficientLocalization

/-!
# `K₀(Ḣ_{q,π})` as an `ℒ`-algebra

Brundan–Ellis, arXiv:1701.04133v2, (11.2) and the setting of Theorem 11.3: `K₀(Ḣ_{q,π})` with
the induction product is a unital `ℒ`-algebra (`KHop.algebra`), the target of the
`ℒ`-algebra isomorphism `γ̄ : f_𝒜 → K₀(Ḣ_{q,π})`. Over a field:

* `Ḣ_{q,π}` has one object (`hDot_eq_star`), so the idempotent `1 = [𝟙]` of the locally unital
  ring `K₀Ring` is an identity (`KH.ring`);
* `K₀` of the completed hom category maps bijectively onto `K₀(Ḣ_{q,π})`
  (`hKarToKH_injective`, `hKarToKH_surjective`), and the map is `ℒ`-linear (`hKarToKH_smul`):
  the entrywise shifts agree with the action of BE2 §6 on the generating classes of
  `dpSpan_eq_top`;
* `K₀(Ḣ_{q,π})` has no `ℤ[q, q⁻¹]`-torsion (`KHop.eq_zero_of_smul_eq_zero`), since it is free over
  `ℤ[q, q⁻¹]` (`k0_free_laurentInt`), so extension of scalars to `𝕃 = ℚ(q)[π]/(π² - 1)`, a
  localization of `ℒ` at nonzero elements of `ℤ[q, q⁻¹]`, is injective (`KHop.tmul_injective`).
  BE2 extend scalars to `𝕃` to construct `γ̄`; the last fact restricts it to `f_𝒜`.
-/

noncomputable section

open CategoryTheory StringDiagrams LaurentPolynomial
open CategoryTheory.Idempotents OddMath.SKM.Summands

namespace OddMath.QuiverHecke

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [Field k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- `Ḣ_{q,π}` has one object. -/
theorem hDot_eq_star (a : HDot D Sc sy hc) : a = HDot.star D Sc sy hc := by
  rcases a with ⟨⟨⟨⟨⟨⟩⟩⟩⟩⟩
  rfl

/-- `[𝟙]` is a two-sided identity of `K₀(Ḣ_{q,π})`. -/
theorem one_mul_KH (x : KH D Sc sy hc) :
    K₀Ring.one (HDot.star D Sc sy hc) * x = x ∧ x * K₀Ring.one (HDot.star D Sc sy hc) = x := by
  classical
  obtain ⟨s, hs⟩ := K₀Ring.exists_finset_one_mul x
  have ht : insert (HDot.star D Sc sy hc) s = {HDot.star D Sc sy hc} :=
    Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_insert_self _ _, fun c _ => hDot_eq_star D Sc sy hc c⟩
  have h := hs _ (Finset.subset_insert (HDot.star D Sc sy hc) s)
  rw [ht, Finset.sum_singleton] at h
  exact h

/-- **BE2 (11.2).** `K₀(Ḣ_{q,π})` is a unital ring, with identity the class of the unit object. -/
instance KH.ring : Ring (KH D Sc sy hc) :=
  { K₀Ring.instNonUnitalRing with
    one := K₀Ring.one (HDot.star D Sc sy hc)
    one_mul := fun x => (one_mul_KH D Sc sy hc x).1
    mul_one := fun x => (one_mul_KH D Sc sy hc x).2 }

theorem one_KH : (1 : KH D Sc sy hc) = K₀Ring.one (HDot.star D Sc sy hc) := rfl

theorem wordCls_nil : wordCls D Sc sy hc [] = 1 := rfl

/-- **BE2 (11.2).** `K₀(Ḣ_{q,π})` with the induction product is an `ℒ`-algebra. -/
instance KHop.algebra : Algebra (LaurentPolynomial Zπ) (KHop D Sc sy hc) :=
  Algebra.ofModule
    (fun r x y => by
      change MulOpposite.op (y.unop *
          (letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc)); r • x.unop)) =
        MulOpposite.op (letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc));
          r • (y.unop * x.unop))
      rw [GSKAR.mul_smul])
    (fun r x y => by
      change MulOpposite.op ((letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc));
          r • y.unop) * x.unop) =
        MulOpposite.op (letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc));
          r • (y.unop * x.unop))
      rw [GSKAR.smul_mul])

theorem hKarToKH_surjective : Function.Surjective (hKarToKH (k := k) D Sc sy hc) := by
  intro x
  change x ∈ (hKarToKH (k := k) D Sc sy hc).range
  induction x using K₀Ring.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | of a b x =>
    obtain rfl := hDot_eq_star D Sc sy hc a
    obtain rfl := hDot_eq_star D Sc sy hc b
    induction x using K₀.induction_on with
    | mk f => exact ⟨K₀.mk f, hKarToKH_mk (D := D) (Sc := Sc) (sy := sy) (hc := hc) f⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | neg x hx => rw [map_neg]; exact neg_mem hx

/-- **`K₀(HKar) → K₀(Ḣ_{q,π})` is `ℒ`-linear**: by `hcls_smul` on the shifted products of
divided powers, which generate (`dpSpan_eq_top`). -/
theorem hKarToKH_smul (r : LaurentPolynomial Zπ) (y : K₀ (HKar (k := k) D Sc sy hc)) :
    MulOpposite.op (hKarToKH D Sc sy hc (letI := K₀.moduleLaurent k (HKar D Sc sy hc); r • y)) =
      r • MulOpposite.op (hKarToKH D Sc sy hc y) := by
  let g : K₀ (HKar (k := k) D Sc sy hc) →+ KHop D Sc sy hc :=
    (DistribSMul.toAddMonoidHom (KHop D Sc sy hc) r).comp
      ((MulOpposite.opAddEquiv.toAddMonoidHom).comp (hKarToKH D Sc sy hc))
  let f : K₀ (HKar (k := k) D Sc sy hc) →+ KHop D Sc sy hc :=
    ((MulOpposite.opAddEquiv.toAddMonoidHom).comp (hKarToKH D Sc sy hc)).comp
      (@DistribSMul.toAddMonoidHom _ _ _ (@DistribMulAction.toDistribSMul _ _ _ _
        (@Module.toDistribMulAction _ _ _ _ (K₀.moduleLaurent k (HKar (k := k) D Sc sy hc)))) r)
  have hfg : f = g := by
    refine AddMonoidHom.eq_of_eqOn_dense (dpSpan_eq_top D Sc sy hc) ?_
    rintro _ ⟨t, e, h, n, p, rfl⟩
    exact hcls_smul h.mem_idem.2 h.mem_idem.1.1 h.mem_idem.1.2 r n p
  exact DFunLike.congr_fun hfg y

/-- **`K₀(Ḣ_{q,π})` has no `ℤ[q, q⁻¹]`-torsion**: it is free over `ℤ[q, q⁻¹]`
(`k0_free_laurentInt`). -/
theorem KHop.eq_zero_of_smul_eq_zero {s : LaurentPolynomial Zπ}
    (hs : s ∈ CoveringQuantum.Coefficients.intDenominators)
    {x : KHop D Sc sy hc} (h : s • x = 0) : x = 0 := by
  obtain ⟨p, hp, rfl⟩ := hs
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact nonZeroDivisors.ne_zero (Submonoid.mem_comap.mp hp) (map_zero _)
  obtain ⟨y, hy⟩ := hKarToKH_surjective D Sc sy hc x.unop
  have hx : x = MulOpposite.op (hKarToKH D Sc sy hc y) := by rw [hy]; rfl
  subst hx
  rw [← hKarToKH_smul] at h
  have h0 : (letI := K₀.moduleLaurent k (HKar D Sc sy hc);
      CoveringQuantum.Coefficients.intToLaurent p • y) = 0 :=
    hKarToKH_injective ((MulOpposite.op_eq_zero_iff _).1 h |>.trans (map_zero _).symm)
  have hfree : letI := K₀.moduleLaurentInt k (HKar (k := k) D Sc sy hc)
      Module.Free (LaurentPolynomial ℤ) (K₀ (HKar (k := k) D Sc sy hc)) :=
    k0_free_laurentInt D sy Sc hc
  let := K₀.moduleLaurentInt k (HKar (k := k) D Sc sy hc)
  have h1 : p • y = 0 := h0
  rw [(smul_eq_zero.1 h1).resolve_left hp0, map_zero, MulOpposite.op_zero]

omit [AddCommGroup X] in
private theorem mk_one_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (S : Submonoid R) [IsLocalization S A]
    (htor : ∀ s ∈ S, ∀ m : M, s • m = 0 → m = 0) :
    Function.Injective (TensorProduct.mk R A M 1) := by
  have : IsLocalizedModule S (TensorProduct.mk R A M 1) :=
    (isLocalizedModule_iff_isBaseChange S A _).mpr (TensorProduct.isBaseChange _ _ _)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S _).mp hx
  exact htor s s.2 x hs

/-- **Extension of scalars from `ℒ` to `𝕃` is injective on `K₀(Ḣ_{q,π})`**: `𝕃` is a
localization of `ℒ` at nonzero elements of `ℤ[q, q⁻¹]` (`Coefficients.isLocalization`), and
`K₀(Ḣ_{q,π})` has no such torsion. -/
theorem KHop.tmul_injective :
    Function.Injective (TensorProduct.mk (LaurentPolynomial Zπ) CoveringQuantum.Coefficients.Ring
      (KHop D Sc sy hc) 1) := by
  have := CoveringQuantum.Coefficients.isLocalization
  refine mk_one_injective (R := LaurentPolynomial Zπ) (A := CoveringQuantum.Coefficients.Ring)
    (M := KHop D Sc sy hc) CoveringQuantum.Coefficients.intDenominators ?_
  intro s hs x hx
  exact KHop.eq_zero_of_smul_eq_zero D Sc sy hc hs hx

end OddMath.QuiverHecke
