/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreDividedPowersDown
import OddMath.QuiverHecke.CategoricalDividedPowersDown
import OddMath.SKM.K0Commutation
import OddMath.QuiverHecke.CornerProjectors

/-!
# BE2 Lemma 11.5 in the Grothendieck ring

Brundan–Ellis, arXiv:1701.04133v2, Lemma 11.5, read in the Grothendieck ring `K₀(U̇(𝔤))` of §6
with its `ℤ[q^±, π]/(π² - 1)`-module structure (left multiplication by the classes `[q 1_λ]`,
`[π 1_λ]`). This is the first step towards the existence part of Theorem 11.7.

`CategoricalDividedPowers` proves the class equations in `K₀` of one completed hom category, where
`q` and `π` act by entrywise shifts. Here they are carried into the Grothendieck ring:

* `toGr_smul_raw`: the map from `K₀` of the completed hom category `μ → ν` to the Grothendieck
  ring is `ℒ`-linear on summand classes (`smul_shift_family`: both actions are determined by the
  shifts `Q^n Π^p`).
* `cls_mul_cls`: products of classes of words are classes of concatenated words, with the shifts
  added.
* `cls_power_eq_dividedPower`: `[E_i^n 1_ν] = [n]^!_{q_i,π_i} [E_i^{(n)} 1_ν]`, every colour,
  every `n`, with the corrected divided power `Q^{d_i n(n-1)/2} Π^{|i| n(n-1)/2} E_i^{(n)} 1_ν`
  (ERRATA [BE2] 13).
* `cls_power_eq_dividedPower_down`: `[F_i^n 1_{-ν}] = [n]^!_{q_i,π_i} [F_i^{(n)} 1_{-ν}]`, with
  the corrected divided power `Q^{-d_i n(n-1)/2} F_i^{(n)} 1_{-ν}`.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke BicategoryStruct LaurentPolynomial
open CategoryTheory.Idempotents
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w}
  [CommRing k] {Sc : SKM.Scalars D k} (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

namespace SerreComplex
open SKM.K0Relations

instance : Module (LaurentPolynomial Zπ) (Grothendieck Sc sy hc) :=
  letI := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc)
  inferInstanceAs (Module _ (K₀Ring (SKM.UDot D Sc sy hc))ᵐᵒᵖ)

theorem raw_id {A : Type*} [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    [GradedSupercategory k A] (f : A) (n : ℤ) (p : ZMod 2) :
    SKM.Summands.raw (Category.id_comp (𝟙 f)) (GradedSupercategory.id_mem_degree f)
      (Supercategory.id_mem f) n p =
      (toKaroubi _).obj ((Mat_.embedding _).obj (SKM.Summands.shifted (k := k) f n p)) := by
  refine Karoubi.ext rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (Mat_.embedding _).map_id _

theorem cls_eq_raw (μ ν : X) (s) (hs : SKM.wt D ν s = μ) (n : ℤ) (a : ZMod 2) :
    cls Sc sy hc μ ν s hs n a = MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc)
      (a := weight Sc sy hc μ) (b := weight Sc sy hc ν)
      (SKM.Summands.raw (f := SKM.K0Relations.word Sc sy hc μ ν s hs) (Category.id_comp (𝟙 _))
        (GradedSupercategory.id_mem_degree _) (Supercategory.id_mem _) n a)) := by
  rw [raw_id]; rfl

theorem word_comp (μ ρ ν : X) (s t : List (SKM.Letter I)) (hs : SKM.wt D ρ s = μ)
    (ht : SKM.wt D ν t = ρ) :
    SKM.K0Relations.word Sc sy hc μ ρ s hs ≫ SKM.K0Relations.word Sc sy hc ρ ν t ht =
      SKM.K0Relations.word Sc sy hc μ ν (s ++ t) (by rw [SKM.wt_append, ht, hs]) := by
  subst hs ht
  refine Presentation.Bicat.Hom.ext (Obj.ext ?_ ?_)
  · exact (SKM.wt_append D ν s t).symm
  · exact (SKM.wd_append D ν s t).symm

open BicategoryStruct in
theorem hcomp_id {a b c : SKM.UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    TwoSupercategory.hcomp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := by
  simp only [TwoSupercategory.hcomp]
  rw [TwoSupercategory.whiskerLeft_id (R := k), TwoSupercategory.id_whiskerRight (R := k),
    Category.comp_id]

/-- **Products of words**: `[Q^n Π^a s 1_ρ] [Q^{n'} Π^{a'} t 1_ν] = [Q^{n+n'} Π^{a+a'} s t 1_ν]`. -/
theorem cls_mul_cls (μ ρ ν : X) (s t : List (SKM.Letter I)) (hs : SKM.wt D ρ s = μ)
    (ht : SKM.wt D ν t = ρ) (n n' : ℤ) (a a' : ZMod 2) :
    cls Sc sy hc μ ρ s hs n a * cls Sc sy hc ρ ν t ht n' a' =
      cls Sc sy hc μ ν (s ++ t) (by rw [SKM.wt_append, ht, hs]) (n + n') (a + a') := by
  rw [cls_eq_raw, cls_eq_raw, cls_eq_raw, ← MulOpposite.op_mul, SKM.Summands.mk_raw_mul_mk_raw]
  congr 2
  exact raw_congr (word_comp sy hc μ ρ ν s t hs ht) (heq_of_eq_of_heq (hcomp_id sy hc _ _)
    (by rw [word_comp sy hc μ ρ ν s t hs ht])) _ _ _ _ _ _ _ _


/-! ### Lemma 11.5 in the Grothendieck ring -/

section Coefficients
open CategoricalDividedPowers (val_qUnit_zpow)

theorem map_T_int (z : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (T z : LaurentPolynomial ℤ) = T z := by
  rw [T, AddMonoidAlgebra.mapRingHom_single, map_one]; rfl

theorem map_qint (d : ℤ) (m : ℕ) :
    AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ)
        (Categorification.QuantumGroup.qint (CategoricalDividedPowers.qUnit d) m) =
      CoveringQuantum.qpNat (qUnit d) (piCoeff 0) m := by
  rw [Categorification.QuantumGroup.qint_eq_sum, map_sum, CoveringQuantum.qpNat]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs := Finset.mem_range.mp hs
  rw [val_qUnit_zpow, map_T_int]
  change T _ = ((C Zπ.π) ^ (0 : ZMod 2).val) ^ s * (T d) ^ (m - 1 - s) * (T (-d)) ^ s
  rw [ZMod.val_zero, pow_zero, one_pow, one_mul, T_pow, T_pow, ← T_add]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem map_qfact (d : ℤ) (n : ℕ) :
    AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ)
        (Categorification.QuantumGroup.qfact (CategoricalDividedPowers.qUnit d) n) =
      CoveringQuantum.qpFact (qUnit d) (piCoeff 0) n := by
  induction n with
  | zero => simp [Categorification.QuantumGroup.qfact, CoveringQuantum.qpFact]
  | succ n ih =>
    rw [Categorification.QuantumGroup.qfact_succ, map_mul, ih, map_qint, CoveringQuantum.qpFact]
    ring

end Coefficients

theorem smul_int {C : Type*} [Category C] [Preadditive C] [Linear k C] [QPiCategory k C]
    [Limits.HasBinaryBiproducts C] (p : LaurentPolynomial ℤ) (x : K₀ C) :
    (letI := K₀.moduleLaurentInt k C; p • x) =
      (letI := K₀.moduleLaurent k C;
        AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) p • x) := rfl

variable (i : I)

theorem dpIdem_eq_even (hi : D.parity i = 0) (r : ℕ) :
    dpIdem D Sc i r = evenCornerProjector D Sc i hi r := by
  rw [evenCornerProjector_eq_idem, dpIdem, eps, hi]; rfl


theorem comp_id_eq {a b : SKM.UGr D Sc sy hc} (f : a ⟶ b) : f ≫ 𝟙 b = f := by
  apply Presentation.Bicat.Hom.ext
  exact Obj.tensor_nil f.obj b.region

theorem rightUnitor_eq_eqToIso {a b : SKM.UGr D Sc sy hc} (f : a ⟶ b) :
    rightUnitor f = eqToIso (comp_id_eq sy hc f) :=
  Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_nil f.obj b.region) _

theorem heq_conj {C : Type*} [Category C] {X X' : C} (p : X = X') (x : X' ⟶ X') :
    HEq (eqToHom p ≫ x ≫ eqToHom p.symm) x := by
  subst p; simp

theorem hcomp_id_right_heq {a b : SKM.UGr D Sc sy hc} {f : a ⟶ b} (e : f ⟶ f) :
    HEq (TwoSupercategory.hcomp e (𝟙 (𝟙 b))) e := by
  have h1 : TwoSupercategory.hcomp e (𝟙 (𝟙 b)) = e ▷ 𝟙 b := by
    simp only [TwoSupercategory.hcomp]
    rw [TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  have h2 : e ▷ 𝟙 b = (rightUnitor f).hom ≫ e ≫ (rightUnitor f).inv :=
    TwoSupercategory.whiskerRight_id (R := k) e
  rw [h1, h2, rightUnitor_eq_eqToIso, eqToIso.hom, eqToIso.inv]
  exact heq_conj _ e

omit [CommRing k] in
private theorem smul_expand {V : Type*} [AddCommGroup V] [Module (LaurentPolynomial Zπ) V]
    (i j m : ℤ) (v : V) :
    ((i : LaurentPolynomial Zπ) * T m + (j : LaurentPolynomial Zπ) * (C Zπ.π * T m)) • v =
      i • ((T m : LaurentPolynomial Zπ) • v) +
        j • ((C Zπ.π : LaurentPolynomial Zπ) • (T m : LaurentPolynomial Zπ) • v) := by
  rw [add_smul, mul_smul, mul_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

omit [CommRing k] in
/-- A `ℤ`-linear map between `Zπ[q^±]`-modules commutes with the action on a family of elements on
which `T z` and `C π` act by the same shifts on both sides. -/
theorem smul_shift_family {M N : Type*} [AddCommGroup M] [Module (LaurentPolynomial Zπ) M]
    [AddCommGroup N] [Module (LaurentPolynomial Zπ) N] (φ : M →+ N) (x : ℤ → ZMod 2 → M)
    (y : ℤ → ZMod 2 → N) (hφ : ∀ n p, φ (x n p) = y n p)
    (hxT : ∀ z n p, (T z : LaurentPolynomial Zπ) • x n p = x (n + z) p)
    (hxπ : ∀ n p, (C Zπ.π : LaurentPolynomial Zπ) • x n p = x n (p + 1))
    (hyT : ∀ z n p, (T z : LaurentPolynomial Zπ) • y n p = y (n + z) p)
    (hyπ : ∀ n p, (C Zπ.π : LaurentPolynomial Zπ) • y n p = y n (p + 1))
    (r : LaurentPolynomial Zπ) (n : ℤ) (p : ZMod 2) : φ (r • x n p) = r • y n p := by
  induction r using LaurentPolynomial.induction_on' generalizing n p with
  | add r s hr hs => rw [add_smul, map_add, hr, hs, add_smul]
  | C_mul_T m a =>
    obtain ⟨i, j, rfl⟩ := Zπ.exists_eq_add_mul_π a
    have hK : (C ((i : Zπ) + j * Zπ.π) * T m : LaurentPolynomial Zπ) =
        (i : LaurentPolynomial Zπ) * T m + (j : LaurentPolynomial Zπ) * (C Zπ.π * T m) := by
      simp only [map_add, map_mul, map_intCast]; ring
    rw [hK, smul_expand, smul_expand, hxT, hxπ, hyT, hyπ, map_add, map_zsmul, map_zsmul, hφ, hφ]

section Shifts

variable {μ ν : X} {f : (show SKM.UGr D Sc sy hc from ⟨μ⟩) ⟶ ⟨ν⟩} {e : f ⟶ f}
  (he : e ≫ e = e) (hd : e ∈ GradedSupercategory.degree (R := k) f f 0)
  (hp : e ∈ Supercategory.parity (R := k) f f 0)

/-- The class of the summand `Q^n Π^p (f, e)` in the Grothendieck ring. -/
abbrev rcls (n : ℤ) (p : ZMod 2) : Grothendieck Sc sy hc :=
  MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc μ)
    (b := weight Sc sy hc ν) (SKM.Summands.raw he hd hp n p))

variable (ν) in
/-- The shifted identity `Q^m Π^s 1_ν`. -/
abbrev unitRaw (m : ℤ) (s : ZMod 2) :=
  SKM.Summands.raw (k := k) (f := 𝟙 (show SKM.UGr D Sc sy hc from ⟨ν⟩)) (Category.id_comp _)
    (GradedSupercategory.id_mem_degree (R := k) _) (Supercategory.id_mem (R := k) _) m s

theorem unit_mul_raw (n m : ℤ) (p s : ZMod 2) :
    K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc ν) (b := weight Sc sy hc ν)
        (unitRaw sy hc ν m s) *
      K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc μ) (b := weight Sc sy hc ν)
        (SKM.Summands.raw he hd hp n p) =
    K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc μ) (b := weight Sc sy hc ν)
      (SKM.Summands.raw he hd hp (n + m) (p + s)) := by
  rw [SKM.Summands.mk_raw_mul_mk_raw]
  congr 1
  exact raw_congr (comp_id_eq sy hc f) (hcomp_id_right_heq sy hc e) _ _ _ _ _ _ _ _

variable (ν) in
theorem q_eq_unitRaw : QPiTwoCategory.q (R := k) (weight Sc sy hc ν) = unitRaw sy hc ν 1 0 := by
  rw [unitRaw, raw_id]; rfl

variable (ν) in
theorem qinv_eq_unitRaw :
    QPiTwoCategory.qinv (R := k) (weight Sc sy hc ν) = unitRaw sy hc ν (-1) 0 := by
  rw [unitRaw, raw_id]; rfl

variable (ν) in
theorem pi_eq_unitRaw : PiTwoCategory.pi (R := k) (weight Sc sy hc ν) = unitRaw sy hc ν 0 1 := by
  rw [unitRaw, raw_id]; rfl

theorem T_one_smul_rcls (n : ℤ) (p : ZMod 2) :
    (T 1 : LaurentPolynomial Zπ) • rcls sy hc he hd hp n p = rcls sy hc he hd hp (n + 1) p := by
  let := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc)
  change MulOpposite.op ((T 1 : LaurentPolynomial Zπ) • K₀Ring.of _ _ (K₀.mk _)) = _
  rw [K₀Ring.T_smul_of]
  change MulOpposite.op (K₀Ring.mk _ * K₀Ring.mk _) = _
  rw [q_eq_unitRaw, unit_mul_raw, add_zero]

theorem T_neg_one_smul_rcls (n : ℤ) (p : ZMod 2) :
    (T (-1) : LaurentPolynomial Zπ) • rcls sy hc he hd hp n p =
      rcls sy hc he hd hp (n + -1) p := by
  let := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc)
  change MulOpposite.op ((T (-1) : LaurentPolynomial Zπ) • K₀Ring.of _ _ (K₀.mk _)) = _
  rw [K₀Ring.T_neg_one_smul_of]
  change MulOpposite.op (K₀Ring.mk _ * K₀Ring.mk _) = _
  rw [qinv_eq_unitRaw, unit_mul_raw, add_zero]

theorem pi_smul_rcls (n : ℤ) (p : ZMod 2) :
    (C Zπ.π : LaurentPolynomial Zπ) • rcls sy hc he hd hp n p = rcls sy hc he hd hp n (p + 1) := by
  let := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc)
  change MulOpposite.op ((C Zπ.π : LaurentPolynomial Zπ) • K₀Ring.of _ _ (K₀.mk _)) = _
  rw [K₀Ring.C_π_smul_of]
  change MulOpposite.op (K₀Ring.mk _ * K₀Ring.mk _) = _
  rw [pi_eq_unitRaw, unit_mul_raw, add_zero]

theorem T_smul_rcls (z n : ℤ) (p : ZMod 2) :
    (T z : LaurentPolynomial Zπ) • rcls sy hc he hd hp n p = rcls sy hc he hd hp (n + z) p := by
  induction z using Int.induction_on generalizing n with
  | zero => simp
  | succ z ih =>
    rw [T_add, mul_smul, T_one_smul_rcls, ih]
    congr 1; ring
  | pred z ih =>
    rw [show -(z : ℤ) - 1 = -(z : ℤ) + -1 by ring, T_add, mul_smul, T_neg_one_smul_rcls, ih]
    congr 1; ring

variable (μ ν) in
/-- The completed hom category from `μ` to `ν`, with its entrywise shifts. -/
abbrev HomK := CategoryTheory.Idempotents.Karoubi
  (Mat_ (SKM.Summands.Base k ((show SKM.UGr D Sc sy hc from ⟨μ⟩) ⟶ ⟨ν⟩)))

variable (μ ν) in
/-- Classes of the completed hom category in the Grothendieck ring, with BE2's order. -/
def toGr : K₀ (HomK sy hc μ ν) →+ Grothendieck Sc sy hc :=
  (MulOpposite.opAddEquiv.toAddMonoidHom).comp (K₀Ring.of (weight Sc sy hc μ) (weight Sc sy hc ν))

/-- **The `ℒ`-action on summands**: carrying a class of the completed hom category, with its
entrywise shift action, into the Grothendieck ring with the action of BE2 §6 (left
multiplication by `[q_μ]`, `[π_μ]`) is `ℒ`-linear on summand classes. -/
theorem toGr_smul_raw (r : LaurentPolynomial Zπ) (n : ℤ) (p : ZMod 2) :
    toGr sy hc μ ν (letI := K₀.moduleLaurent k (HomK sy hc μ ν)
      r • K₀.mk (SKM.Summands.raw he hd hp n p)) = r • rcls sy hc he hd hp n p := by
  let := K₀.moduleLaurent k (HomK sy hc μ ν)
  exact smul_shift_family (toGr sy hc μ ν) (fun n p => K₀.mk (SKM.Summands.raw he hd hp n p))
    (rcls sy hc he hd hp) (fun _ _ => rfl)
    (fun z n p => SKM.Summands.class_raw_shift he hd hp n z p)
    (fun n p => SKM.Summands.class_raw_pi he hd hp n p)
    (T_smul_rcls sy hc he hd hp) (pi_smul_rcls sy hc he hd hp) r n p

end Shifts

/-- **BE2 Lemma 11.5 for an even colour, in the Grothendieck ring**:
`[E_i^r 1_ν] = [r]^!_{q_i,π_i} [E_i^{(r)} 1_ν]`, with the corrected divided power. -/
theorem cls_power_even (hi : D.parity i = 0) (r : ℕ) (ν : X) :
    cls Sc sy hc _ ν (upWord (List.replicate r i)) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) r •
        Edp sy hc i r _ ν rfl (sy.d i * (r.choose 2 : ℕ))
          (((r.choose 2 : ℕ) : ZMod 2) * D.parity i) := by
  have h := CategoricalDividedPowers.class_corrected D Sc sy hc i hi r ν
  rw [smul_int, map_qfact] at h
  have e1 : cls Sc sy hc _ ν (upWord (List.replicate r i)) rfl 0 0 =
      toGr sy hc _ ν (K₀.mk (SKM.Summands.whole
        (CategoricalDividedPowers.upWordHom D Sc sy hc i r ν))) := rfl
  rw [hi, mul_zero, e1, h, toGr_smul_raw]
  congr 1
  change MulOpposite.op (K₀Ring.mk _) = MulOpposite.op (K₀Ring.mk _)
  congr 2
  rw [mul_comm]
  exact raw_congr rfl (heq_of_eq (congrArg _ (dpIdem_eq_even i hi r)).symm) _ _ _ _ _ _ _ _

theorem dpIdem_eq_odd (hi : D.parity i = 1) (r : ℕ) :
    dpIdem D Sc i r = DividedPowerModules.oddCornerProjector D Sc i hi r :=
  (oddCornerProjector_eq_idem D Sc i hi r).symm

theorem qUnitPi_eq (d : ℤ) : CategoricalDividedPowers.qUnitPi d = qUnit d := Units.ext rfl

theorem piCoeff_one : piCoeff 1 = CategoricalDividedPowers.piLP := by
  simp [piCoeff, CategoricalDividedPowers.piLP, ZMod.val_one]

/-- **BE2 Lemma 11.5 for an odd colour, in the Grothendieck ring**:
`[E_i^{n+2} 1_ν] = [n+2]^!_{q_i,π_i} [E_i^{(n+2)} 1_ν]`, with the corrected divided power. -/
theorem cls_power_odd (hi : D.parity i = 1) (n : ℕ) (ν : X) :
    cls Sc sy hc _ ν (upWord (List.replicate (n + 2) i)) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) (n + 2) •
        Edp sy hc i (n + 2) _ ν rfl (sy.d i * ((n + 2).choose 2 : ℕ))
          ((((n + 2).choose 2 : ℕ) : ZMod 2) * D.parity i) := by
  have h := CategoricalDividedPowers.class_corrected_odd D Sc sy hc i hi n ν
  have e1 : cls Sc sy hc _ ν (upWord (List.replicate (n + 2) i)) rfl 0 0 =
      toGr sy hc _ ν (K₀.mk (SKM.Summands.whole
        (CategoricalDividedPowers.upWordHom D Sc sy hc i (n + 2) ν))) := rfl
  rw [hi, mul_one, piCoeff_one, ← qUnitPi_eq, e1, h]
  rw [toGr_smul_raw]
  congr 1
  change MulOpposite.op (K₀Ring.mk _) = MulOpposite.op (K₀Ring.mk _)
  congr 2
  rw [mul_comm]
  exact raw_congr rfl (heq_of_eq (congrArg _ (dpIdem_eq_odd i hi (n + 2))).symm) _ _ _ _ _ _ _ _

/-- Lemma 11.5 with at most one strand: `E_i^{(n)} 1_ν = E_i^n 1_ν` for `n ≤ 1`. -/
theorem cls_power_le_one (hi : D.parity i = 1) (n : ℕ) (hn : n ≤ 1) (ν : X) :
    cls Sc sy hc _ ν (upWord (List.replicate n i)) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n •
        Edp sy hc i n _ ν rfl (sy.d i * (n.choose 2 : ℕ))
          (((n.choose 2 : ℕ) : ZMod 2) * D.parity i) := by
  have hq : CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n = 1 := by
    interval_cases n <;> simp [CoveringQuantum.qpFact, CoveringQuantum.qpNat]
  have hch : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [hq, one_smul, hch, Nat.cast_zero, mul_zero, Nat.cast_zero, zero_mul, cls_eq_raw]
  change MulOpposite.op (K₀Ring.mk _) = MulOpposite.op (K₀Ring.mk _)
  congr 2
  have hp : dpProj sy hc i n _ ν rfl = 𝟙 _ := by
    rw [dpProj, dpIdem_eq_odd i hi n]
    interval_cases n <;> exact (alpha D Sc ν).map_id _
  exact raw_congr rfl (heq_of_eq hp.symm) _ _ _ _ _ _ _ _

/-- **BE2 Lemma 11.5 in the Grothendieck ring**, for every colour and every `n`:
`[E_i^n 1_ν] = [n]^!_{q_i,π_i} [E_i^{(n)} 1_ν]`, where `E_i^{(n)} 1_ν` is the corrected divided
power `Q^{d_i n(n-1)/2} Π^{|i| n(n-1)/2} (E_i^n 1_ν, α(1_{i^{(n)}}))` (ERRATA [BE2] 13). -/
theorem cls_power_eq_dividedPower (n : ℕ) (ν : X) :
    cls Sc sy hc _ ν (upWord (List.replicate n i)) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n •
        Edp sy hc i n _ ν rfl (sy.d i * (n.choose 2 : ℕ))
          (((n.choose 2 : ℕ) : ZMod 2) * D.parity i) := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (D.parity i) with hi | hi
  · exact cls_power_even sy hc i hi n ν
  · match n with
    | 0 => exact cls_power_le_one sy hc i hi 0 (by omega) ν
    | 1 => exact cls_power_le_one sy hc i hi 1 le_rfl ν
    | n + 2 => exact cls_power_odd sy hc i hi n ν

/-! ### The negative half -/

/-- Summand classes do not depend on how the source weight is written. -/
theorem rcls_transport {μ μ' ν : X} (h : μ = μ')
    {f : (show SKM.UGr D Sc sy hc from ⟨μ⟩) ⟶ ⟨ν⟩} {f' : (show SKM.UGr D Sc sy hc from ⟨μ'⟩) ⟶ ⟨ν⟩}
    (hobj : f.obj = f'.obj)
    (y : (SKM.pres D Sc).obj f.obj ⟶ (SKM.pres D Sc).obj f.obj)
    (y' : (SKM.pres D Sc).obj f'.obj ⟶ (SKM.pres D Sc).obj f'.obj) (hy : HEq y y')
    (he : (y : f ⟶ f) ≫ (y : f ⟶ f) = y) (hd : (y : f ⟶ f) ∈ GradedSupercategory.degree (R := k) f f 0)
    (hp : (y : f ⟶ f) ∈ Supercategory.parity (R := k) f f 0)
    (he' : (y' : f' ⟶ f') ≫ (y' : f' ⟶ f') = y')
    (hd' : (y' : f' ⟶ f') ∈ GradedSupercategory.degree (R := k) f' f' 0)
    (hp' : (y' : f' ⟶ f') ∈ Supercategory.parity (R := k) f' f' 0) (n : ℤ) (p : ZMod 2) :
    rcls sy hc he hd hp n p = rcls sy hc he' hd' hp' n p := by
  subst h
  obtain rfl : f = f' := Presentation.Bicat.Hom.ext hobj
  obtain rfl := eq_of_heq hy
  rfl

theorem word_eq_downWordHom (r : ℕ) (ν : X) :
    SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate r i))) rfl =
      CategoricalDividedPowers.downWordHom D Sc sy hc i r ν :=
  Presentation.Bicat.Hom.ext (SKM.chevMap_obj D ν _).symm

theorem cls_eq_down (r : ℕ) (ν : X) :
    cls Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate r i))) rfl 0 0 =
      toGr sy hc _ (-ν) (K₀.mk (SKM.Summands.whole
        (CategoricalDividedPowers.downWordHom D Sc sy hc i r ν))) := by
  change toGr sy hc _ (-ν) (K₀.mk (SKM.Summands.whole
    (SKM.K0Relations.word Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate r i))) rfl))) = _
  rw [word_eq_downWordHom]

/-- **BE2 Lemma 11.5 for `F_i^{(r)}`, even colour, in the Grothendieck ring**:
`[F_i^r 1_{-ν}] = [r]^!_{q_i,π_i} [F_i^{(r)} 1_{-ν}]`, with the corrected divided power. -/
theorem cls_power_down_even (hi : D.parity i = 0) (r : ℕ) (ν : X) :
    cls Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate r i))) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) r •
        Fdp sy hc i r _ ν rfl (-(sy.d i * (r.choose 2 : ℕ))) 0 := by
  have h := CategoricalDividedPowers.class_corrected_down D Sc sy hc i hi r ν
  rw [smul_int, map_qfact] at h
  rw [hi, cls_eq_down, h, toGr_smul_raw, mul_comm (sy.d i)]
  congr 1
  refine rcls_transport sy hc (SKM.wt_flipW D ν _) rfl _ _ ?_ _ _ _ _ _ _ _ _
  rw [SKM.chevHom_map, dpProj, dpIdem_eq_even i hi r]
  apply heq_of_eq
  unfold CategoricalDividedPowers.betaEnd
  dsimp only

/-- **BE2 Lemma 11.5 for `F_i^{(n+2)}`, odd colour, in the Grothendieck ring**. -/
theorem cls_power_down_odd (hi : D.parity i = 1) (n : ℕ) (ν : X) :
    cls Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate (n + 2) i))) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) (n + 2) •
        Fdp sy hc i (n + 2) _ ν rfl (-(sy.d i * ((n + 2).choose 2 : ℕ))) 0 := by
  have h := CategoricalDividedPowers.class_corrected_down_odd D Sc sy hc i hi n ν
  rw [hi, piCoeff_one, ← qUnitPi_eq, cls_eq_down, h]
  rw [toGr_smul_raw, mul_comm (sy.d i)]
  congr 1
  refine rcls_transport sy hc (SKM.wt_flipW D ν _) rfl _ _ ?_ _ _ _ _ _ _ _ _
  rw [SKM.chevHom_map, dpProj, dpIdem_eq_odd i hi (n + 2)]
  apply heq_of_eq
  unfold CategoricalDividedPowers.betaEnd
  dsimp only
  rfl

/-- Lemma 11.5 for `F_i^{(n)}` with at most one strand. -/
theorem cls_power_down_le_one (hi : D.parity i = 1) (n : ℕ) (hn : n ≤ 1) (ν : X) :
    cls Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate n i))) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n •
        Fdp sy hc i n _ ν rfl (-(sy.d i * (n.choose 2 : ℕ))) 0 := by
  have hq : CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n = 1 := by
    interval_cases n <;> simp [CoveringQuantum.qpFact, CoveringQuantum.qpNat]
  have hch : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hp : dpProj sy hc i n _ ν rfl = 𝟙 _ := by
    rw [dpProj, dpIdem_eq_odd i hi n]
    interval_cases n <;> exact (alpha D Sc ν).map_id _
  rw [hq, one_smul, hch, Nat.cast_zero, mul_zero, neg_zero, cls_eq_down]
  have hw : SKM.Summands.whole (k := k) (CategoricalDividedPowers.downWordHom D Sc sy hc i n ν) =
      SKM.Summands.raw (Category.id_comp (𝟙 _)) (GradedSupercategory.id_mem_degree _)
        (Supercategory.id_mem _) 0 0 := (raw_id _ 0 0).symm
  change MulOpposite.op (K₀Ring.mk _) = _
  rw [hw]
  refine rcls_transport sy hc (SKM.wt_flipW D ν _) rfl _ _ ?_ _ _ _ _ _ _ _ _
  rw [hp, CategoryTheory.Functor.map_id]
  rfl

/-- **BE2 Lemma 11.5 for `F_i^{(n)}` in the Grothendieck ring**, every colour and every `n`:
`[F_i^n 1_{-ν}] = [n]^!_{q_i,π_i} [F_i^{(n)} 1_{-ν}]`, where `F_i^{(n)} 1_{-ν}` is the corrected
divided power `Q^{-d_i n(n-1)/2} (F_i^n 1_{-ν}, α'(1_{i^{(n)}}))` (ERRATA [BE2] 13). -/
theorem cls_power_eq_dividedPower_down (n : ℕ) (ν : X) :
    cls Sc sy hc _ (-ν) (SKM.flipW (upWord (List.replicate n i))) rfl 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n •
        Fdp sy hc i n _ ν rfl (-(sy.d i * (n.choose 2 : ℕ))) 0 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (D.parity i) with hi | hi
  · exact cls_power_down_even sy hc i hi n ν
  · match n with
    | 0 => exact cls_power_down_le_one sy hc i hi 0 (by omega) ν
    | 1 => exact cls_power_down_le_one sy hc i hi 1 le_rfl ν
    | n + 2 => exact cls_power_down_odd sy hc i hi n ν

end SerreComplex
end OddMath.QuiverHecke
