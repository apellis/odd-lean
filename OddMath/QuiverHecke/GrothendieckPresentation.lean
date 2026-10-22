/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GrothendieckDividedPowers
import OddMath.CoveringQuantum.UDot.Basic

/-!
# The presentation of `U̇_{q,π}(𝔤)` holds in the Grothendieck ring

Brundan–Ellis, arXiv:1701.04133v2, existence part of Theorem 11.7, over
`ℒ = ℤ[q,q⁻¹,π]/(π² - 1)`. The Grothendieck ring `K₀(𝔘̇(𝔤))` is an `ℒ`-algebra (end of §6;
`IsScalarTower`, `SMulCommClass` for the opposite multiplication of BE2). The assignment
`1_λ ↦ [1_λ]`, `e_i 1_λ ↦ [E_i 1_λ]`, `f_i 1_λ ↦ [F_i 1_λ]` satisfies the defining relations of
`U̇_{q,π}(𝔤)` (§9):

* `comm_gr`: (9.2), from Lemma 11.6 (inversion relations, `K0Relations.comm_same`, `comm_ne`);
* `serreE_sum`, `serreF_sum`: (9.3) and (9.4) with plain powers of the generators and the printed
  coefficients `(-1)^r π_i^{r|j| + r(r-1)/2} [d_ij+1, r]_{q_i,π_i}`. They follow from the
  divided-power form of Lemma 11.6 (`serre_E`, `serre_F`) and Lemma 11.5
  (`cls_power_eq_dividedPower`), using `[N, r] [r]! [N-r]! = [N]!`.

`gammaL` is the resulting `ℒ`-algebra homomorphism from `CoveringUDot ℒ Q q π` into the
Grothendieck ring with an identity adjoined (`Unitization`; the paper's algebras are locally
unital). `gammaL_epow`, `gammaL_fpow` evaluate it on powers of generators. The remaining step of
the existence statement is to extend scalars to `𝕃` and restrict to the `ℒ`-form (9.5)
(`CoveringQuantum.UDot.lForm`).
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke LaurentPolynomial
open CategoryTheory.Idempotents
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w}
  [CommRing k] {Sc : SKM.Scalars D k} (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

namespace SerreComplex
open SKM.K0Relations

instance : IsScalarTower (LaurentPolynomial Zπ) (Grothendieck Sc sy hc) (Grothendieck Sc sy hc) where
  smul_assoc r x y := by
    change MulOpposite.op (y.unop * (letI := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc); r • x.unop)) =
      MulOpposite.op (letI := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc); r • (y.unop * x.unop))
    rw [GSKAR.mul_smul]

instance : SMulCommClass (LaurentPolynomial Zπ) (Grothendieck Sc sy hc) (Grothendieck Sc sy hc) where
  smul_comm r x y := by
    change MulOpposite.op (letI := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc); r • (y.unop * x.unop)) =
      MulOpposite.op ((letI := GSKAR.moduleLaurent k (SKM.UGr D Sc sy hc); r • y.unop) * x.unop)
    rw [GSKAR.smul_mul]

attribute [local instance] SKM.K0Relations.homModule in
theorem toGr_smul_blockClass (r : LaurentPolynomial Zπ) (μ ν : X) (s) (hs : SKM.wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    toGr sy hc μ ν (r • blockClass Sc sy hc μ ν s hs n a) = r • cls Sc sy hc μ ν s hs n a := by
  rw [cls_eq_raw]
  have := toGr_smul_raw sy hc (f := SKM.K0Relations.word Sc sy hc μ ν s hs) (Category.id_comp (𝟙 _))
    (GradedSupercategory.id_mem_degree _) (Supercategory.id_mem _) r n a
  rw [raw_id] at this
  exact this

theorem toGr_blockClass (μ ν : X) (s) (hs : SKM.wt D ν s = μ) (n : ℤ) (a : ZMod 2) :
    toGr sy hc μ ν (blockClass Sc sy hc μ ν s hs n a) = cls Sc sy hc μ ν s hs n a := by
  simpa using toGr_smul_blockClass sy hc 1 μ ν s hs n a

/-- `toGr` on the completed weight block of `K0Relations`. -/
def toGrBlock (μ ν : X) : K₀ (block Sc sy hc μ ν) →+ Grothendieck Sc sy hc := toGr sy hc μ ν

attribute [local instance] SKM.K0Relations.homModule in
theorem toGrBlock_smul (r : LaurentPolynomial Zπ) (μ ν : X) (s) (hs : SKM.wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    toGrBlock sy hc μ ν (r • blockClass Sc sy hc μ ν s hs n a) = r • cls Sc sy hc μ ν s hs n a :=
  toGr_smul_blockClass sy hc r μ ν s hs n a

theorem toGrBlock_blockClass (μ ν : X) (s) (hs : SKM.wt D ν s = μ) (n : ℤ) (a : ZMod 2) :
    toGrBlock sy hc μ ν (blockClass Sc sy hc μ ν s hs n a) = cls Sc sy hc μ ν s hs n a :=
  toGr_blockClass sy hc μ ν s hs n a

theorem id_eq_unitRaw (ν : X) : 𝟙 (weight Sc sy hc ν) = unitRaw sy hc ν 0 0 := by
  rw [unitRaw, raw_id]; rfl

theorem cls_nil (ν : X) : cls Sc sy hc ν ν [] rfl 0 0 = one Sc sy hc ν := by
  rw [cls_eq_raw]
  change _ = MulOpposite.op (K₀Ring.mk (𝟙 (weight Sc sy hc ν)))
  rw [id_eq_unitRaw]

theorem cls_congr {μ μ' ν ν' : X} {s s' : List (SKM.Letter I)} (hμ : μ = μ') (hν : ν = ν')
    (hs : s = s') (h : SKM.wt D ν s = μ) (h' : SKM.wt D ν' s' = μ') (n : ℤ) (a : ZMod 2) :
    cls Sc sy hc μ ν s h n a = cls Sc sy hc μ' ν' s' h' n a := by
  subst hμ hν hs; rfl

theorem piCoeff_add (a b : ZMod 2) : piCoeff (a + b) = piCoeff a * piCoeff b := by
  have hv : (1 : ZMod 2).val = 1 := rfl
  have h : (C Zπ.π : LaurentPolynomial Zπ) ^ 2 = 1 := by
    simpa [piCoeff, hv] using piCoeff_sq 1
  simp only [piCoeff]
  fin_cases a <;> fin_cases b
  · simp
  · simp
  · simp
  · simp [hv, ← pow_two, h]

theorem piCoeff_pow (p : ZMod 2) (e : ℕ) : piCoeff p ^ e = piCoeff (p * e) := by
  induction e with
  | zero => simp [piCoeff]
  | succ e ih => rw [pow_succ (piCoeff p) e, ih, ← piCoeff_add]; push_cast; ring_nf

theorem piCoeff_smul_Edp (i : I) (n : ℕ) (μ ν : X) (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ)
    (m : ℤ) (a p : ZMod 2) :
    piCoeff p • Edp sy hc i n μ ν hs m a = Edp sy hc i n μ ν hs m (a + p) := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) p with rfl | rfl
  · simp [piCoeff]
  · change (C Zπ.π ^ 1 : LaurentPolynomial Zπ) • _ = _
    rw [pow_one]
    exact pi_smul_rcls sy hc (dpProj_idem sy hc n μ ν hs)
      (alpha_mem_degree D Sc sy ν (dpIdem_degree sy hc n))
      (alpha_mem_parity D Sc ν (dpIdem_even sy hc n)) m a

theorem piCoeff_smul_Fdp (i : I) (n : ℕ) (μ ν : X) (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ)
    (m : ℤ) (a p : ZMod 2) :
    piCoeff p • Fdp sy hc i n μ ν hs m a = Fdp sy hc i n μ ν hs m (a + p) := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) p with rfl | rfl
  · simp [piCoeff]
  · change (C Zπ.π ^ 1 : LaurentPolynomial Zπ) • _ = _
    rw [pow_one]
    exact pi_smul_rcls sy hc _ _ _ m a

/-! ### Words in the generators -/

variable (i : I)

theorem cls_rep_succ (n : ℕ) (ν : X) :
    E Sc sy hc i (ν + n • D.α i) *
        cls Sc sy hc _ ν (upWord (List.replicate n i)) (wt_rep ν n) 0 0 =
      cls Sc sy hc _ ν (upWord (List.replicate (n + 1) i)) (wt_rep ν (n + 1)) 0 0 := by
  rw [E, cls_mul_cls]
  exact cls_congr sy hc (by rw [add_smul, one_smul, add_assoc]) rfl rfl _ _ _ _

theorem wt_rep_down (ν : X) (n : ℕ) :
    SKM.wt D ν (SKM.flipW (upWord (List.replicate n i))) = ν - n • D.α i := by
  have h := SKM.wt_flipW D (-ν) (upWord (List.replicate n i))
  rw [neg_neg] at h
  rw [h, wt_rep]; abel

theorem cls_rep_down_succ (n : ℕ) (ν : X) :
    F Sc sy hc i (ν - n • D.α i) *
        cls Sc sy hc _ ν (SKM.flipW (upWord (List.replicate n i))) (wt_rep_down i ν n) 0 0 =
      cls Sc sy hc _ ν (SKM.flipW (upWord (List.replicate (n + 1) i))) (wt_rep_down i ν (n + 1))
        0 0 := by
  rw [F, cls_mul_cls]
  exact cls_congr sy hc (by rw [add_smul, one_smul]; abel) rfl rfl _ _ _ _

/-- Lemma 11.5 at a weight `ν`, with the source weight written `ν + n αᵢ`. -/
theorem cls_rep_eq (n : ℕ) (ν : X) :
    cls Sc sy hc _ ν (upWord (List.replicate n i)) (wt_rep ν n) 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n •
        Edp sy hc i n _ ν (wt_rep ν n) (sy.d i * (n.choose 2 : ℕ))
          (((n.choose 2 : ℕ) : ZMod 2) * D.parity i) :=
  (cls_congr sy hc (wt_rep ν n).symm rfl rfl _ rfl 0 0).trans
    ((cls_power_eq_dividedPower sy hc i n ν).trans
      (congrArg _ (Edp_congr sy hc rfl (wt_rep ν n) rfl rfl rfl _ _)))

/-- Lemma 11.5 for `F`, at a weight `ν`. -/
theorem cls_rep_down_eq (n : ℕ) (ν : X) :
    cls Sc sy hc _ ν (SKM.flipW (upWord (List.replicate n i))) (wt_rep_down i ν n) 0 0 =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n •
        Fdp sy hc i n _ (-ν) (wt_rep (-ν) n) (-(sy.d i * (n.choose 2 : ℕ))) 0 := by
  refine (cls_congr sy hc ?_ (neg_neg ν).symm rfl _ rfl 0 0).trans
    ((cls_power_eq_dividedPower_down sy hc i n (-ν)).trans
      (congrArg _ (Fdp_congr sy hc rfl (wt_rep (-ν) n) rfl rfl rfl _ _)))
  rw [SKM.wt_flipW, wt_rep]; abel

theorem qpFact_one_eq : CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) 1 = 1 := by
  simp [CoveringQuantum.qpFact, CoveringQuantum.qpNat]

theorem E_eq_Edp (ν μ : X) (h : SKM.wt D ν (upWord (List.replicate 1 i)) = μ) :
    E Sc sy hc i ν = Edp sy hc i 1 μ ν h 0 0 := by
  rw [E]
  refine (cls_congr sy hc (μ' := ν + 1 • D.α i) (s' := upWord (List.replicate 1 i))
    (by rw [one_smul]) rfl rfl _ (wt_rep ν 1) 0 0).trans ?_
  rw [cls_rep_eq, qpFact_one_eq, one_smul]
  exact Edp_congr sy hc rfl (h.symm.trans (wt_rep ν 1)).symm rfl (by simp) (by simp) _ _

theorem F_eq_Fdp (ν μ : X) (h : SKM.wt D (-ν) (upWord (List.replicate 1 i)) = μ) :
    F Sc sy hc i ν = Fdp sy hc i 1 μ (-ν) h 0 0 := by
  rw [F]
  refine (cls_congr sy hc (μ' := ν - 1 • D.α i)
    (s' := SKM.flipW (upWord (List.replicate 1 i)))
    (by rw [one_smul]) rfl rfl _ (wt_rep_down i ν 1) 0 0).trans ?_
  rw [cls_rep_down_eq, qpFact_one_eq, one_smul]
  exact Fdp_congr sy hc rfl (h.symm.trans (wt_rep (-ν) 1)).symm rfl (by simp) rfl _ _

/-! ### The Serre relations -/

variable (j : I) (M : ℕ)

/-- The printed Serre coefficient `(-1)^r π_i^{r|j| + r(r-1)/2} [M, r]_{q_i,π_i}` of (9.3). -/
abbrev serreC (r : ℕ) : LaurentPolynomial Zπ :=
  (-1) ^ r * piCoeff (D.parity i) ^ (r * (D.parity j).val + r.choose 2) *
    CoveringQuantum.qpBinom (qUnit (sy.d i)) (piCoeff (D.parity i)) M r

omit [CommRing k] in
theorem serreC_mul {r : ℕ} (hr : r ≤ M) :
    serreC sy i j M r * CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) (M - r) *
        CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) r =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M * (-1) ^ r *
        piCoeff (D.parity i * ((r : ZMod 2) * D.parity j + ((r.choose 2 : ℕ) : ZMod 2))) := by
  rw [serreC, piCoeff_pow, ← CoveringQuantum.qpBinom_mul_qpFact hr]
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

theorem serre_term (ν : X) {r : ℕ} (hr : r ≤ M) :
    serreC sy i j M r •
      (cls Sc sy hc _ (ν + r • D.α i + D.α j) (upWord (List.replicate (M - r) i)) (wt_rep _ _) 0 0 *
        E Sc sy hc j (ν + r • D.α i) *
        cls Sc sy hc _ ν (upWord (List.replicate r i)) (wt_rep ν r) 0 0) =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M • ((-1 : ℤ) ^ r •
        (Edp sy hc i (M - r) _ (ν + r • D.α i + D.α j) (wt_rep _ _) (sy.d i * ((M - r).choose 2 : ℕ))
            ((((M - r).choose 2 : ℕ) : ZMod 2) * D.parity i) *
          Edp sy hc j 1 (ν + r • D.α i + D.α j) (ν + r • D.α i) (wt_mid ν r) 0 0 *
          Edp sy hc i r (ν + r • D.α i) ν (wt_rep ν r) (sy.d i * (r.choose 2 : ℕ))
            (parR D i j r))) := by
  rw [cls_rep_eq, cls_rep_eq, E_eq_Edp sy hc j _ _ (wt_mid ν r), ← piCoeff_smul_Edp]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Int.cast_smul_eq_zsmul (LaurentPolynomial Zπ)]
  congr 1
  push_cast
  linear_combination serreC_mul sy i j M hr

/-- **BE2 (9.3) in the Grothendieck ring**: for `i ≠ j` and `M = d_ij + 1`,
`∑_r (-1)^r π_i^{r|j| + r(r-1)/2} [M, r]_{q_i,π_i} [E_i^{M-r} E_j E_i^r 1_ν] = 0`, with plain
powers of the generators. It follows from Lemma 11.6 (`serre_E`) and Lemma 11.5
(`cls_power_eq_dividedPower`). -/
theorem serreE_sum (ν : X) (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∑ r ∈ Finset.range (M + 1), serreC sy i j M r •
      (cls Sc sy hc _ (ν + r • D.α i + D.α j) (upWord (List.replicate (M - r) i)) (wt_rep _ _) 0 0 *
        E Sc sy hc j (ν + r • D.α i) *
        cls Sc sy hc _ ν (upWord (List.replicate r i)) (wt_rep ν r) 0 0) = 0 := by
  rw [Finset.sum_congr rfl fun r hr =>
    serre_term sy hc i j M ν (Nat.le_of_lt_succ (Finset.mem_range.mp hr)), ← Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun r => (-1 : ℤ) ^ r •
        (Edp sy hc i (M - r) _ (ν + r • D.α i + D.α j) (wt_rep _ _) (sy.d i * ((M - r).choose 2 : ℕ))
            ((((M - r).choose 2 : ℕ) : ZMod 2) * D.parity i) *
          Edp sy hc j 1 (ν + r • D.α i + D.α j) (ν + r • D.α i) (wt_mid ν r) 0 0 *
          Edp sy hc i r (ν + r • D.α i) ν (wt_rep ν r) (sy.d i * (r.choose 2 : ℕ))
            (parR D i j r)))]
  refine (congrArg (CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M • ·)
    ?_).trans (smul_zero _)
  refine Eq.trans ?_ (serre_E sy hc ν hij hM)
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 3
  exact Edp_congr sy hc rfl ((wt_rep _ _).symm.trans
    (wt_left' ν (Nat.sub_add_cancel (Nat.le_of_lt_succ r.2)))) rfl rfl rfl _ _

theorem serre_term_down (ν : X) {r : ℕ} (hr : r ≤ M) :
    serreC sy i j M r •
      (cls Sc sy hc _ (ν - r • D.α i - D.α j) (SKM.flipW (upWord (List.replicate (M - r) i)))
          (wt_rep_down i _ _) 0 0 *
        F Sc sy hc j (ν - r • D.α i) *
        cls Sc sy hc _ ν (SKM.flipW (upWord (List.replicate r i))) (wt_rep_down i ν r) 0 0) =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M • ((-1 : ℤ) ^ r •
        (Fdp sy hc i (M - r) _ (-(ν - r • D.α i - D.α j)) (wt_rep _ _)
            (-(sy.d i * ((M - r).choose 2 : ℕ))) 0 *
          Fdp sy hc j 1 (-ν + r • D.α i + D.α j) (-(ν - r • D.α i))
            (by rw [wt_rep, one_smul]; abel) 0 0 *
          Fdp sy hc i r _ (-ν) (wt_rep (-ν) r) (-(sy.d i * (r.choose 2 : ℕ)))
            (parF D i j r))) := by
  rw [cls_rep_down_eq, cls_rep_down_eq, F_eq_Fdp sy hc j _ (-ν + r • D.α i + D.α j) (by rw [wt_rep, one_smul]; abel),
    show parF D i j r = 0 + parF D i j r from (zero_add _).symm, ← piCoeff_smul_Fdp]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Int.cast_smul_eq_zsmul (LaurentPolynomial Zπ)]
  congr 1
  push_cast
  linear_combination serreC_mul sy i j M hr

/-- **BE2 (9.4) in the Grothendieck ring**: for `i ≠ j` and `M = d_ij + 1`,
`∑_r (-1)^r π_i^{r|j| + r(r-1)/2} [M, r]_{q_i,π_i} [F_i^{M-r} F_j F_i^r 1_ν] = 0`, with plain
powers of the generators. It follows from Lemma 11.6 (`serre_F`) and Lemma 11.5
(`cls_power_eq_dividedPower_down`). -/
theorem serreF_sum (ν : X) (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∑ r ∈ Finset.range (M + 1), serreC sy i j M r •
      (cls Sc sy hc _ (ν - r • D.α i - D.α j) (SKM.flipW (upWord (List.replicate (M - r) i)))
          (wt_rep_down i _ _) 0 0 *
        F Sc sy hc j (ν - r • D.α i) *
        cls Sc sy hc _ ν (SKM.flipW (upWord (List.replicate r i))) (wt_rep_down i ν r) 0 0) = 0 := by
  rw [Finset.sum_congr rfl fun r hr =>
    serre_term_down sy hc i j M ν (Nat.le_of_lt_succ (Finset.mem_range.mp hr)), ← Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun r => (-1 : ℤ) ^ r •
        (Fdp sy hc i (M - r) _ (-(ν - r • D.α i - D.α j)) (wt_rep _ _)
            (-(sy.d i * ((M - r).choose 2 : ℕ))) 0 *
          Fdp sy hc j 1 (-ν + r • D.α i + D.α j) (-(ν - r • D.α i))
            (by rw [wt_rep, one_smul]; abel) 0 0 *
          Fdp sy hc i r _ (-ν) (wt_rep (-ν) r) (-(sy.d i * (r.choose 2 : ℕ)))
            (parF D i j r)))]
  refine (congrArg (CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M • ·)
    ?_).trans (smul_zero _)
  refine Eq.trans ?_ (serre_F sy hc (-ν) hij hM)
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := Nat.le_of_lt_succ r.2
  rw [Fdp_congr sy hc rfl
      (show -(ν - (r : ℕ) • D.α i - D.α j) + (M - r) • D.α i = -ν + (M • D.α i + D.α j) by
        rw [sub_nsmul _ hr]; abel)
      (show -(ν - (r : ℕ) • D.α i - D.α j) = -ν + (r : ℕ) • D.α i + D.α j by abel) rfl rfl
      (wt_rep _ _) (wt_left' (-ν) (Nat.sub_add_cancel hr)),
    Fdp_congr sy hc rfl rfl (show -(ν - (r : ℕ) • D.α i) = -ν + (r : ℕ) • D.α i by abel) rfl rfl
      _ (wt_mid (-ν) r)]

/-! ### The commutation relation -/

theorem wt_up_dn (μ : X) : SKM.wt D μ [SKM.up i, SKM.dn j] = μ + D.α i - D.α j := by
  simp only [SKM.wt, SKM.sh]; abel_nf

theorem wt_dn_up (μ : X) : SKM.wt D μ [SKM.dn j, SKM.up i] = μ + D.α i - D.α j := by
  simp only [SKM.wt, SKM.sh]; abel_nf

theorem E_mul_F (μ : X) :
    E Sc sy hc i (μ - D.α j) * F Sc sy hc j μ =
      cls Sc sy hc (μ + D.α i - D.α j) μ [SKM.up i, SKM.dn j] (wt_up_dn i j μ) 0 0 := by
  rw [E, F, cls_mul_cls]
  exact cls_congr sy hc (by abel) rfl rfl _ _ _ _

theorem F_mul_E (μ : X) :
    F Sc sy hc j (μ + D.α i) * E Sc sy hc i μ =
      cls Sc sy hc (μ + D.α i - D.α j) μ [SKM.dn j, SKM.up i] (wt_dn_up i j μ) 0 0 := by
  rw [F, E, cls_mul_cls]
  exact cls_congr sy hc rfl rfl rfl _ _ _ _

attribute [local instance] SKM.K0Relations.homModule in
theorem comm_gr_ne (μ : X) (h : i ≠ j) :
    cls Sc sy hc (μ + D.α i - D.α j) μ [SKM.up i, SKM.dn j] (wt_up_dn i j μ) 0 0 -
        piCoeff (D.parity i * D.parity j) •
          cls Sc sy hc (μ + D.α i - D.α j) μ [SKM.dn j, SKM.up i] (wt_dn_up i j μ) 0 0 = 0 := by
  calc _ = toGrBlock sy hc (μ + D.α i - D.α j) μ
        (blockClass Sc sy hc _ μ [SKM.up i, SKM.dn j] (wt_up_dn i j μ) 0 0) -
      toGrBlock sy hc (μ + D.α i - D.α j) μ (piCoeff (D.parity i * D.parity j) •
        blockClass Sc sy hc _ μ [SKM.dn j, SKM.up i] (wt_dn_up i j μ) 0 0) :=
        congrArg₂ (· - ·) (toGrBlock_blockClass sy hc _ μ _ _ 0 0).symm
          (toGrBlock_smul sy hc _ _ μ _ _ 0 0).symm
    _ = toGrBlock sy hc (μ + D.α i - D.α j) μ
        (blockClass Sc sy hc _ μ [SKM.up i, SKM.dn j] (wt_up_dn i j μ) 0 0 -
          piCoeff (D.parity i * D.parity j) •
            blockClass Sc sy hc _ μ [SKM.dn j, SKM.up i] (wt_dn_up i j μ) 0 0) :=
        (map_sub _ _ _).symm
    _ = 0 := (congrArg _ (comm_ne Sc sy hc i j μ _ (wt_up_dn i j μ) (wt_dn_up i j μ) h)).trans
        (map_zero _)

theorem comm_gr_same (μ : X) :
    cls Sc sy hc (μ + D.α i - D.α i) μ [SKM.up i, SKM.dn i] (wt_up_dn i i μ) 0 0 -
        piCoeff (D.parity i) •
          cls Sc sy hc (μ + D.α i - D.α i) μ [SKM.dn i, SKM.up i] (wt_dn_up i i μ) 0 0 =
      CoveringQuantum.qpInt (qUnit (sy.d i)) (piCoeff (D.parity i)) (D.h i μ) •
        one Sc sy hc μ := by
  rw [cls_congr sy hc (add_sub_cancel_right μ (D.α i)) rfl rfl _ (by simp [SKM.wt, SKM.sh]),
    cls_congr sy hc (add_sub_cancel_right μ (D.α i)) rfl rfl _ (by simp [SKM.wt, SKM.sh])]
  refine Eq.trans ?_ ((congrArg (toGrBlock sy hc μ μ) (comm_same Sc sy hc i μ)).trans
    ((toGrBlock_smul sy hc _ μ μ [] rfl 0 0).trans (congrArg _ (cls_nil sy hc μ))))
  exact (congrArg₂ (· - ·) (toGrBlock_blockClass sy hc μ μ _ _ 0 0).symm
    (toGrBlock_smul sy hc _ μ μ _ _ 0 0).symm).trans (map_sub _ _ _).symm

/-- **BE2 (9.2) in the Grothendieck ring**, in the coefficient convention of
`CoveringQuantum.UDot.Rel.comm`:
`[E_i F_j 1_μ] - π^{|i||j|} [F_j E_i 1_μ] = δ_ij [⟨h_i, μ⟩]_{q_i,π_i} 1_μ`. -/
theorem comm_gr (μ : X) :
    E Sc sy hc i (μ - D.α j) * F Sc sy hc j μ -
        piCoeff (D.parity i * D.parity j) • (F Sc sy hc j (μ + D.α i) * E Sc sy hc i μ) =
      if i = j then
        CoveringQuantum.qpInt (qUnit (sy.d i)) (piCoeff (D.parity i)) (D.h i μ) • one Sc sy hc μ
      else 0 := by
  rw [E_mul_F, F_mul_E]
  split_ifs with h
  · subst h
    have hp : D.parity i * D.parity i = D.parity i := by
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (D.parity i) with h | h <;> rw [h] <;> rfl
    rw [hp]
    exact comm_gr_same sy hc i μ
  · exact comm_gr_ne sy hc i j μ h

/-! ### The homomorphism from `U̇_{q,π}(𝔤)` over `ℒ` -/

section Covering

variable (Q : CoveringQuantum.RootDatum I X) {S : SKM.Scalars Q.toSKM k} (hS : S.Homogeneous)

/-- The Grothendieck ring of `𝔘̇_{q,π}(𝔤)` with an identity adjoined, as an `ℒ`-algebra. -/
abbrev GrUnit := Unitization (LaurentPolynomial Zπ) (Grothendieck S Q.skmSymmetrizer hS)

/-- The generators of `U̇_{q,π}(𝔤)` go to the classes `1_λ`, `[E_i 1_λ]`, `[F_i 1_λ]`. -/
def gammaGen : CoveringQuantum.UDot.Gen I X → GrUnit Q hS
  | .one μ => Unitization.inr (one S Q.skmSymmetrizer hS μ)
  | .e i μ => Unitization.inr (E S Q.skmSymmetrizer hS i μ)
  | .f i μ => Unitization.inr (F S Q.skmSymmetrizer hS i μ)

/-- The assignment of Theorem 11.7 on the free algebra. -/
def gammaFree : CoveringQuantum.UDot.Free (LaurentPolynomial Zπ) I X →ₐ[LaurentPolynomial Zπ]
    GrUnit Q hS :=
  FreeAlgebra.lift _ (gammaGen Q hS)

theorem gammaFree_one (μ : X) :
    gammaFree Q hS (CoveringQuantum.UDot.Free.one _ μ) =
      Unitization.inr (one S Q.skmSymmetrizer hS μ) :=
  FreeAlgebra.lift_ι_apply _ _

theorem gammaFree_E (i : I) (μ : X) :
    gammaFree Q hS (CoveringQuantum.UDot.Free.E _ i μ) =
      Unitization.inr (E S Q.skmSymmetrizer hS i μ) :=
  FreeAlgebra.lift_ι_apply _ _

theorem gammaFree_F (i : I) (μ : X) :
    gammaFree Q hS (CoveringQuantum.UDot.Free.F _ i μ) =
      Unitization.inr (F S Q.skmSymmetrizer hS i μ) :=
  FreeAlgebra.lift_ι_apply _ _

theorem gammaFree_epow (i : I) (n : ℕ) (μ : X) :
    gammaFree Q hS (CoveringQuantum.UDot.epow Q i n μ) = Unitization.inr
      (cls S Q.skmSymmetrizer hS _ μ (upWord (List.replicate n i)) (wt_rep μ n) 0 0) := by
  induction n with
  | zero =>
    rw [CoveringQuantum.UDot.epow, gammaFree_one, ← cls_nil]
    exact congrArg _ (cls_congr _ _ (by simp) rfl rfl _ _ _ _)
  | succ n ih =>
    rw [CoveringQuantum.UDot.epow, map_mul, ih, gammaFree_E, ← Unitization.inr_mul]
    exact congrArg _ (cls_rep_succ (Sc := S) Q.skmSymmetrizer hS i n μ)

theorem gammaFree_fpow (i : I) (n : ℕ) (μ : X) :
    gammaFree Q hS (CoveringQuantum.UDot.fpow Q i n μ) = Unitization.inr
      (cls S Q.skmSymmetrizer hS _ μ (SKM.flipW (upWord (List.replicate n i)))
        (wt_rep_down i μ n) 0 0) := by
  induction n with
  | zero =>
    rw [CoveringQuantum.UDot.fpow, gammaFree_one, ← cls_nil]
    exact congrArg _ (cls_congr _ _ (by simp) rfl rfl _ _ _ _)
  | succ n ih =>
    rw [CoveringQuantum.UDot.fpow, map_mul, ih, gammaFree_F, ← Unitization.inr_mul]
    exact congrArg _ (cls_rep_down_succ (Sc := S) Q.skmSymmetrizer hS i n μ)

theorem serreCoeff_eq (i j : I) (r : ℕ) :
    Q.serreCoeff (qUnit 1) (C Zπ.π) i j r = serreC Q.skmSymmetrizer i j (Q.serreDeg i j) r := by
  rw [CoveringQuantum.SuperCartanDatum.serreCoeff, root_qi]
  rfl

theorem serreDeg_eq {i j : I} (h : i ≠ j) : Q.serreDeg i j = Q.toSKM.dn i j + 1 := by
  have := Q.isGCM.offDiag_nonpos i j h
  simp only [CoveringQuantum.SuperCartanDatum.serreDeg, SKM.Datum.dn,
    CoveringQuantum.RootDatum.toSKM_d]
  omega

theorem inr_mul' (a b : Grothendieck S Q.skmSymmetrizer hS) :
    (Unitization.inr a : GrUnit Q hS) * Unitization.inr b = Unitization.inr (a * b) :=
  (Unitization.inr_mul (LaurentPolynomial Zπ) a b).symm

theorem inr_sub' (a b : Grothendieck S Q.skmSymmetrizer hS) :
    (Unitization.inr a : GrUnit Q hS) - Unitization.inr b = Unitization.inr (a - b) :=
  (Unitization.inr_sub (LaurentPolynomial Zπ) a b).symm

theorem inr_smul' (r : LaurentPolynomial Zπ) (a : Grothendieck S Q.skmSymmetrizer hS) :
    r • (Unitization.inr a : GrUnit Q hS) = Unitization.inr (r • a) :=
  (Unitization.inr_smul (LaurentPolynomial Zπ) r a).symm

theorem gammaFree_mul {x y : CoveringQuantum.UDot.Free (LaurentPolynomial Zπ) I X}
    {a b : Grothendieck S Q.skmSymmetrizer hS} (hx : gammaFree Q hS x = Unitization.inr a)
    (hy : gammaFree Q hS y = Unitization.inr b) :
    gammaFree Q hS (x * y) = Unitization.inr (a * b) :=
  ((map_mul _ x y).trans (congrArg₂ (· * ·) hx hy)).trans (inr_mul' Q hS a b)

theorem gammaFree_sub {x y : CoveringQuantum.UDot.Free (LaurentPolynomial Zπ) I X}
    {a b : Grothendieck S Q.skmSymmetrizer hS} (hx : gammaFree Q hS x = Unitization.inr a)
    (hy : gammaFree Q hS y = Unitization.inr b) :
    gammaFree Q hS (x - y) = Unitization.inr (a - b) :=
  ((map_sub _ x y).trans (congrArg₂ (· - ·) hx hy)).trans (inr_sub' Q hS a b)

theorem gammaFree_smul {x : CoveringQuantum.UDot.Free (LaurentPolynomial Zπ) I X}
    {a : Grothendieck S Q.skmSymmetrizer hS} (r : LaurentPolynomial Zπ)
    (hx : gammaFree Q hS x = Unitization.inr a) :
    gammaFree Q hS (r • x) = Unitization.inr (r • a) :=
  ((map_smul _ r x).trans (congrArg (r • ·) hx)).trans (inr_smul' Q hS r a)

theorem gammaFree_serreE (i j : I) (μ : X) (h : i ≠ j) :
    gammaFree Q hS (CoveringQuantum.UDot.serreE Q (qUnit 1) (C Zπ.π) i j μ) = gammaFree Q hS 0 := by
    rw [map_zero, CoveringQuantum.UDot.serreE, map_sum]
    refine (Finset.sum_congr rfl fun r _ => gammaFree_smul Q hS _
      (gammaFree_mul Q hS (gammaFree_mul Q hS (gammaFree_epow Q hS i _ _) (gammaFree_E Q hS j _))
        (gammaFree_epow Q hS i r μ))).trans ?_
    refine (map_sum (Unitization.inrNonUnitalAlgHom (LaurentPolynomial Zπ) _) _ _).symm.trans
      ((congrArg Unitization.inr ?_).trans (Unitization.inr_zero _))
    simp only [serreCoeff_eq]
    exact serreE_sum (Sc := S) Q.skmSymmetrizer hS i j (Q.serreDeg i j) μ h (serreDeg_eq Q h)

theorem gammaFree_serreF (i j : I) (μ : X) (h : i ≠ j) :
    gammaFree Q hS (CoveringQuantum.UDot.serreF Q (qUnit 1) (C Zπ.π) i j μ) = gammaFree Q hS 0 := by

    rw [map_zero, CoveringQuantum.UDot.serreF, map_sum]
    refine (Finset.sum_congr rfl fun r _ => gammaFree_smul Q hS _
      (gammaFree_mul Q hS (gammaFree_mul Q hS (gammaFree_fpow Q hS i _ _) (gammaFree_F Q hS j _))
        (gammaFree_fpow Q hS i r μ))).trans ?_
    refine (map_sum (Unitization.inrNonUnitalAlgHom (LaurentPolynomial Zπ) _) _ _).symm.trans
      ((congrArg Unitization.inr ?_).trans (Unitization.inr_zero _))
    simp only [serreCoeff_eq]
    exact serreF_sum (Sc := S) Q.skmSymmetrizer hS i j (Q.serreDeg i j) μ h (serreDeg_eq Q h)

variable [DecidableEq I] [DecidableEq X]

theorem gammaFree_rel ⦃x y : CoveringQuantum.UDot.Free (LaurentPolynomial Zπ) I X⦄
    (h : CoveringQuantum.UDot.Rel Q (qUnit 1) (C Zπ.π) x y) :
    gammaFree Q hS x = gammaFree Q hS y := by
  cases h with
  | one_one μ ν =>
    refine (gammaFree_mul Q hS (gammaFree_one Q hS μ) (gammaFree_one Q hS ν)).trans ?_
    rw [one_mul_one]
    by_cases h : μ = ν
    · simp only [h, ite_true, gammaFree_one]
    · simp only [h, ite_false, map_zero, Unitization.inr_zero]
  | one_E i μ =>
    exact (gammaFree_mul Q hS (gammaFree_one Q hS _) (gammaFree_E Q hS i μ)).trans
      ((congrArg _ ((weight_relations S Q.skmSymmetrizer hS).2.1 i μ)).trans
        (gammaFree_E Q hS i μ).symm)
  | E_one i μ =>
    exact (gammaFree_mul Q hS (gammaFree_E Q hS i μ) (gammaFree_one Q hS _)).trans
      ((congrArg _ ((weight_relations S Q.skmSymmetrizer hS).2.2.1 i μ)).trans
        (gammaFree_E Q hS i μ).symm)
  | one_F i μ =>
    exact (gammaFree_mul Q hS (gammaFree_one Q hS _) (gammaFree_F Q hS i μ)).trans
      ((congrArg _ ((weight_relations S Q.skmSymmetrizer hS).2.2.2.1 i μ)).trans
        (gammaFree_F Q hS i μ).symm)
  | F_one i μ =>
    exact (gammaFree_mul Q hS (gammaFree_F Q hS i μ) (gammaFree_one Q hS _)).trans
      ((congrArg _ ((weight_relations S Q.skmSymmetrizer hS).2.2.2.2 i μ)).trans
        (gammaFree_F Q hS i μ).symm)
  | comm i j μ =>
    refine (gammaFree_sub Q hS (gammaFree_mul Q hS (gammaFree_E Q hS i _) (gammaFree_F Q hS j μ))
      (gammaFree_smul Q hS _ (gammaFree_mul Q hS (gammaFree_F Q hS j _)
        (gammaFree_E Q hS i μ)))).trans ?_
    have hc := comm_gr (Sc := S) Q.skmSymmetrizer hS i j μ
    split_ifs at hc ⊢ with h
    · subst h
      rw [root_qi]
      exact (congrArg _ hc).trans (gammaFree_smul Q hS _ (gammaFree_one Q hS μ)).symm
    · exact (congrArg _ hc).trans ((Unitization.inr_zero _).trans (map_zero _).symm)
  | serreE i j μ h => exact gammaFree_serreE Q hS i j μ h
  | serreF i j μ h => exact gammaFree_serreF Q hS i j μ h

/-- **The algebra homomorphism of BE2 Theorem 11.7 over `ℒ = ℤ[q,q⁻¹,π]/(π²-1)`**:
`1_λ ↦ [1_λ]`, `e_i 1_λ ↦ [E_i 1_λ]`, `f_i 1_λ ↦ [F_i 1_λ]` respects the relations (9.2)–(9.4)
of `U̇_{q,π}(𝔤)` at `q ↦ q`, `π ↦ π`, so it descends to an `ℒ`-algebra homomorphism into the
Grothendieck ring of `𝔘̇(𝔤)` with an identity adjoined. -/
def gammaL : CoveringQuantum.CoveringUDot (LaurentPolynomial Zπ) Q (qUnit 1) (C Zπ.π) →ₐ[LaurentPolynomial Zπ]
    GrUnit Q hS :=
  RingQuot.liftAlgHom _ ⟨gammaFree Q hS, gammaFree_rel Q hS⟩

theorem gammaL_mk (x : CoveringQuantum.UDot.Free (LaurentPolynomial Zπ) I X) :
    gammaL Q hS (CoveringQuantum.UDot.mk Q (qUnit 1) (C Zπ.π) x) = gammaFree Q hS x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem gammaL_one (μ : X) :
    gammaL Q hS (CoveringQuantum.UDot.one Q (qUnit 1) (C Zπ.π) μ) =
      Unitization.inr (one S Q.skmSymmetrizer hS μ) :=
  (gammaL_mk Q hS _).trans (gammaFree_one Q hS μ)

theorem gammaL_E (i : I) (μ : X) :
    gammaL Q hS (CoveringQuantum.UDot.E Q (qUnit 1) (C Zπ.π) i μ) =
      Unitization.inr (E S Q.skmSymmetrizer hS i μ) :=
  (gammaL_mk Q hS _).trans (gammaFree_E Q hS i μ)

theorem gammaL_F (i : I) (μ : X) :
    gammaL Q hS (CoveringQuantum.UDot.F Q (qUnit 1) (C Zπ.π) i μ) =
      Unitization.inr (F S Q.skmSymmetrizer hS i μ) :=
  (gammaL_mk Q hS _).trans (gammaFree_F Q hS i μ)

/-- Lemma 11.5 through `γ`: `γ(e_i^n 1_μ) = [n]!_{q_i,π_i} [E_i^{(n)} 1_μ]`, with the corrected
divided power (ERRATA [BE2] 13). -/
theorem gammaL_epow (i : I) (n : ℕ) (μ : X) :
    gammaL Q hS (CoveringQuantum.UDot.mk Q (qUnit 1) (C Zπ.π) (CoveringQuantum.UDot.epow Q i n μ)) =
      Unitization.inr (CoveringQuantum.qpFact (Q.qi (qUnit 1) i) (Q.pii (C Zπ.π) i) n •
        Edp Q.skmSymmetrizer hS i n _ μ (wt_rep μ n) (Q.d i * (n.choose 2 : ℕ))
          (((n.choose 2 : ℕ) : ZMod 2) * Q.parity i)) := by
  rw [gammaL_mk, gammaFree_epow, cls_rep_eq, root_qi]
  rfl

/-- Lemma 11.5 through `γ`: `γ(f_i^n 1_μ) = [n]!_{q_i,π_i} [F_i^{(n)} 1_μ]`. -/
theorem gammaL_fpow (i : I) (n : ℕ) (μ : X) :
    gammaL Q hS (CoveringQuantum.UDot.mk Q (qUnit 1) (C Zπ.π) (CoveringQuantum.UDot.fpow Q i n μ)) =
      Unitization.inr (CoveringQuantum.qpFact (Q.qi (qUnit 1) i) (Q.pii (C Zπ.π) i) n •
        Fdp Q.skmSymmetrizer hS i n _ (-μ) (wt_rep (-μ) n) (-(Q.d i * (n.choose 2 : ℕ))) 0) := by
  rw [gammaL_mk, gammaFree_fpow, cls_rep_down_eq, root_qi]
  rfl

end Covering

end SerreComplex
end OddMath.QuiverHecke
