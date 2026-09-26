import OddMath.Frontier.EKGeneralQCoideal

/-!
# EK Proposition 2.3 (coideal part) fails over `ℤ/4` at `q = 2`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, p.8, Proposition 2.3
(`Δ(I) ⊂ I ⊗ Λ' + Λ' ⊗ I`) and Corollary 2.4, for "`q ∈ k`" with `k` an arbitrary commutative
ring.

Take `k = ℤ/4`, `q = 2`.  In degree `2` the Gram matrix is `[[3,1],[1,1]]`, so
`I₂ = {0, 2(h₁₁ - h₂)}` and `Λ₂ ≅ ℤ/4 ⊕ ℤ/2`.

* `xc = h₁₂₁ + h₁₃ + h₃₁ + h₄` lies in `I` (`xc_mem_radical`, from the §5.2 table at `q = 2`);
* `ψ : Λ' → ℤ/2`, the coefficient of `h₁₁` reduced mod `2`, kills `I` (`psi4_radical`);
* `(ψ ⊗ ψ)(Δ xc) = 1` (`psi4_tensor_coproduct`), while `ψ ⊗ ψ` kills `I ⊗ Λ' + Λ' ⊗ I`.

Hence `Δ(xc) ∉ I ⊗ Λ' + Λ' ⊗ I` (`coideal_counterexample`), and no linear map `Λ → Λ ⊗ Λ` is
induced by `Δ` (`no_quotient_coproduct`), so Corollary 2.4 fails as well.  The repaired
statements are in `EKGeneralQCoideal`.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKFreeCoproduct (W degree partWord partWord_degree)

/-! ## Words of a given degree from an explicit list of compositions -/

theorem word_mem_list {n : ℕ} (Ls : List (List ℕ)) (hpos : ∀ l ∈ Ls, ∀ a ∈ l, 0 < a)
    (hsum : ∀ l ∈ Ls, l.sum = n) (hnd : Ls.Nodup) (hcard : Ls.length = 2 ^ (n - 1))
    (w : W) (hw : degree w = n) : ∃ i : Fin Ls.length, w = partWord (Ls.get i) := by
  obtain ⟨i, hi⟩ := (enumComp_bijective Ls hpos hsum hnd hcard).2 ((wordEquiv n).symm ⟨w, hw⟩)
  refine ⟨i, ?_⟩
  have h1 : partWord ((wordEquiv n).symm ⟨w, hw⟩).blocks = w :=
    congrArg Subtype.val ((wordEquiv n).apply_symm_apply ⟨w, hw⟩)
  rw [← h1, ← hi]
  rfl

theorem degree_partWord (l : List ℕ) : degree (partWord l) = l.sum := partWord_degree l

/-! ## The ring `ℤ/4`, `q = 2` -/

/-- `ℤ/2` as a `ℤ/4`-algebra. -/
abbrev algZ2 : Algebra (ZMod 4) (ZMod 2) := (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAlgebra
attribute [local instance] algZ2

/-- The element `xc = h₁₂₁ + h₁₃ + h₃₁ + h₄` of `Λ'` over `ℤ/4`. -/
def xc : L (ZMod 4) :=
  hWord (ZMod 4) [1, 2, 1] + hWord (ZMod 4) [1, 3] + hWord (ZMod 4) [3, 1] + hWord (ZMod 4) [4]

theorem xc_eq : xc = hWord (ZMod 4) (comps4 2) + hWord (ZMod 4) (comps4 5) +
    hWord (ZMod 4) (comps4 6) + hWord (ZMod 4) (comps4 7) := rfl

theorem form_xc_comps4 (j : Fin 8) :
    form (2 : ZMod 4) xc (hWord (ZMod 4) (comps4 j)) = 0 := by
  rw [xc_eq]
  simp only [map_add, LinearMap.add_apply, table4]
  fin_cases j <;>
    simp [printed4, qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ] <;> decide

theorem xc_mem_radical : xc ∈ radical (2 : ZMod 4) := by
  intro y
  induction y using basis_induction (ZMod 4) (wordBasis (ZMod 4)) with
  | hz => simp
  | ha y z hy hz => simp only [map_add, hy, hz, add_zero]
  | hb w r =>
    suffices h : form (2 : ZMod 4) xc (wordBasis (ZMod 4) w) = 0 by
      rw [map_smul, h, smul_zero]
    by_cases hw : degree w = 4
    · obtain ⟨i, rfl⟩ := word_mem_list (n := 4) (List.ofFn comps4) (by decide) (by decide)
        (by decide) (by decide) w hw
      rw [partWord_value, List.get_ofFn]
      exact form_xc_comps4 _
    · have hd : ∀ l : List ℕ, l.sum = 4 →
          form (2 : ZMod 4) (hWord (ZMod 4) l) (wordBasis (ZMod 4) w) = 0 := by
        intro l hl
        rw [← partWord_value]
        exact form_degree_ne _ _ _ (by rw [degree_partWord, hl]; exact Ne.symm hw)
      simp only [xc, map_add, LinearMap.add_apply]
      rw [hd _ rfl, hd _ rfl, hd _ rfl, hd _ rfl]
      simp

/-! ## The functional `ψ` -/

/-- `ψ(x)` = the coefficient of `h₁₁` in `x`, reduced modulo `2`. -/
def psi4 : L (ZMod 4) →ₗ[ZMod 4] ZMod 2 :=
  (wordBasis (ZMod 4)).constr (ZMod 4) fun w => if w.toList = [0, 0] then 1 else 0

theorem psi4_apply (x : L (ZMod 4)) :
    psi4 x = ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
      ((wordBasis (ZMod 4)).repr x (partWord [1, 1])) := by
  induction x using basis_induction (ZMod 4) (wordBasis (ZMod 4)) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply]
  | hb w r =>
    simp only [map_smul, psi4, Basis.constr_basis, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    by_cases h : w.toList = [0, 0]
    · have hw : w = partWord [1, 1] := FreeMonoid.toList.injective h
      subst hw; rw [if_pos h]; simp [Algebra.smul_def]; rfl
    · have hw : w ≠ partWord [1, 1] := fun e => h (by rw [e]; rfl)
      rw [if_neg h]; simp [Finsupp.single_apply, hw, Ne.symm hw]

/-- The two compositions of `2`. -/
def comps2L : List (List ℕ) := [[1, 1], [2]]

theorem degreeProj_two (x : L (ZMod 4)) :
    degreeProj (ZMod 4) 2 x =
      (wordBasis (ZMod 4)).repr x (partWord [1, 1]) • hWord (ZMod 4) [1, 1] +
      (wordBasis (ZMod 4)).repr x (partWord [2]) • hWord (ZMod 4) [2] := by
  rw [degreeProj_eq_sum]
  let e := Equiv.ofBijective _ (enumComp_bijective (n := 2) comps2L (by decide) (by decide)
    (by decide) (by decide))
  rw [← e.sum_comp]
  change ∑ i : Fin 2, _ = _
  rw [Fin.sum_univ_two]
  rfl

theorem psi4_radical {x : L (ZMod 4)} (hx : x ∈ radical (2 : ZMod 4)) : psi4 x = 0 := by
  rw [psi4_apply]
  have hp : ∀ l : List ℕ, l.sum = 2 →
      form (2 : ZMod 4) x (hWord (ZMod 4) l) =
        (wordBasis (ZMod 4)).repr x (partWord [1, 1]) * form (2 : ZMod 4) (hWord (ZMod 4) [1, 1]) (hWord (ZMod 4) l) +
        (wordBasis (ZMod 4)).repr x (partWord [2]) *
          form (2 : ZMod 4) (hWord (ZMod 4) [2]) (hWord (ZMod 4) l) := by
    intro l hl
    have h1 : degreeProj (ZMod 4) 2 (hWord (ZMod 4) l) = hWord (ZMod 4) l := by
      rw [← partWord_value, degreeProj_basis, if_pos (by rw [degree_partWord, hl])]
    rw [← h1, ← form_degreeProj, degreeProj_two]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1]
  have e1 := hp [1, 1] rfl
  have e2 := hp [2] rfl
  rw [hx] at e1 e2
  rw [table2_11_11, (form_symm _ _ _).trans (table2_11_2 _), table2_11_2, table2_2_2] at *
  simp only [qnum, Finset.sum_range_succ, Finset.sum_range_zero] at e1
  generalize (wordBasis (ZMod 4)).repr x (partWord [1, 1]) = a at e1 e2 ⊢
  generalize (wordBasis (ZMod 4)).repr x (partWord [2]) = b at e1 e2 ⊢
  revert a b
  decide

/-- `ψ` on `Λ = Λ'/I`. -/
def psi4Bar : Lam (2 : ZMod 4) →ₗ[ZMod 4] ZMod 2 :=
  ((radical (2 : ZMod 4)).restrictScalars (ZMod 4)).liftQ psi4 (fun _ hx => psi4_radical hx)

/-- `ψ ⊗ ψ` on `Λ ⊗ Λ`. -/
def psi4Tensor : Lam (2 : ZMod 4) ⊗[ZMod 4] Lam (2 : ZMod 4) →ₗ[ZMod 4] ZMod 2 :=
  TensorProduct.lift ((LinearMap.mul (ZMod 4) (ZMod 2)).compl₁₂ psi4Bar psi4Bar)

/-- `ψ ⊗ ψ` on `Λ' ⊗ Λ'`. -/
def psi4TensorL : LL (ZMod 4) →ₗ[ZMod 4] ZMod 2 :=
  TensorProduct.lift ((LinearMap.mul (ZMod 4) (ZMod 2)).compl₁₂ psi4 psi4)

theorem psi4Tensor_map (z : LL (ZMod 4)) :
    psi4Tensor (quotientTensorMap (2 : ZMod 4) z) = psi4TensorL z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem psi4_vWord {c : ℕ} (v : Fin c → ℕ) :
    psi4 (vWord (ZMod 4) v) = if (partWord (List.ofFn v)).toList = [0, 0] then 1 else 0 := by
  rw [vWord, ← partWord_value, psi4, Basis.constr_basis]

theorem psi4TensorL_coproduct (l : List ℕ) :
    psi4TensorL (coproduct (2 : ZMod 4) (hWord (ZMod 4) l)) =
      ∑ u : EKPairingMatrices.Splits l.get,
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
            ((2 : ZMod 4) ^ EKPairingMatrices.crossCols (EKPairingMatrices.upper u)
              (EKPairingMatrices.lower u)) *
          ((if (partWord (List.ofFn (EKPairingMatrices.upper u))).toList = [0, 0] then 1 else 0) *
          (if (partWord (List.ofFn (EKPairingMatrices.lower u))).toList = [0, 0] then 1 else 0)) := by
  have hl : hWord (ZMod 4) l = vWord (ZMod 4) l.get := by rw [vWord, List.ofFn_get]
  rw [hl, coproduct_vWord, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [map_smul, psi4TensorL, TensorProduct.lift.tmul]
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', psi4_vWord, Algebra.smul_def]
  rfl

theorem psi4_tensor_coproduct : psi4TensorL (coproduct (2 : ZMod 4) xc) = 1 := by
  simp only [xc, map_add, psi4TensorL_coproduct]
  decide

/-! ## The counterexample -/

/-- EK Proposition 2.3 (coideal part) fails for `k = ℤ/4`, `q = 2`. -/
theorem coideal_counterexample :
    xc ∈ radical (2 : ZMod 4) ∧ coproduct (2 : ZMod 4) xc ∉ coidealSubmodule (2 : ZMod 4) := by
  refine ⟨xc_mem_radical, fun h => ?_⟩
  have h0 := (quotientTensorMap_eq_zero_iff (2 : ZMod 4) _).mpr h
  have h1 := psi4_tensor_coproduct
  rw [← psi4Tensor_map, h0, map_zero] at h1
  exact zero_ne_one h1

/-- EK Corollary 2.4 fails for `k = ℤ/4`, `q = 2`: `Δ` does not descend to `Λ → Λ ⊗ Λ`. -/
theorem no_quotient_coproduct :
    ¬ ∃ D : Lam (2 : ZMod 4) →ₗ[ZMod 4] Lam (2 : ZMod 4) ⊗[ZMod 4] Lam (2 : ZMod 4),
      ∀ x, D (piQ (2 : ZMod 4) x) = quotientTensorMap (2 : ZMod 4) (coproduct (2 : ZMod 4) x) := by
  rintro ⟨D, hD⟩
  have h := hD xc
  rw [(piQ_eq_zero_iff _ _).mpr xc_mem_radical, LinearMap.map_zero] at h
  have h1 := psi4_tensor_coproduct
  rw [← psi4Tensor_map, ← h, map_zero] at h1
  exact zero_ne_one h1

/-- The failure is not visible to the forms: `Δ(xc)` pairs to zero with every pure tensor. -/
theorem counterexample_annihilated (z : LL (ZMod 4)) :
    tensorForm (2 : ZMod 4) (coproduct (2 : ZMod 4) xc) z = 0 :=
  coproduct_radical_annihilates _ xc_mem_radical z

end OddMath.Frontier.EKGeneralQ
