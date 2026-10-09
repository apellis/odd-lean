import OddMath.Frontier.EQFunctorRingTensor
import OddMath.Frontier.EQSchurDifferential

/-!
# Block twists of `OPol_{a+b}`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3 (Definition 4.6) and §4.4 (Corollary 4.21). Auxiliary ring endomorphisms of
`OPol_{a+b} = OPol_a ⊠ OPol_b` (variables `x_1, …, x_a`, `y_1, …, y_b`) used to compare
`(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z_{a,b}` with `Z_{a+b}`:

* `blockRev a b`: the plain permutation `w₀ × w₀ ∈ S_a × S_b` (reversal inside each block), with
  `blockRev (f(x) g(y)) = (w₀ f)(x) (w₀ g)(y)`;
* the twisted Leibniz rule for `θ_a ⊗ θ_b` (`EQZab.tauAB`):
  `d(θ_{ab} f) = θ_{ab}(d f) + s_β θ_{ab}(f) - ι(θ_{ab} f) s_β` with `β = (0,1,0,1,…) ⊔ (0,1,0,1,…)`
  (`d_tauAB`);
* `sAlpha_zAlpha_eq`: `s_{(0,1,0,…)}` in `a + b` variables is `s_β + {a} θ_b(e_1)(y)`.
-/

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY diagHom diagHom_generator inclX_generator inclY_generator
  par tauAB tauCoeff parityInv_tauAB)

noncomputable section

variable (a b : ℕ)

/-! ## The block reversal `w₀ × w₀` -/

/-- The permutation of `Fin (a + b)` reversing each of the blocks `[0, a)` and `[a, a + b)`. -/
def blockRevPerm : Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr Fin.revPerm Fin.revPerm).trans finSumFinEquiv)

theorem blockRevPerm_castAdd (i : Fin a) :
    blockRevPerm a b (Fin.castAdd b i) = Fin.castAdd b i.rev := by
  simp [blockRevPerm]

theorem blockRevPerm_natAdd (j : Fin b) :
    blockRevPerm a b (Fin.natAdd a j) = Fin.natAdd a j.rev := by
  simp [blockRevPerm]

/-- `w₀ × w₀`, the plain permutation reversing the variables `x` and the variables `y`. -/
def blockRev : SkewPolynomial (a + b) →+* SkewPolynomial (a + b) :=
  skewLift (fun j => (1 : ℤ) • generator (blockRevPerm a b j))
    (fun i j h => smul_generator_anticomm (fun _ => 1) (blockRevPerm a b) i j h)

variable {a b}

theorem blockRev_generator (j : Fin (a + b)) :
    blockRev a b (generator j) = generator (blockRevPerm a b j) := by
  simp [blockRev]

theorem blockRev_inclX (f : SkewPolynomial a) :
    blockRev a b (inclX a b f) = inclX a b (longestPerm a f) := by
  have h : (blockRev a b).comp (inclX a b) = (inclX a b).comp (longestPerm a) :=
    ringHom_ext fun i => by
      simp [blockRev_generator, blockRevPerm_castAdd]
  exact RingHom.congr_fun h f

theorem blockRev_inclY (f : SkewPolynomial b) :
    blockRev a b (inclY a b f) = inclY a b (longestPerm b f) := by
  have h : (blockRev a b).comp (inclY a b) = (inclY a b).comp (longestPerm b) :=
    ringHom_ext fun j => by
      simp [blockRev_generator, blockRevPerm_natAdd]
  exact RingHom.congr_fun h f

/-! ## The twisted Leibniz rule for `θ_a ⊗ θ_b` -/

theorem tauAB_generator (i : Fin (a + b)) : tauAB a b (generator i) = tauCoeff a b i • generator i := by
  simp [tauAB]

variable (a b) in
/-- `β = (0,1,0,1,…) ⊔ (0,1,0,1,…)`: the pattern `zAlpha` on each block. -/
def zAB (i : Fin (a + b)) : ℤ := if i.val < a then ((i.val % 2 : ℕ) : ℤ) else (((i.val - a) % 2 : ℕ) : ℤ)

theorem tauCoeff_identity (i : Fin (a + b)) :
    tauCoeff a b i = tauCoeff a b i * tauCoeff a b i + tauCoeff a b i * (2 * zAB a b i) := by
  unfold tauCoeff zAB
  split_ifs with h1 h2 h2
  · omega
  · rcases Nat.even_or_odd (i.val - a) with he | ho
    · rw [Nat.even_iff.mp he, he.neg_one_pow]; norm_num
    · rw [Nat.odd_iff.mp ho, ho.neg_one_pow]; norm_num
  · rcases Nat.even_or_odd i.val with he | ho
    · rw [Nat.even_iff.mp he, he.neg_one_pow]; norm_num
    · rw [Nat.odd_iff.mp ho, ho.neg_one_pow]; norm_num
  · omega

/-- `d(θ_{ab} f) = θ_{ab}(d f) + s_β θ_{ab}(f) - ι(θ_{ab} f) s_β` for `θ_{ab} = θ_a ⊗ θ_b`. -/
theorem d_tauAB (f : SkewPolynomial (a + b)) :
    d (a + b) (tauAB a b f) = tauAB a b (d (a + b) f) + sAlpha (zAB a b) * tauAB a b f -
      parityInv (a + b) (tauAB a b f) * sAlpha (zAB a b) := by
  induction f using induction_generator with
  | hgen j =>
    have hs := eq_sub_of_add_eq (sAlpha_mul_generator_add (zAB a b) j)
    have hc := tauCoeff_identity (a := a) (b := b) j
    rw [tauAB_generator, map_zsmul, d_generator, map_mul, tauAB_generator,
      map_zsmul, parityInv_generator, smul_mul_smul_comm, mul_smul_comm, hs, smul_neg, neg_mul,
      smul_mul_assoc]
    set Y := generator j * generator j
    set Z := generator j * sAlpha (zAB a b)
    rw [smul_sub, smul_smul]
    conv_lhs => rw [hc]
    rw [add_smul]
    abel
  | h0 => rw [map_zero, map_zero, map_zero, map_zero, EQBorel.sp_mul_zero, EQBorel.sp_zero_mul,
      sub_zero, add_zero]
  | h1 => simp
  | hadd f g hf hg =>
    rw [map_add, map_add, hf, hg, map_add, map_add, map_add]
    simp only [mul_add, add_mul]
    abel
  | hneg f hf =>
    rw [map_neg, map_neg, hf, map_neg, map_neg, map_neg]
    simp only [mul_neg, neg_mul]
    abel
  | hmul f g hf hg =>
    rw [map_mul, d_mul, d_mul, map_add, map_mul, map_mul, ← parityInv_tauAB, map_mul]
    exact twisted_leibniz_aux _ _ _ _ _ _ _ _ _ hf hg

/-- `s_{(0,1,0,…)} = s_β + {a} θ_b(e_1)(y)` in `a + b` variables. -/
theorem sAlpha_zAlpha_eq :
    sAlpha (zAlpha (a + b)) = sAlpha (zAB a b) + par a • inclY a b (theta b (elementary b 1)) := by
  rw [show theta b (elementary b 1) = ∑ j : Fin b, (-1 : ℤ) ^ j.val • generator j by
    rw [elementary, EQZab.strictSum_one, map_sum]
    simp]
  rw [map_sum, Finset.smul_sum, sAlpha, sAlpha, Fin.sum_univ_add, Fin.sum_univ_add, add_assoc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [zAlpha, zAB, i.isLt]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zAlpha, zAB, Fin.val_natAdd, map_zsmul, inclY_generator, smul_smul, ← add_smul]
    simp only [show ¬(a + j.val < a) by omega, ↓reduceIte, show a + j.val - a = j.val by omega]
    congr 1
    unfold par
    rcases Nat.even_or_odd j.val with hj | hj
    · have hj' := Nat.even_iff.mp hj
      rw [hj.neg_one_pow, hj']
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · rw [ha, show (a + j.val) % 2 = 0 by omega]; norm_num
      · rw [ha, show (a + j.val) % 2 = 1 by omega]; norm_num
    · have hj' := Nat.odd_iff.mp hj
      rw [hj.neg_one_pow, hj']
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · rw [ha, show (a + j.val) % 2 = 1 by omega]; norm_num
      · rw [ha, show (a + j.val) % 2 = 0 by omega]; norm_num


section BlockRevRing

open DG
open OddMath.Frontier.EQZab (osymAB)

variable {a b : ℕ}

/-! ### The block reversal on `OΛ_a ⊗ OΛ_b` -/

variable (a b) in
theorem parityInv_blockRev (f : SkewPolynomial (a + b)) :
    parityInv (a + b) (blockRev a b f) = blockRev a b (parityInv (a + b) f) := by
  have h : (parityInv (a + b)).comp (blockRev a b) = (blockRev a b).comp (parityInv (a + b)) :=
    ringHom_ext fun j => by simp [blockRev_generator]
  exact RingHom.congr_fun h f

variable (a b) in
theorem d_blockRev (f : SkewPolynomial (a + b)) :
    d (a + b) (blockRev a b f) = blockRev a b (d (a + b) f) := by
  let D : SkewPolynomial (a + b) →+ SkewPolynomial (a + b) :=
    (d (a + b)).comp (blockRev a b).toAddMonoidHom
  let E : SkewPolynomial (a + b) →+ SkewPolynomial (a + b) :=
    (blockRev a b).toAddMonoidHom.comp (d (a + b))
  exact EQZab.deriv_ext (D := D) (E := E) ((parityInv (a + b)).comp (blockRev a b)) (blockRev a b)
    (fun f g => by simp [D, EQSkewDifferential.d_mul])
    (fun f g => by simp [E, EQSkewDifferential.d_mul, parityInv_blockRev])
    (fun j => by simp [D, E, blockRev_generator]) f

variable (a b) in
theorem blockRev_blockRev (f : SkewPolynomial (a + b)) : blockRev a b (blockRev a b f) = f := by
  have h : (blockRev a b).comp (blockRev a b) = RingHom.id _ :=
    ringHom_ext fun j => by
      rw [RingHom.comp_apply, blockRev_generator, blockRev_generator, RingHom.id_apply]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [blockRevPerm_castAdd, blockRevPerm_castAdd, Fin.rev_rev]
      · rw [blockRevPerm_natAdd, blockRevPerm_natAdd, Fin.rev_rev]
  exact RingHom.congr_fun h f

variable (a b) in
theorem blockRev_mem {f : SkewPolynomial (a + b)} (hf : f ∈ osymAB a b) : blockRev a b f ∈ osymAB a b := by
  refine EQZab.osymAB_induction (P := fun f => blockRev a b f ∈ osymAB a b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf
  · intro k
    rw [blockRev_inclX]
    exact EQZab.inclX_mem (EQZab.longestPerm_mem_osym (EQZab.elementary_mem a k))
  · intro k
    rw [blockRev_inclY]
    exact EQZab.inclY_mem (EQZab.longestPerm_mem_osym (EQZab.elementary_mem b k))
  · rw [map_zero]; exact zero_mem _
  · rw [map_one]; exact one_mem _
  · intro f g hf hg; rw [map_add]; exact add_mem hf hg
  · intro f hf; rw [map_neg]; exact neg_mem hf
  · intro f g hf hg; rw [map_mul]; exact mul_mem hf hg

variable (a b) in
theorem blockRev_mem_grading {k : ℤ} {f : SkewPolynomial (a + b)} (hf : f ∈ grading (a + b) k) :
    blockRev a b f ∈ grading (a + b) k :=
  ringHom_mem_grading _ (fun j => by rw [blockRev_generator]; exact generator_mem_grading _) hf

variable (a b) in
/-- `w₀ × w₀` as a ring endomorphism of `OΛ_{a,b}`. -/
def blockRevRing : osymABDG a b →+* osymABDG a b where
  toFun g := ⟨OPol.equiv _ (blockRev a b ((OPol.equiv _).symm g)), mem_osymABDG.mpr (by
    rw [RingEquiv.symm_apply_apply]; exact blockRev_mem a b (mem_osymABDG.mp g.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' g g' := Subtype.ext (by simp)

variable (a b) in
/-- **`w₀ × w₀ : OΛ_{a,b} → OΛ_{a,b}`** as a morphism of dg rings (the plain permutation reversing
each block of variables). -/
def blockRevDG : osymABDG a b →ᵈᵍ+* osymABDG a b where
  __ := blockRevRing a b
  map_mem' {k g} hg := (DGSubring.mem_grading_iff _).mpr (OPol.equiv_mem_grading_iff.mpr
    (blockRev_mem_grading a b (OPol.equiv_mem_grading_iff.mp ((DGSubring.mem_grading_iff _).mp hg))))
  map_d' g := Subtype.ext (by
    change OPol.equiv _ (blockRev a b ((OPol.equiv _).symm (DG.d (g : OPol (a + b))))) =
      DG.d (OPol.equiv _ (blockRev a b ((OPol.equiv _).symm (g : OPol (a + b)))))
    rw [OPol.symm_d, ← d_blockRev]
    rfl)

theorem blockRevDG_val (g : osymABDG a b) :
    (OPol.equiv _).symm ((blockRevDG a b g : osymABDG a b) : OPol (a + b)) =
      blockRev a b ((OPol.equiv _).symm (g : OPol (a + b))) := rfl


end BlockRevRing

/-! ### The block swap `OPol_{A+B} → OPol_{A+B}` -/

section Swap

open DG
open OddMath.Frontier.EQZab (osymAB)

variable (A B : ℕ)

/-- `j ↦ a + j` for `j < b`, `j ↦ j - b` otherwise: the variables `x_1, …, x_{a+b}` sent to
`y_1, …, y_b, x_1, …, x_a`. -/
def swapFin (j : Fin (A + B)) : Fin (A + B) :=
  if h : j.val < B then ⟨A + j.val, by omega⟩ else ⟨j.val - B, by omega⟩

theorem swapFin_injective : Function.Injective (swapFin A B) := by
  intro i j h
  unfold swapFin at h
  split_ifs at h <;> simp [Fin.ext_iff] at h <;> exact Fin.ext (by omega)

theorem swapFin_append (j : Fin (B + A)) :
    generator (swapFin A B (Fin.cast (Nat.add_comm B A) j)) =
      Fin.append (fun j : Fin B => generator (Fin.natAdd A j))
        (fun i : Fin A => generator (Fin.castAdd B i)) j := by
  refine Fin.addCases (fun j => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    congr 1
    simp [swapFin, Fin.ext_iff, j.isLt]
  · rw [Fin.append_right]
    congr 1
    simp [swapFin, Fin.ext_iff]

/-- The block swap `f(x) ↦ f(y, x)`. -/
def swapPoly : SkewPolynomial (A + B) →+* SkewPolynomial (A + B) :=
  skewLift (fun j => generator (swapFin A B j))
    (EQZab.generator_anticomm_of_injective _ (swapFin_injective A B))

variable {A B}

theorem swapPoly_generator (j : Fin (A + B)) : swapPoly A B (generator j) = generator (swapFin A B j) := by
  simp [swapPoly]

theorem swapPoly_elementary (k : ℕ) :
    swapPoly A B (elementary (A + B) k) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        inclY A B (elementary B p.1) * inclX A B (elementary A p.2) := by
  rw [elementary, EQZab.ringHom_strictSum]
  simp only [swapPoly_generator]
  have h : (fun j : Fin (A + B) => generator (swapFin A B j)) =
      fun j => (Fin.append (fun j : Fin B => inclY A B (generator j))
        (fun i : Fin A => inclX A B (generator i))) (Fin.cast (Nat.add_comm A B) j) := by
    funext j
    rw [show j = Fin.cast (Nat.add_comm B A) (Fin.cast (Nat.add_comm A B) j) from Fin.ext rfl,
      swapFin_append]
    simp only [EQZab.inclY_generator, EQZab.inclX_generator]
    rfl
  rw [h, EQZab.strictSum_cast, EQZab.strictSum_append]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [elementary, elementary, EQZab.ringHom_strictSum, EQZab.ringHom_strictSum]

theorem swapPoly_mem {f : SkewPolynomial (A + B)} (hf : f ∈ osym (A + B)) : swapPoly A B f ∈ osymAB A B := by
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [swapPoly_elementary]
    exact Subring.sum_mem _ fun p _ =>
      mul_mem (EQZab.inclY_mem (EQZab.elementary_mem B p.1)) (EQZab.inclX_mem (EQZab.elementary_mem A p.2))
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem parityInv_swapPoly (f : SkewPolynomial (A + B)) :
    parityInv (A + B) (swapPoly A B f) = swapPoly A B (parityInv (A + B) f) := by
  have h : (parityInv (A + B)).comp (swapPoly A B) = (swapPoly A B).comp (parityInv (A + B)) :=
    ringHom_ext fun j => by simp [swapPoly_generator]
  exact RingHom.congr_fun h f

theorem d_swapPoly (f : SkewPolynomial (A + B)) :
    d (A + B) (swapPoly A B f) = swapPoly A B (d (A + B) f) := by
  let D : SkewPolynomial (A + B) →+ SkewPolynomial (A + B) := (d (A + B)).comp (swapPoly A B).toAddMonoidHom
  let E : SkewPolynomial (A + B) →+ SkewPolynomial (A + B) := (swapPoly A B).toAddMonoidHom.comp (d (A + B))
  exact EQZab.deriv_ext (D := D) (E := E) ((parityInv (A + B)).comp (swapPoly A B)) (swapPoly A B)
    (fun f g => by simp [D, EQSkewDifferential.d_mul])
    (fun f g => by simp [E, EQSkewDifferential.d_mul, parityInv_swapPoly])
    (fun j => by simp [D, E, swapPoly_generator]) f

theorem swapPoly_mem_grading {k : ℤ} {f : SkewPolynomial (A + B)} (hf : f ∈ grading (A + B) k) :
    swapPoly A B f ∈ grading (A + B) k :=
  ringHom_mem_grading _ (fun j => by rw [swapPoly_generator]; exact generator_mem_grading _) hf

variable (A B) in
/-- The block swap `OΛ_{A+B} → OΛ_{A,B}` as a morphism of dg rings. -/
def swapOsym : osymDG (A + B) →ᵈᵍ+* osymABDG A B where
  toFun h := ⟨OPol.equiv _ (swapPoly A B ((OPol.equiv _).symm h)), mem_osymABDG.mpr (by
    rw [RingEquiv.symm_apply_apply]; exact swapPoly_mem (mem_osymDG.mp h.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' g g' := Subtype.ext (by simp)
  map_mem' {k g} hg := (DGSubring.mem_grading_iff _).mpr (OPol.equiv_mem_grading_iff.mpr
    (swapPoly_mem_grading (OPol.equiv_mem_grading_iff.mp ((DGSubring.mem_grading_iff _).mp hg))))
  map_d' g := Subtype.ext (by
    change OPol.equiv _ (swapPoly A B ((OPol.equiv _).symm (DG.d (g : OPol (A + B))))) =
      DG.d (OPol.equiv _ (swapPoly A B ((OPol.equiv _).symm (g : OPol (A + B)))))
    rw [OPol.symm_d, ← d_swapPoly]
    rfl)

end Swap

end

end OddMath.Frontier.EQFunctor
