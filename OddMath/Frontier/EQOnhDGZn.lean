import OddMath.Frontier.EQOnhDGCompare
import OddMath.Frontier.EQOnhDGPoly
import OddMath.Frontier.EQZnAction

/-!
# `Z_n` as a dg `(ONH_n, OΛ_n)`-bimodule (Corollary 3.9, dg form)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.2, Proposition 3.7, Definition 3.8 and Corollary 3.9.

Rank `N = n + 2`. `Z_N = OPol_N(0,1,0,1,…)` (`EQSkewDifferential.Zn N`, a dg
`(OPol_N, OΛ_N)`-bimodule) carries the action of `ONH_N` by dots (left multiplication) and odd
divided differences (`NilHeckeAction.action`). Corollary 3.9 says that this action identifies
`(ONH_N, d)` with the endomorphism dg algebra of `Z_N` over `OΛ_N`: the differential of `ONH_N`
is the super commutator with the differential of `Z_N` (`EQZn.action_dONH_of_mem_parity`), and
the action commutes with the right action of `OΛ_N`. In the language of the `DG` library this is
the statement that the action makes `Z_N` a dg `(ONH_N, OΛ_N)`-bimodule:

* `divided_mem_grading`: `∂_i` lowers the degree by one;
* `action_mem_grading`: an element of `ONH_N` of degree `i` maps `OPol_N` of degree `j` to
  degree `i + j`;
* `ONH.instModuleZn`, `ONH.instDGModuleZn`: `Z_N` is a left dg `ONH_N`-module (the Leibniz rule
  `d(p z) = d(p) z + (-1)^{|p|} p d(z)` is Corollary 3.9);
* `ONH.polyHom_smul`: its restriction along the dots `OPol_N → ONH_N` is the `OPol_N`-module
  structure of `Z_N`;
* `ONH.instDGBimoduleZn`: `Z_N` is a dg `(ONH_N, OΛ_N)`-bimodule, the actions commuting since
  `ONH_N` acts by right `OΛ_N`-linear operators (`EQZn.onhEndEquiv`).
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential (OPol OPolAlpha Zn osymDG twistRev)
open NilHeckeAction NilHeckeGrading
open AllRankDivided (divided s)

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) onhZnNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) onhZnNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-! ## Degrees of the operators -/

/-- `s_i` preserves the grading. -/
theorem s_mem_grading (i : Fin (n + 1)) {k : ℤ} {f : SkewPolynomial (n + 2)}
    (hf : f ∈ EQSkewDifferential.grading (n + 2) k) :
    s i f ∈ EQSkewDifferential.grading (n + 2) k :=
  EQSkewDifferential.ringHom_mem_grading (s i).toRingHom
    (fun j => by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AllRankDivided.s_generator]
      exact neg_mem (EQSkewDifferential.generator_mem_grading _))
    hf

/-- Homogeneity of `∂_i`, for a homogeneous element. -/
def DivHom (i : Fin (n + 1)) (f : SkewPolynomial (n + 2)) (k : ℤ) : Prop :=
  f ∈ EQSkewDifferential.grading (n + 2) k ∧ divided i f ∈ EQSkewDifferential.grading (n + 2) (k - 1)

theorem divHom_mul (i : Fin (n + 1)) {f g : SkewPolynomial (n + 2)} {a b : ℤ}
    (hf : DivHom i f a) (hg : DivHom i g b) : DivHom i (f * g) (a + b) := by
  refine ⟨EQSkewDifferential.mul_mem_grading' hf.1 hg.1, ?_⟩
  rw [AllRankDivided.divided_mul]
  refine add_mem ?_ ?_
  · have := EQSkewDifferential.mul_mem_grading' hf.2 hg.1
    rwa [show a - 1 + b = a + b - 1 by ring] at this
  · have := EQSkewDifferential.mul_mem_grading' (s_mem_grading i hf.1) hg.2
    rwa [show a + (b - 1) = a + b - 1 by ring] at this

theorem divHom_one (i : Fin (n + 1)) : DivHom i 1 0 :=
  ⟨EQSkewDifferential.one_mem_grading', by rw [AllRankDivided.divided_one]; exact zero_mem _⟩

theorem divHom_generator (i : Fin (n + 1)) (j : Fin (n + 2)) : DivHom i (generator j) 1 := by
  refine ⟨EQSkewDifferential.generator_mem_grading j, ?_⟩
  rw [AllRankDivided.divided_generator, sub_self]
  split_ifs
  · exact EQSkewDifferential.one_mem_grading'
  · exact zero_mem _

theorem divHom_pow (i : Fin (n + 1)) (j : Fin (n + 2)) :
    ∀ e : ℕ, DivHom i (generator j ^ e) (e : ℤ)
  | 0 => by simpa using divHom_one i
  | e + 1 => by
    rw [pow_succ]
    simpa using divHom_mul i (divHom_pow i j e) (divHom_generator i j)

theorem divHom_ofFn_prod (i : Fin (n + 1)) :
    ∀ {l : ℕ} (v : Fin l → SkewPolynomial (n + 2)) (e : Fin l → ℤ),
      (∀ t, DivHom i (v t) (e t)) → DivHom i (List.ofFn v).prod (∑ t, e t)
  | 0, v, e, _ => by simpa using divHom_one i
  | l + 1, v, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact divHom_mul i (h 0) (divHom_ofFn_prod i (fun t => v t.succ) (fun t => e t.succ)
      fun t => h _)

/-- **`∂_i` lowers the degree by one** (the `q`-degree by two). -/
theorem divided_mem_grading (i : Fin (n + 1)) {k : ℤ} {f : SkewPolynomial (n + 2)}
    (hf : f ∈ EQSkewDifferential.grading (n + 2) k) :
    divided i f ∈ EQSkewDifferential.grading (n + 2) (k - 1) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine AddSubgroup.sum_mem _ fun a ha => ?_
  have h := OddMath.Frontier.MonomialReversal.monomial_eq_smul_prod a (f a)
  change Finsupp.single a (f a) = _ at h
  rw [h, map_zsmul, ← hf a ha]
  exact AddSubgroup.zsmul_mem _
    (divHom_ofFn_prod i _ (fun j => (a j : ℤ)) fun j => divHom_pow i j (a j)).2 _

theorem action_wordValue_mem_grading (w : List (Letter n)) {j : ℤ} {f : SkewPolynomial (n + 2)}
    (hf : f ∈ EQSkewDifferential.grading (n + 2) j) :
    action n (wordValue w) f ∈ EQSkewDifferential.grading (n + 2) (halfWordDegree w + j) := by
  induction w with
  | nil =>
    simpa [wordValue, halfWordDegree] using hf
  | cons g w ih =>
    simp only [wordValue, halfWordDegree, List.map_cons, List.prod_cons] at ih ⊢
    rw [action_mul_apply]
    cases g with
    | inl t =>
      rw [List.sum_cons, add_assoc, letterValue, Sum.elim_inl, action_dot_apply,
        show halfLetterDegree (Sum.inl t : Letter n) = 1 from rfl]
      exact EQSkewDifferential.mul_mem_grading' (EQSkewDifferential.generator_mem_grading t) ih
    | inr t =>
      rw [List.sum_cons, add_assoc]
      have := divided_mem_grading t ih
      rw [letterValue, Sum.elim_inr, action_crossing_apply]
      rwa [show halfLetterDegree (Sum.inr t : Letter n) +
          ((w.map halfLetterDegree).sum + j) = (w.map halfLetterDegree).sum + j - 1 by
        simp only [halfLetterDegree, Sum.elim_inr]; ring]

/-- An element of `ONH_{n+2}` of degree `i` maps `OPol_{n+2}` of degree `j` to degree `i + j`. -/
theorem action_mem_grading {i j : ℤ} {p : Presented n} (hp : p ∈ grading n i)
    {f : SkewPolynomial (n + 2)} (hf : f ∈ EQSkewDifferential.grading (n + 2) j) :
    action n p f ∈ EQSkewDifferential.grading (n + 2) (i + j) := by
  rw [grading_eq_degreePiece] at hp
  change p ∈ degreePiece n (2 * i) at hp
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hw : wordDegree w = 2 * i := hw
    rw [wordDegree_eq_two_mul] at hw
    have : halfWordDegree w = i := by omega
    exact this ▸ action_wordValue_mem_grading w hf
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply]; exact add_mem hy hz
  | smul r y _ hy => rw [map_zsmul, LinearMap.smul_apply]; exact AddSubgroup.zsmul_mem _ hy r

/-! ## `Z_{n+2}` as a dg `ONH_{n+2}`-module -/

namespace ONH

/-- The operator of `p ∈ ONH_{n+2}` on `Z_{n+2}`. -/
def actionFun (p : ONH n) : Zn (n + 2) →+ Zn (n + 2) where
  toFun z := OPolAlpha.equiv _ _ (action n ((equiv n).symm p) ((OPolAlpha.equiv _ _).symm z))
  map_zero' := by rw [map_zero, map_zero, map_zero]
  map_add' z z' := by rw [map_add, map_add, map_add]

theorem actionFun_apply (p : ONH n) (z : Zn (n + 2)) :
    actionFun p z = OPolAlpha.equiv _ _ (action n ((equiv n).symm p) ((OPolAlpha.equiv _ _).symm z)) :=
  rfl

/-- The action of `ONH_{n+2}` on `Z_{n+2}` by dots and odd divided differences. -/
def actionZn (n : ℕ) : ONH n →+* AddMonoid.End (Zn (n + 2)) where
  toFun := actionFun
  map_one' := by
    ext z
    rw [actionFun_apply, map_one, map_one, Module.End.one_apply, AddEquiv.apply_symm_apply]
    rfl
  map_mul' p q := by
    ext z
    show actionFun (p * q) z = actionFun p (actionFun q z)
    rw [actionFun_apply, actionFun_apply, actionFun_apply,
      AddEquiv.symm_apply_apply, map_mul, map_mul, Module.End.mul_apply]
  map_zero' := by
    ext z
    rw [actionFun_apply, map_zero, map_zero, LinearMap.zero_apply, map_zero]
    rfl
  map_add' p q := by
    ext z
    show actionFun (p + q) z = actionFun p z + actionFun q z
    rw [actionFun_apply, actionFun_apply, actionFun_apply, map_add,
      map_add, LinearMap.add_apply, map_add]

instance instModuleZn : Module (ONH n) (Zn (n + 2)) := Module.compHom _ (actionZn n)

theorem symm_smul (p : ONH n) (z : Zn (n + 2)) :
    (OPolAlpha.equiv _ _).symm (p • z) = action n ((equiv n).symm p) ((OPolAlpha.equiv _ _).symm z) :=
  rfl

/-- **Ellis–Qi, Corollary 3.9** (dg form): `Z_{n+2}` is a left dg module over `(ONH_{n+2}, d)`;
the Leibniz rule `d(p z) = d(p) z + (-1)^{|p|} p d(z)` is the statement that the differential of
`ONH_{n+2}` is the super commutator with the differential of `Z_{n+2}`. -/
instance instDGModuleZn : DG.DGModule (ONH n) (Zn (n + 2)) where
  smul_mem _ _ _ _ hp hz := action_mem_grading hp hz
  d_smul' {k p} hp z := by
    apply (OPolAlpha.equiv _ _).symm.injective
    simp only [map_add, Units.smul_def, map_zsmul, symm_smul, OPolAlpha.symm_d, symm_d]
    rw [EQSkewDifferential.indicator_oddStrands,
      EQZn.action_dONH_of_mem_parity
        (grading_le_parity n k (show (equiv n).symm p ∈ grading n k from hp)), negOnePow_val_cast]
    abel

/-- Restricted along the dots `OPol_{n+2} → ONH_{n+2}`, the action of `ONH_{n+2}` on `Z_{n+2}` is
its `OPol_{n+2}`-module structure. -/
theorem polyHom_smul (f : OPol (n + 2)) (z : Zn (n + 2)) : polyHom n f • z = f • z := by
  apply (OPolAlpha.equiv _ _).symm.injective
  rw [symm_smul, OPolAlpha.symm_smul]
  exact OnhPolynomial.action_polyElem _ _

/-- The action of `ONH_{n+2}` on `Z_{n+2}` is faithful. -/
theorem eq_zero_of_forall_smul_eq_zero {p : ONH n} (h : ∀ z : Zn (n + 2), p • z = 0) : p = 0 := by
  have hact : action n ((equiv n).symm p) = 0 := by
    refine LinearMap.ext fun f => ?_
    have h1 := congrArg (OPolAlpha.equiv (n + 2) (EQSkewDifferential.oddStrands (n + 2))).symm
      (h (OPolAlpha.equiv _ _ f))
    rw [symm_smul, AddEquiv.symm_apply_apply, map_zero] at h1
    exact h1
  have h0 : (equiv n).symm p = 0 :=
    NilHeckeBasis.action_injective n (hact.trans (map_zero _).symm)
  exact (equiv n).symm.injective (h0.trans (map_zero _).symm)

instance instSMulCommClassZn : SMulCommClass (ONH n) (osymDG (n + 2))ᵐᵒᵖ (Zn (n + 2)) where
  smul_comm p c z := by
    apply (OPolAlpha.equiv _ _).symm.injective
    rw [← MulOpposite.op_unop c, symm_smul, EQSkewDifferential.Zn.op_smul_osym, EQSkewDifferential.Zn.symm_op_smul,
      EQSkewDifferential.Zn.op_smul_osym, EQSkewDifferential.Zn.symm_op_smul, symm_smul]
    have hc : (OPol.equiv (n + 2)).symm ((MulOpposite.unop c : osymDG (n + 2)) : OPol (n + 2)) ∈
        EQSkewDifferential.osym (n + 2) :=
      EQSkewDifferential.mem_osymDG.mp (MulOpposite.unop c).2
    exact (EQZn.onhEndEquiv n ((equiv n).symm p)).2 _ _ hc

/-- **Ellis–Qi, Corollary 3.9 / Definition 3.8** (dg form): `Z_{n+2}` is a dg
`(ONH_{n+2}, OΛ_{n+2})`-bimodule. -/
instance instDGBimoduleZn : DG.DGBimodule (ONH n) (osymDG (n + 2)) (Zn (n + 2)) :=
  DG.DGBimodule.mk'

end ONH

end OddMath.Frontier.EQOnhDG

end
