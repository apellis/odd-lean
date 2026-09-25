import OddMath.Frontier.SmallRank
import OddMath.Frontier.ThickDots
import OddMath.Frontier.OnhStructure
import OddMath.Frontier.Categorification
import OddMath.Frontier.ThickBubble

/-!
# Ranks `0` and `1`: the odd nilHecke side

EKL arXiv:1111.1320v1, §3.1 (Props 3.5–3.6), §4.1 ((4.8)–(4.11)), Cor 2.14 and §6 (Morita
structure), for every rank `a ≥ 0`. In ranks `0` and `1` there are no crossings: `D_a = x^δ =
e_a = 1` (the empty reduced word), and `ONH_a = OPol_a = OΛ_a`.

* `polyHom a : OPol_a → ONH_a` (the dots), `proj a = e_a`, `DE a = D_a`, `stairE a = x^δ`.
* Every-rank forms of Prop 3.5 (`prop_3_5_all`), Prop 3.6 (`DE_mul_proj`, `proj_mul_proj`),
  (2.64) in `ONH_a` (`DE_poly_kernel_all`), `D_a g D_a = D_a(g) D_a` (`DE_poly_DE_all`),
  (4.8)–(4.11) (`proj_poly_proj_all`, `proj_poly_proj_eq_all`, `thick_mul_all`).
* `a ≤ 1`: `e_a ONH_a e_a = ONH_a ≅ OΛ_a` (`cornerEquiv_small`), `Mat_{a!}(OΛ_a) ≅ ONH_a`
  (`matrixEquiv_small`, `a! = 1`), `End(ONH_a e_a) ≅ OΛ_a^op` (`endProjectorEquiv_small`), `e_a`
  primitive (`proj_primitive_small`), `ONH_a e_a` indecomposable
  (`leftIdeal_indecomposable_small`), and the centre of `ONH_a` is everything
  (`center_ONH_small`, Prop 2.15).

* Thm 4.15, Thm 4.16 and Prop 4.11 in the ranks left out by the `a + b ≥ 2` statements
  (`thm_4_15_small`, `thm_4_16_small`, `prop_4_11_small`; `|Sq(a)| = |P(a,b)| = 1`,
  `card_Sq_small`, `card_box_small`), the closed form of `χ^a_{(1^r)}` (`chi_col_small`), and
  (6.1), (6.2) as module isomorphisms (`eq_6_1_small`, `eq_6_2_small`).

Vacuous for `a ≤ 1` (no crossing): (3.17)–(3.18), `e_a` independent of the reduced word (the only
word is empty), Lemmas 3.1–3.3, (3.28)–(3.31), (3.40)–(3.44), Prop 3.7, (4.2), Props 4.1–4.2,
(4.13)–(4.16), Lemmas 4.13–4.14, (4.41)–(4.42), (4.46). In §3.3, `D_a = x^δ = e_a = 1` for
`a ≤ 1` (`DE_small`, `stairE_small`, `proj_small`), so (3.50)–(3.53) hold for any ring
(anti-)automorphism `σ`, `ψ`; (3.54) is `LongestDivided.D_staircase`.
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open scoped BigOperators

noncomputable section

/-! ## Dots, `e_a`, `D_a`, `x^δ` -/

/-- The dots `OPol_a → ONH_a`. -/
def polyHom : (a : ℕ) → SkewPolynomial a →+* ONH a
  | 0 => zeroEquiv.toRingHom
  | 1 => RingHom.id _
  | n+2 => OnhPolynomial.polyElem n

/-- `e_a = ∂̄_{w_0}` (EKL §3.1), `e_0 = e_1 = 1`. -/
def proj : (a : ℕ) → ONH a
  | 0 => (1 : ONH 0)
  | 1 => (1 : ONH 1)
  | n+2 => ZeroHecke.projector n

/-- `D_a = ∂_{w_0}` (EKL (3.11)), `D_0 = D_1 = 1`. -/
def DE : (a : ℕ) → ONH a
  | 0 => (1 : ONH 0)
  | 1 => (1 : ONH 1)
  | n+2 => ZeroHecke.DElem n

/-- `x^δ` (EKL (2.40), (3.11)), `= 1` for `a ≤ 1`. -/
def stairE : (a : ℕ) → ONH a
  | 0 => (1 : ONH 0)
  | 1 => (1 : ONH 1)
  | n+2 => ZeroHecke.staircaseElem n

theorem proj_small {a : ℕ} (ha : a ≤ 1) : proj a = 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rfl

theorem DE_small {a : ℕ} (ha : a ≤ 1) : DE a = 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rfl

theorem stairE_small {a : ℕ} (ha : a ≤ 1) : stairE a = 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rfl

theorem choose_three_small {a : ℕ} (ha : a ≤ 1) : a.choose 3 = 0 :=
  Nat.choose_eq_zero_of_lt (by omega)

/-- The dots act by left multiplication, every rank. -/
theorem act_polyHom (a : ℕ) (g f : SkewPolynomial a) : act a (polyHom a g) f = g * f := by
  match a, g, f with
  | 0, g, f =>
    change (g 0) • f = g * f
    conv_rhs => rw [eq_intCast_zero g]
    change _ = ((g 0) • (1 : SkewPolynomial 0)) * f
    rw [smul_mul_assoc, one_mul]
  | 1, g, f => rfl
  | n+2, g, f =>
    rw [act, polyHom, ← RingHom.comp_apply, OnhPolynomial.action_comp_polyElem]
    rfl

/-- `OPol_a ⊂ ONH_a`, every rank. -/
theorem polyHom_injective (a : ℕ) : Function.Injective (polyHom a) := fun g h hgh => by
  have := congrArg (fun x => act a x 1) hgh
  simpa only [act_polyHom, mul_one] using this

/-- `D_a` acts as `∂_{w_0}`, every rank. -/
theorem act_DE (a : ℕ) : act a (DE a) = LongestDivided.D a := by
  match a with
  | 0 => exact LinearMap.ext fun f => by change (1 : ℤ) • f = f; rw [one_smul]
  | 1 => exact LinearMap.ext fun f => one_mul f
  | n+2 => exact ZeroHecke.action_DElem

/-! ## Props 3.5, 3.6; (2.64) and (4.8)–(4.11) in `ONH_a`, every rank -/

/-- **EKL Prop 3.5**, every rank: `e_a = (-1)^{C(a,3)} x^δ D_a`. For `a = n+2` this is
`ZeroHecke.prop_3_5`. -/
theorem prop_3_5_all (a : ℕ) : proj a = (-1 : ℤ)^(a.choose 3) • (stairE a * DE a) := by
  match a with
  | 0 => rw [proj_small (by omega), stairE_small (by omega), DE_small (by omega),
      choose_three_small (by omega), pow_zero, one_smul, mul_one]
  | 1 => rw [proj_small le_rfl, stairE_small le_rfl, DE_small le_rfl,
      choose_three_small le_rfl, pow_zero, one_smul, mul_one]
  | n+2 => exact ZeroHecke.prop_3_5

/-- **EKL Prop 3.6(3)**, every rank: `D_a e_a = D_a`. -/
theorem DE_mul_proj (a : ℕ) : DE a * proj a = DE a := by
  match a with
  | 0 => rw [proj_small (by omega), mul_one]
  | 1 => rw [proj_small le_rfl, mul_one]
  | n+2 => exact ZeroHecke.DElem_mul_projector

/-- **EKL Prop 3.6**, every rank: `e_a² = e_a`. -/
theorem proj_mul_proj (a : ℕ) : proj a * proj a = proj a := by
  match a with
  | 0 => rw [proj_small (by omega), mul_one]
  | 1 => rw [proj_small le_rfl, mul_one]
  | n+2 => exact ZeroHecke.projector_mul_projector

/-- **EKL (2.64)** in `ONH_a`, every rank: `D_a f = f^{w_0} D_a` for `f ∈ OΛ_a`. For `a = n+2`
this is `OnhPolynomial.DElem_poly_kernel`. -/
theorem DE_poly_kernel_all (a : ℕ) (f : SkewPolynomial a) (hf : f ∈ OLam a) :
    DE a * polyHom a f =
      polyHom a (SignedPermutation.skewAction (LongestElementary.longest a) f) * DE a := by
  match a, f, hf with
  | 0, f, _ => simp only [DE_small (by omega : 0 ≤ 1), one_mul, mul_one,
      skewAction_longest_small (by omega : 0 ≤ 1)]
  | 1, f, _ => simp only [DE_small le_rfl, one_mul, mul_one, skewAction_longest_small le_rfl]
  | n+2, f, hf => exact OnhPolynomial.DElem_poly_kernel f hf

/-- EKL §4.1.2: `D_a g D_a = D_a(g) D_a`, every rank (`OnhPolynomial.DElem_poly_DElem`). -/
theorem DE_poly_DE_all (a : ℕ) (g : SkewPolynomial a) :
    DE a * polyHom a g * DE a = polyHom a (LongestDivided.D a g) * DE a := by
  match a, g with
  | 0, g => simp only [DE_small (by omega : 0 ≤ 1), D_small (by omega : 0 ≤ 1), mul_one, one_mul]
  | 1, g => simp only [DE_small le_rfl, D_small le_rfl, mul_one, one_mul]
  | n+2, g => exact OnhPolynomial.DElem_poly_DElem g

/-- **EKL Def 4.3, (4.8)**, every rank: `e_a f e_a = (-1)^{C(a,3)} x^δ f^{w_0} D_a` for
`f ∈ OΛ_a` (`ThickDots.projector_poly_projector`). -/
theorem proj_poly_proj_all (a : ℕ) (f : SkewPolynomial a) (hf : f ∈ OLam a) :
    proj a * polyHom a f * proj a = (-1 : ℤ)^(a.choose 3) •
      (stairE a * polyHom a (SignedPermutation.skewAction (LongestElementary.longest a) f) *
        DE a) := by
  match a, f, hf with
  | 0, f, _ => simp only [proj_small (by omega : 0 ≤ 1), stairE_small (by omega : 0 ≤ 1),
      DE_small (by omega : 0 ≤ 1), skewAction_longest_small (by omega : 0 ≤ 1),
      choose_three_small (by omega : 0 ≤ 1), pow_zero, one_smul, one_mul, mul_one]
  | 1, f, _ => simp only [proj_small le_rfl, stairE_small le_rfl, DE_small le_rfl,
      skewAction_longest_small le_rfl, choose_three_small le_rfl, pow_zero, one_smul, one_mul,
      mul_one]
  | n+2, f, hf => exact ThickDots.projector_poly_projector f hf

/-- **EKL (4.9)–(4.10)**, every rank: `e_a f e_a = e_a f` for `f ∈ OΛ_a`. -/
theorem proj_poly_proj_eq_all (a : ℕ) (f : SkewPolynomial a) (hf : f ∈ OLam a) :
    proj a * polyHom a f * proj a = proj a * polyHom a f := by
  match a, f, hf with
  | 0, f, _ => rw [proj_small (by omega), mul_one]
  | 1, f, _ => rw [proj_small le_rfl, mul_one]
  | n+2, f, hf => exact ThickDots.projector_poly_projector_eq f hf

/-- **EKL (4.11)**, every rank: `(e_a g e_a)(e_a f e_a) = e_a g f e_a` for `g ∈ OΛ_a`. -/
theorem thick_mul_all (a : ℕ) (g f : SkewPolynomial a) (hg : g ∈ OLam a) :
    (proj a * polyHom a g * proj a) * (proj a * polyHom a f * proj a) =
      proj a * polyHom a (g * f) * proj a := by
  match a, g, f, hg with
  | 0, g, f, _ => rw [proj_small (by omega), one_mul, one_mul, one_mul, mul_one, mul_one,
      mul_one, map_mul]
  | 1, g, f, _ => rw [proj_small le_rfl, one_mul, one_mul, one_mul, mul_one, mul_one,
      mul_one, map_mul]
  | n+2, g, f, hg => exact ThickDots.thick_mul g f hg

/-- `|Sq(a)| = a! = 1` for `a ≤ 1` (EKL (4.37)): Thm 4.15 and (6.1) have one summand, `e_a = 1`. -/
theorem card_Sq_small {a : ℕ} (ha : a ≤ 1) : (BoxPartitionCount.Sq a).card = 1 := by
  rw [BoxPartitionCount.card_Sq]
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rfl

/-- `|P(a,b)| = 1` for `a + b ≤ 1` (EKL (2.67)): Thm 4.16 has one summand. -/
theorem card_box_small {a b : ℕ} (hab : a + b ≤ 1) : (BoxPartitionCount.box a b).card = 1 := by
  rw [BoxPartitionCount.card_box]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  all_goals rfl

/-- **EKL Thm 4.15**, `a ≤ 1`: the unique idempotent `e_ℓ = σ_ℓ λ_ℓ = e_a = 1`, `ℓ ∈ Sq(a)`,
decomposes the identity. For `a ≥ 2` see `ThickMatrixUnits.thm_4_15_sum`. -/
theorem thm_4_15_small {a : ℕ} (ha : a ≤ 1) :
    ∑ _ℓ ∈ BoxPartitionCount.Sq a, proj a = 1 := by
  rw [Finset.sum_const, card_Sq_small ha, one_smul, proj_small ha]

/-- **EKL Thm 4.16** (4.56), `a + b ≤ 1`: `e_a ⊗ e_b = 1 = ∑_{α ∈ P(a,b)} e_α` with the unique
`e_α = e_{a+b} = 1`. For `a + b ≥ 2` see `ThickDecomposition.thm_4_16`. -/
theorem thm_4_16_small {a b : ℕ} (hab : a + b ≤ 1) :
    (1 : ONH (a+b)) = ∑ _α ∈ BoxPartitionCount.box a b, proj (a+b) := by
  rw [Finset.sum_const, card_box_small hab, one_smul, proj_small hab]

/-- **EKL Prop 4.11**, `a + b ≤ 1`: every diagram in (4.35) is the identity (`α = 0`, so
`s_α = 1`, and all projectors, splitters and mergers are `1`), and the right side of (4.35) is
`+1`: `β = α̂` and the sign `bubbleSign a b α` is even. For `a + b ≥ 2` see
`ThickBubble.prop_4_11`. -/
theorem prop_4_11_small {a b : ℕ} (hab : a + b ≤ 1) {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hαb : ∀ k, α k ≤ b) (hβa : ∀ j, β j ≤ a) :
    β = BoxComplement.hat b α ∧ Even (ThickBubble.bubbleSign a b α) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  · exact ⟨funext fun j => j.elim0, by simp [ThickBubble.bubbleSign, ThickBubble.blockChi,
      StaircaseEvaluation.omega]⟩
  · have hβ : β = 0 := funext fun j => Nat.le_zero.mp (hβa j)
    subst hβ
    refine ⟨funext fun j => ?_, ?_⟩
    · simp [BoxComplement.hat]
    · simp [ThickBubble.bubbleSign, ThickBubble.blockChi, BoxComplement.hat,
        StaircaseEvaluation.omega, Nat.choose_eq_zero_of_lt]
  · have hα : α = 0 := funext fun k => Nat.le_zero.mp (hαb k)
    subst hα
    refine ⟨funext fun j => j.elim0, ?_⟩
    simp [ThickBubble.bubbleSign, ThickBubble.blockChi, StaircaseEvaluation.omega,
      Nat.choose_eq_zero_of_lt]

/-- The closed form of `χ^a_{(1^r)}` (EKL p. 34, `EKLMisc.chi_col` for `a ≥ 2`) in ranks `a ≤ 1`,
where `χ = 0`. -/
theorem chi_col_small {a r : ℕ} (ha : a ≤ 1) (hr : r ≤ a) :
    6 * (ThickBubble.blockChi a (ThickMatrixUnits.col a r) : ℤ) =
      6 * a.choose 3 + 6 * r * a.choose 2 + r * (3 * (a : ℤ) ^ 2 - 3 * a * r + r ^ 2 - 1) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (a = 0 ∧ r = 0) ∨ (a = 1 ∧ r = 0) ∨ (a = 1 ∧ r = 1) := by omega
  all_goals simp [ThickBubble.blockChi, Nat.choose_eq_zero_of_lt]

/-! ## Ranks `0` and `1`: `ONH_a` is a commutative domain -/

theorem ONH_mul_comm {a : ℕ} (ha : a ≤ 1) (x y : ONH a) : x * y = y * x := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · exact Int.mul_comm (x : ℤ) (y : ℤ)
  · exact rankOne_mul_comm (x : SkewPolynomial 1) (y : SkewPolynomial 1)

theorem ONH_noZeroDivisors {a : ℕ} (ha : a ≤ 1) : NoZeroDivisors (ONH a) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · exact inferInstanceAs (NoZeroDivisors ℤ)
  · exact ⟨fun {f g} h => rankOne_eq_zero_or_eq_zero (f := f) (g := g) h⟩

theorem ONH_nontrivial {a : ℕ} (ha : a ≤ 1) : Nontrivial (ONH a) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · exact inferInstanceAs (Nontrivial ℤ)
  · exact rankOneEquiv.toEquiv.nontrivial

/-- **EKL Prop 2.15** (corrected, `CenterCorrected.center_nilHecke`), `a ≤ 1`: the centre of
`ONH_a` is everything. -/
theorem center_ONH_small {a : ℕ} (ha : a ≤ 1) : Subring.center (ONH a) = ⊤ :=
  eq_top_iff.mpr fun z _ => Subring.mem_center_iff.mpr fun w => ONH_mul_comm ha w z

/-- `ONH_a ≅ OΛ_a` for `a ≤ 1`, through the dots. -/
def polyEquiv {a : ℕ} (ha : a ≤ 1) : SkewPolynomial a ≃+* ONH a :=
  { Equiv.ofBijective (polyHom a) ⟨polyHom_injective a, by
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact zeroEquiv.surjective
      · exact Function.surjective_id⟩ with
    map_mul' := map_mul (polyHom a)
    map_add' := map_add (polyHom a) }

def onhEquivOLam {a : ℕ} (ha : a ≤ 1) : OLam a ≃+* ONH a :=
  (RingEquiv.subringCongr (OLam_small ha)).trans (Subring.topEquiv.trans (polyEquiv ha))

@[simp] theorem onhEquivOLam_apply {a : ℕ} (ha : a ≤ 1) (f : OLam a) :
    onhEquivOLam ha f = polyHom a f := rfl

/-! ## Cor 2.14 and the Morita structure (§6) for `a ≤ 1` -/

/-- `e_a ONH_a e_a ≅ OΛ_a` for `a ≤ 1` (`OnhStructure.cornerEquiv` for `a ≥ 2`): here `e_a = 1`,
and `x ↦ e_a x e_a` is the dot inclusion. -/
theorem cornerEquiv_small {a : ℕ} (ha : a ≤ 1) (f : OLam a) :
    proj a * onhEquivOLam ha f * proj a = polyHom a f := by
  rw [proj_small ha, one_mul, mul_one, onhEquivOLam_apply]

/-- **EKL Cor 2.14**, p. 42, `a ≤ 1`: `Mat_{a!}(OΛ_a) ≅ ONH_a` with `a! = 1`
(`OnhStructure.matrixEquiv` for `a ≥ 2`). -/
def matrixEquiv_small {a : ℕ} (ha : a ≤ 1) : Matrix (Fin 1) (Fin 1) (OLam a) ≃+* ONH a :=
  Matrix.uniqueRingEquiv.trans (onhEquivOLam ha)

/-- `End_{ONH_a}(ONH_a e_a) ≅ OΛ_a^op` for `a ≤ 1` (`OnhStructure.endProjectorEquiv` for
`a ≥ 2`); here `ONH_a e_a = ONH_a`. -/
def endProjectorEquiv_small {a : ℕ} (ha : a ≤ 1) : Module.End (ONH a) (ONH a) ≃+* (OLam a)ᵐᵒᵖ :=
  (RingEquiv.moduleEndSelf (ONH a)).symm.trans (onhEquivOLam ha).symm.op

/-- **EKL §6**: `e_a` is primitive, `a ≤ 1` (`OnhStructure.projector_primitive` for `a ≥ 2`). -/
theorem proj_primitive_small {a : ℕ} (ha : a ≤ 1) (y : ONH a)
    (h : proj a * y * proj a * (proj a * y * proj a) = proj a * y * proj a) :
    proj a * y * proj a = 0 ∨ proj a * y * proj a = proj a := by
  haveI := ONH_noZeroDivisors ha
  rw [proj_small ha] at h ⊢
  set z := 1 * y * 1
  have : z * (z - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- **EKL §6**: `ONH_a e_a = ONH_a` is indecomposable, `a ≤ 1`
(`OnhStructure.leftIdeal_projector_indecomposable` for `a ≥ 2`). -/
theorem leftIdeal_indecomposable_small {a : ℕ} (ha : a ≤ 1) (N₁ N₂ : Submodule (ONH a) (ONH a))
    (hinf : N₁ ⊓ N₂ = ⊥) : N₁ = ⊥ ∨ N₂ = ⊥ := by
  haveI := ONH_noZeroDivisors ha
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne.1
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne.2
  have h1 : y * x ∈ N₁ := N₁.smul_mem y hx
  have h2 : y * x ∈ N₂ := by rw [ONH_mul_comm ha]; exact N₂.smul_mem x hy
  have : y * x ∈ N₁ ⊓ N₂ := ⟨h1, h2⟩
  rw [hinf, Submodule.mem_bot] at this
  exact mul_ne_zero hy0 hx0 this

/-! ## (6.1) and (6.2) as module isomorphisms for small ranks -/

/-- A one-element finset, as a `Unique` type. -/
def uniqueOfCardOne {α : Type*} (s : Finset α) (h : s.card = 1) : Unique s :=
  let x := (Finset.card_eq_one.mp h).choose
  have hx : s = {x} := (Finset.card_eq_one.mp h).choose_spec
  { default := ⟨x, by rw [hx]; exact Finset.mem_singleton_self x⟩
    uniq := fun ⟨z, hz⟩ => Subtype.ext (Finset.mem_singleton.mp (hx ▸ hz)) }

theorem leftIdeal_proj_small {a : ℕ} (ha : a ≤ 1) :
    Categorification.leftIdeal (proj a) = ⊤ := by
  rw [proj_small ha, Categorification.leftIdeal_one]

/-- **EKL (6.1)**, `a ≤ 1`: `ONH_a ≅ ⊕_{ℓ ∈ Sq(a)} ONH_a e_a` (one summand, `e_a = 1`). For
`a ≥ 2` see `Categorification.eq_6_1`; the shift `C(a,2) - 2|ℓ|` is `0`. -/
def eq_6_1_small {a : ℕ} (ha : a ≤ 1) :
    ONH a ≃ₗ[ONH a] (BoxPartitionCount.Sq a → Categorification.leftIdeal (proj a)) :=
  haveI := uniqueOfCardOne _ (card_Sq_small ha)
  (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ (leftIdeal_proj_small ha).symm)).trans
    (LinearEquiv.funUnique (BoxPartitionCount.Sq a) (ONH a) _).symm

/-- **EKL (6.2)**, `a + b ≤ 1`: `ONH_{a+b}(e_a ⊗ e_b) ≅ ⊕_{α ∈ P(a,b)} ONH_{a+b} e_{a+b}` (one
summand; `e_a ⊗ e_b = 1 = e_{a+b}`). For `a + b ≥ 2` see `Categorification.eq_6_2`. -/
def eq_6_2_small {a b : ℕ} (hab : a + b ≤ 1) :
    Categorification.leftIdeal (1 : ONH (a+b)) ≃ₗ[ONH (a+b)]
      (BoxPartitionCount.box a b → Categorification.leftIdeal (proj (a+b))) :=
  haveI := uniqueOfCardOne _ (card_box_small hab)
  (LinearEquiv.ofEq _ _ (by rw [proj_small hab])).trans
    (LinearEquiv.funUnique (BoxPartitionCount.box a b) (ONH (a+b)) _).symm

end

end OddMath.Frontier.SmallRank
