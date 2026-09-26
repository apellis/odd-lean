import OddMath.Frontier.EKFinalNSym

/-!
# EK §2.4: the `q`-bialgebra `QΛ_q` of quantum quasi-symmetric functions

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.4, pp. 21–22, at arbitrary `q` in an arbitrary
commutative ring `k`.

`QΛ_q = QSym k` is the free `k`-module on compositions with the quantum quasi-shuffle product
`qMul` (`EKFinalNSym`).  Here it receives its coproduct `qCoprod` (deconcatenation,
`M_w ↦ Σ_{w = w₁w₂} M_{w₁} ⊗ M_{w₂}`) and counit `qCounit` (`M_w ↦ δ_{w∅}`), and the axioms
of a `q`-bialgebra are proved:

* `qMul_assoc`, `qMul_one_left`, `qMul_one_right`: associativity and unit;
* `qCoprod_coassoc`, `qCounit_left`, `qCounit_right`: coassociativity and counit;
* `qCoprod_mul`: `Δ(FG) = Δ(F) ⋆ Δ(G)` for the twisted product `⋆` on `QΛ_q ⊗ QΛ_q`,
  `(M_a ⊗ M_b) ⋆ (M_c ⊗ M_d) = q^{|b||c|} (M_a M_c) ⊗ (M_b M_d)` (`qTensorMul`), the same
  twisting rule as for `Λ′ ⊗ Λ′` (EK p. 5);
* `qCoprod_one`, `qCounit_mul`, `qCounit_one`.

Associativity and the compatibility are obtained by transposition through the perfect pairing
`⟨h_α, M_β⟩ = δ_{αβ}` from coassociativity of `Λ′` and from `Δ(xy) = Δ(x)Δ(y)` in `Λ′`
(`EKFinalNSym.pair_coproduct`, `EKGeneralQ.coassociativity`, `EKGeneralQ.coproduct_mul`).
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.EKFinal
open EKGeneralQ
open EKFreeCoproduct (W degree)

variable {k : Type*} [CommRing k] (q : k)

/-! ## Perfectness of the pairing -/

theorem M_eq_basis (v : W) : M k v = (Finsupp.basisSingleOne : Basis W k (QSym k)) v := by
  simp [M]

theorem qsym_ext {F G : QSym k} (h : ∀ x : L k, pair k x F = pair k x G) : F = G := by
  ext v
  have := h (wordBasis k v)
  rwa [pair_wordBasis, pair_wordBasis] at this

theorem qsym_linear_ext {N : Type*} [AddCommGroup N] [Module k N] {f g : QSym k →ₗ[k] N}
    (h : ∀ v : W, f (M k v) = g (M k v)) : f = g :=
  Finsupp.basisSingleOne.ext fun v => by rw [← M_eq_basis]; exact h v

/-! ## Multilinear pairings with tensors of `Λ′` -/

variable (k) in
/-- `⟨a ⊗ b, (F, G)⟩ = ⟨a, F⟩⟨b, G⟩`. -/
def pair2 : LL k →ₗ[k] QSym k →ₗ[k] QSym k →ₗ[k] k :=
  TensorProduct.lift (LinearMap.mk₂ k (fun a b => (pair k a).smulRight (pair k b))
    (fun a a' b => by ext F G; simp [add_mul])
    (fun c a b => by ext F G; simp [mul_assoc])
    (fun a b b' => by ext F G; simp [mul_add])
    (fun c a b => by ext F G; simp; ring))

@[simp] theorem pair2_tmul (a b : L k) (F G : QSym k) :
    pair2 k (a ⊗ₜ b) F G = pair k a F * pair k b G := by
  simp [pair2]

variable (k) in
/-- `⟨a ⊗ z, (F, G, H)⟩ = ⟨a, F⟩⟨z, (G, H)⟩`. -/
def pair3 : L k ⊗[k] LL k →ₗ[k] QSym k →ₗ[k] QSym k →ₗ[k] QSym k →ₗ[k] k :=
  TensorProduct.lift (LinearMap.mk₂ k (fun a z => (pair k a).smulRight (pair2 k z))
    (fun a a' z => by ext F G H; simp [add_mul])
    (fun c a z => by ext F G H; simp [mul_assoc])
    (fun a z z' => by ext F G H; simp [mul_add])
    (fun c a z => by ext F G H; simp; ring))

@[simp] theorem pair3_tmul (a : L k) (z : LL k) (F G H : QSym k) :
    pair3 k (a ⊗ₜ z) F G H = pair k a F * pair2 k z G H := by
  simp [pair3]

theorem pair2_basis (z : LL k) (v₁ v₂ : W) :
    pair2 k z (M k v₁) (M k v₂) = (tensorBasis k).repr z (v₁, v₂) := by
  induction z using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add,
      Finsupp.add_apply]
  | hb p r =>
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_smul,
      Finsupp.smul_apply, smul_eq_mul, Basis.repr_self, tensorBasis, Basis.tensorProduct_apply,
      pair2_tmul, pair_wordBasis_M, pair_wordBasis_M, Finsupp.single_apply]
    congr 1
    rcases p with ⟨a, b⟩
    by_cases h1 : v₁ = a <;> by_cases h2 : v₂ = b <;> simp [h1, h2, eq_comm]

/-- Transposition of the product: `⟨x, FG⟩ = ⟨Δx, (F, G)⟩`. -/
theorem pair_qMul (x : L k) (F G : QSym k) :
    pair k x (qMul q F G) = pair2 k (coproduct q x) F G := by
  have h : (qMul q).compr₂ (pair k x) = pair2 k (coproduct q x) := by
    apply qsym_linear_ext; intro v₁
    apply qsym_linear_ext; intro v₂
    rw [LinearMap.compr₂_apply, pair2_basis, pair_coproduct]
  exact LinearMap.congr_fun (LinearMap.congr_fun h F) G

theorem pair3_assoc_tmul (y : LL k) (b : L k) (F G H : QSym k) :
    pair3 k (TensorProduct.assoc k (L k) (L k) (L k) (y ⊗ₜ b)) F G H =
      pair2 k y F G * pair k b H := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [mul_assoc]
  | add y y' hy hy' =>
    rw [TensorProduct.add_tmul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.add_apply, hy, hy', map_add, LinearMap.add_apply, LinearMap.add_apply, add_mul]

theorem pair2_qMul_left (z : LL k) (F G H : QSym k) :
    pair2 k z (qMul q F G) H =
      pair3 k (TensorProduct.assoc k (L k) (L k) (L k)
        (TensorProduct.map (coproduct q) LinearMap.id z)) F G H := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [pair2_tmul, TensorProduct.map_tmul, LinearMap.id_apply, pair3_assoc_tmul, pair_qMul]
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem pair2_qMul_right (z : LL k) (F G H : QSym k) :
    pair2 k z F (qMul q G H) =
      pair3 k (TensorProduct.map LinearMap.id (coproduct q) z) F G H := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [pair2_tmul, TensorProduct.map_tmul, LinearMap.id_apply, pair3_tmul, pair_qMul]
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

/-! ## Associativity and unit -/

/-- **Associativity of the quantum quasi-shuffle** (transpose of coassociativity of `Λ′`). -/
theorem qMul_assoc (F G H : QSym k) :
    qMul q (qMul q F G) H = qMul q F (qMul q G H) := by
  apply qsym_ext
  intro x
  rw [pair_qMul, pair2_qMul_left, coassociativity, ← pair2_qMul_right, ← pair_qMul]

theorem qsh_nil_right (I : List ℕ) : qsh I [] = [(I, 0)] := by
  cases I <;> simp [qsh]

theorem wl_one : wl (1 : W) = [] := rfl

/-- The unit `M_∅`. -/
theorem qMul_one_left (F : QSym k) : qMul q (M k 1) F = F := by
  have h : qMul q (M k 1) = LinearMap.id := by
    apply qsym_linear_ext; intro v
    rw [qMul_M, qMulB, wl_one, qsh]
    simp [partWord_wl]
  rw [h, LinearMap.id_apply]

theorem qMul_one_right (F : QSym k) : qMul q F (M k 1) = F := by
  have h : (qMul q).flip (M k 1) = LinearMap.id := by
    apply qsym_linear_ext; intro v
    rw [LinearMap.flip_apply, qMul_M, qMulB, wl_one, qsh_nil_right]
    simp [partWord_wl]
  exact LinearMap.congr_fun h F

/-! ## Coproduct and counit: deconcatenation -/

variable (k) in
/-- `QΛ_q ⊗ QΛ_q`. -/
abbrev QQ := QSym k ⊗[k] QSym k

variable (k) in
/-- The basis `M_a ⊗ M_b` of `QΛ_q ⊗ QΛ_q`. -/
def B2 : Basis (W × W) k (QQ k) :=
  (Finsupp.basisSingleOne : Basis W k (QSym k)).tensorProduct Finsupp.basisSingleOne

variable (k) in
/-- The basis `M_a ⊗ (M_b ⊗ M_c)` of `QΛ_q ⊗ (QΛ_q ⊗ QΛ_q)`. -/
def B3 : Basis (W × (W × W)) k (QSym k ⊗[k] QQ k) :=
  (Finsupp.basisSingleOne : Basis W k (QSym k)).tensorProduct (B2 k)

theorem B2_apply (a b : W) : B2 k (a, b) = M k a ⊗ₜ M k b := by
  simp [B2, M_eq_basis]

theorem B2_repr_tmul (F G : QSym k) (a b : W) : (B2 k).repr (F ⊗ₜ G) (a, b) = F a * G b := by
  rw [B2, Basis.tensorProduct_repr_tmul_apply]
  simp [mul_comm]

theorem B3_repr_tmul (F : QSym k) (Y : QQ k) (a : W) (bc : W × W) :
    (B3 k).repr (F ⊗ₜ Y) (a, bc) = F a * (B2 k).repr Y bc := by
  rw [B3, Basis.tensorProduct_repr_tmul_apply]
  simp [mul_comm]

variable (k) in
/-- The coproduct of `QΛ_q`: deconcatenation `M_w ↦ Σ_{w = w₁w₂} M_{w₁} ⊗ M_{w₂}`. -/
def qCoprod : QSym k →ₗ[k] QQ k :=
  (Finsupp.basisSingleOne : Basis W k (QSym k)).constr k fun w =>
    ((splitsW w).map fun p => M k p.1 ⊗ₜ M k p.2).sum

variable (k) in
/-- The counit of `QΛ_q`: the coefficient of `M_∅`. -/
def qCounit : QSym k →ₗ[k] k := Finsupp.lapply 1

theorem qCoprod_M (w : W) :
    qCoprod k (M k w) = ((splitsW w).map fun p => M k p.1 ⊗ₜ M k p.2).sum := by
  rw [qCoprod, M_eq_basis, Basis.constr_basis]

theorem M_apply (v w : W) : M k v w = if v = w then 1 else 0 := by
  rw [M, Finsupp.single_apply]

/-- Coordinates of the coproduct: `Δ(F) = Σ_{a,b} F(ab) M_a ⊗ M_b`. -/
theorem repr_qCoprod (F : QSym k) (a b : W) : (B2 k).repr (qCoprod k F) (a, b) = F (a * b) := by
  have h : (Finsupp.lapply (a, b)).comp ((B2 k).repr.toLinearMap.comp (qCoprod k)) =
      Finsupp.lapply (a * b) := by
    apply qsym_linear_ext; intro w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      qCoprod_M, map_list_sum, List.map_map]
    rw [M_apply, show (if w = a * b then (1 : k) else 0) = if a * b = w then 1 else 0 by
      simp only [eq_comm], ← sum_splitsW (k := k) a b w]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Finsupp.lapply_apply, B2_repr_tmul, M_apply]
    by_cases h1 : a = p.1 <;> by_cases h2 : b = p.2 <;> simp [h1, h2, eq_comm]
  exact LinearMap.congr_fun h F

theorem B3_assoc (Y : QQ k) (H : QSym k) (a b c : W) :
    (B3 k).repr (TensorProduct.assoc k (QSym k) (QSym k) (QSym k) (Y ⊗ₜ H)) (a, (b, c)) =
      (B2 k).repr Y (a, b) * H c := by
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | tmul F G => rw [TensorProduct.assoc_tmul, B3_repr_tmul, B2_repr_tmul, B2_repr_tmul, mul_assoc]
  | add Y Y' h h' =>
    rw [TensorProduct.add_tmul, map_add, map_add, Finsupp.add_apply, h, h', map_add,
      Finsupp.add_apply, add_mul]

/-- **Coassociativity of deconcatenation.** -/
theorem qCoprod_coassoc (F : QSym k) :
    TensorProduct.assoc k (QSym k) (QSym k) (QSym k)
        (TensorProduct.map (qCoprod k) LinearMap.id (qCoprod k F)) =
      TensorProduct.map LinearMap.id (qCoprod k) (qCoprod k F) := by
  apply (B3 k).repr.injective
  ext ⟨a, b, c⟩
  have hl : ∀ Z : QQ k, (B3 k).repr (TensorProduct.assoc k (QSym k) (QSym k) (QSym k)
      (TensorProduct.map (qCoprod k) LinearMap.id Z)) (a, (b, c)) = (B2 k).repr Z (a * b, c) := by
    intro Z
    induction Z using TensorProduct.induction_on with
    | zero => simp
    | tmul G H => rw [TensorProduct.map_tmul, LinearMap.id_apply, B3_assoc, repr_qCoprod,
        B2_repr_tmul]
    | add Z Z' h h' => simp only [map_add, Finsupp.add_apply, h, h']
  have hr : ∀ Z : QQ k, (B3 k).repr (TensorProduct.map LinearMap.id (qCoprod k) Z) (a, (b, c)) =
      (B2 k).repr Z (a, b * c) := by
    intro Z
    induction Z using TensorProduct.induction_on with
    | zero => simp
    | tmul G H => rw [TensorProduct.map_tmul, LinearMap.id_apply, B3_repr_tmul, repr_qCoprod,
        B2_repr_tmul]
    | add Z Z' h h' => simp only [map_add, Finsupp.add_apply, h, h']
  rw [hl, hr, repr_qCoprod, repr_qCoprod, mul_assoc]

/-- **Counit laws.** -/
theorem qCounit_left (F : QSym k) :
    TensorProduct.lid k (QSym k) (TensorProduct.map (qCounit k) LinearMap.id (qCoprod k F)) = F := by
  ext v
  have h : ∀ Z : QQ k, (TensorProduct.lid k (QSym k)
      (TensorProduct.map (qCounit k) LinearMap.id Z)) v = (B2 k).repr Z (1, v) := by
    intro Z
    induction Z using TensorProduct.induction_on with
    | zero => simp
    | tmul G H => simp [B2_repr_tmul, qCounit]
    | add Z Z' h h' => simp only [map_add, Finsupp.add_apply, h, h']
  rw [h, repr_qCoprod, one_mul]

theorem qCounit_right (F : QSym k) :
    TensorProduct.rid k (QSym k) (TensorProduct.map LinearMap.id (qCounit k) (qCoprod k F)) = F := by
  ext v
  have h : ∀ Z : QQ k, (TensorProduct.rid k (QSym k)
      (TensorProduct.map LinearMap.id (qCounit k) Z)) v = (B2 k).repr Z (v, 1) := by
    intro Z
    induction Z using TensorProduct.induction_on with
    | zero => simp
    | tmul G H => simp [B2_repr_tmul, qCounit, mul_comm]
    | add Z Z' h h' => simp only [map_add, Finsupp.add_apply, h, h']
  rw [h, repr_qCoprod, mul_one]

theorem qCoprod_one : qCoprod k (M k 1) = M k 1 ⊗ₜ M k 1 := by
  rw [qCoprod_M]
  simp [splitsW]

theorem qCounit_M (w : W) : qCounit k (M k w) = if w = 1 then 1 else 0 := by
  simp [qCounit, M_apply]

theorem qCounit_mul (F G : QSym k) : qCounit k (qMul q F G) = qCounit k F * qCounit k G := by
  have h := pair_qMul q (1 : L k) F G
  rw [coproduct_one, tensorOne, pair2_tmul, ← wordBasis_one, pair_wordBasis, pair_wordBasis,
    pair_wordBasis] at h
  simpa [qCounit] using h

/-! ## The twisted compatibility -/

/-- `Σ_{s ∈ splits u} Σ_{t ∈ splits v} f s t`. -/
def dsum {M' : Type*} [AddCommMonoid M'] (u v : W) (f : W × W → W × W → M') : M' :=
  ((splitsW u).map fun s => ((splitsW v).map fun t => f s t).sum).sum

theorem dsum_add (u v : W) (f g : W × W → W × W → k) :
    dsum u v (fun s t => f s t + g s t) = dsum u v f + dsum u v g := by
  simp only [dsum, List.sum_map_add]

theorem dsum_mul (u v : W) (c : k) (f : W × W → W × W → k) :
    dsum u v (fun s t => c * f s t) = c * dsum u v f := by
  simp only [dsum, List.sum_map_mul_left]

/-- Coordinates of the twisted product of `Λ′ ⊗ Λ′`:
`[h_u ⊗ h_v](X ⋆ Y) = Σ_{u = s₁s₂, v = t₁t₂} q^{|s₂||t₁|} [h_{s₁} ⊗ h_{t₁}]X · [h_{s₂} ⊗ h_{t₂}]Y`. -/
theorem repr_tensorMul (X Y : LL k) (u v : W) :
    (tensorBasis k).repr (tensorMul q X Y) (u, v) = dsum u v fun s t =>
      q ^ (degree s.2 * degree t.1) * ((tensorBasis k).repr X (s.1, t.1) *
        (tensorBasis k).repr Y (s.2, t.2)) := by
  induction X using basis_induction k (tensorBasis k) with
  | hz => simp [dsum]
  | ha X X' hX hX' =>
    rw [tensorMul_add_left, map_add, Finsupp.add_apply, hX, hX', ← dsum_add]
    congr 1; funext s t; simp only [map_add, Finsupp.add_apply]; ring
  | hb p r =>
    induction Y using basis_induction k (tensorBasis k) with
    | hz => simp [dsum]
    | ha Y Y' hY hY' =>
      rw [tensorMul_add_right, map_add, Finsupp.add_apply, hY, hY', ← dsum_add]
      congr 1; funext s t; simp only [map_add, Finsupp.add_apply]; ring
    | hb p' r' =>
      rw [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply]
      have key : ∀ s t : W × W,
          q ^ (degree s.2 * degree t.1) * (r * (if p = (s.1, t.1) then 1 else 0) *
            (r' * if p' = (s.2, t.2) then 1 else 0)) =
          (r * r' * q ^ (degree p.2 * degree p'.1)) *
            (((if p.1 = s.1 then (1 : k) else 0) * if p'.1 = s.2 then 1 else 0) *
              ((if p.2 = t.1 then (1 : k) else 0) * if p'.2 = t.2 then 1 else 0)) := by
        intro s t
        rcases p with ⟨p1, p2⟩; rcases p' with ⟨p1', p2'⟩
        by_cases h1 : p1 = s.1 <;> by_cases h2 : p2 = t.1 <;> by_cases h3 : p1' = s.2 <;>
          by_cases h4 : p2' = t.2 <;> simp [h1, h2, h3, h4]
        ring
      rw [show (dsum u v fun s t => q ^ (degree s.2 * degree t.1) *
          (r * (if p = (s.1, t.1) then 1 else 0) * (r' * if p' = (s.2, t.2) then 1 else 0))) =
          dsum u v fun s t => (r * r' * q ^ (degree p.2 * degree p'.1)) *
            (((if p.1 = s.1 then (1 : k) else 0) * if p'.1 = s.2 then 1 else 0) *
              ((if p.2 = t.1 then (1 : k) else 0) * if p'.2 = t.2 then 1 else 0)) by
        simp only [dsum, key]]
      rw [dsum_mul, dsum]
      simp only [List.sum_map_mul_left, List.sum_map_mul_right, sum_splitsW]
      by_cases hu : p.1 * p'.1 = u <;> by_cases hv : p.2 * p'.2 = v
      · subst hu; subst hv; simp; ring
      · have : ¬ (p.1 * p'.1, p.2 * p'.2) = (u, v) := fun h => hv (Prod.ext_iff.mp h).2
        rw [if_neg this, if_neg hv]; ring
      · have : ¬ (p.1 * p'.1, p.2 * p'.2) = (u, v) := fun h => hu (Prod.ext_iff.mp h).1
        rw [if_neg this, if_neg hu]; ring
      · have : ¬ (p.1 * p'.1, p.2 * p'.2) = (u, v) := fun h => hu (Prod.ext_iff.mp h).1
        rw [if_neg this, if_neg hu]; ring

variable (k) in
/-- The twisted product on `QΛ_q ⊗ QΛ_q`:
`(M_a ⊗ M_b) ⋆ (M_c ⊗ M_d) = q^{|b||c|} (M_a M_c) ⊗ (M_b M_d)`. -/
def qTensorMul : QQ k →ₗ[k] QQ k →ₗ[k] QQ k :=
  (B2 k).constr k fun p => (B2 k).constr k fun r =>
    q ^ (degree p.2 * degree r.1) • (qMul q (M k p.1) (M k r.1) ⊗ₜ qMul q (M k p.2) (M k r.2))

theorem qTensorMul_B2 (p r : W × W) : qTensorMul k q (B2 k p) (B2 k r) =
    q ^ (degree p.2 * degree r.1) • (qMul q (M k p.1) (M k r.1) ⊗ₜ qMul q (M k p.2) (M k r.2)) := by
  rw [qTensorMul, Basis.constr_basis, Basis.constr_basis]

theorem qTensorMul_tmul (a b c d : W) : qTensorMul k q (M k a ⊗ₜ M k b) (M k c ⊗ₜ M k d) =
    q ^ (degree b * degree c) • (qMul q (M k a) (M k c) ⊗ₜ qMul q (M k b) (M k d)) := by
  rw [← B2_apply, ← B2_apply, qTensorMul_B2]

theorem qMul_coord (u v x : W) :
    qMul q (M k u) (M k v) x = (tensorBasis k).repr (coproduct q (wordBasis k x)) (u, v) := by
  rw [pair_coproduct, pair_wordBasis]

theorem qCoprod_M' (u : W) : qCoprod k (M k u) = ((splitsW u).map (B2 k)).sum := by
  rw [qCoprod_M]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [B2_apply]

theorem list_sum_apply₂ {α : Type*} (l : List α) (g : α → QQ k) (f : QQ k →ₗ[k] QQ k →ₗ[k] QQ k)
    (Z : QQ k) : f (l.map g).sum Z = (l.map fun a => f (g a) Z).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **The twisted compatibility of `QΛ_q`:** `Δ(FG) = Δ(F) ⋆ Δ(G)` (transpose of
`Δ(xy) = Δ(x)Δ(y)` in `Λ′`). -/
theorem qCoprod_mul (F G : QSym k) :
    qCoprod k (qMul q F G) = qTensorMul k q (qCoprod k F) (qCoprod k G) := by
  have h : (qMul q).compr₂ (qCoprod k) = (qTensorMul k q).compl₁₂ (qCoprod k) (qCoprod k) := by
    refine qsym_linear_ext (N := QSym k →ₗ[k] QQ k) (fun u => ?_)
    refine qsym_linear_ext (N := QQ k) (fun v => ?_)
    rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    apply (B2 k).repr.injective
    ext ⟨x, y⟩
    rw [repr_qCoprod, qMul_coord, wordBasis_mul, coproduct_mul, tensorMul, ← tensorMul,
      repr_tensorMul, qCoprod_M', qCoprod_M', list_sum_apply₂, dsum]
    simp only [map_list_sum, List.map_map]
    rw [← Finsupp.applyAddHom_apply, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply, Finsupp.applyAddHom_apply]
    rw [map_list_sum, List.map_map, ← Finsupp.applyAddHom_apply, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, Finsupp.applyAddHom_apply, qTensorMul_B2, map_smul,
      Finsupp.smul_apply, B2_repr_tmul, qMul_coord, smul_eq_mul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h F) G

/-! ## Summary -/

/-- **EK §2.4: `QΛ_q` is a `q`-bialgebra** (any commutative ring `k`, any `q`): the quantum
quasi-shuffle is associative and unital, deconcatenation is coassociative and counital, and
`Δ(FG) = Δ(F) ⋆ Δ(G)` for the `q`-twisted product on `QΛ_q ⊗ QΛ_q`; the counit is
multiplicative and `Δ(1) = 1 ⊗ 1`. -/
theorem qsym_bialgebra :
    (∀ F G H : QSym k, qMul q (qMul q F G) H = qMul q F (qMul q G H)) ∧
    (∀ F : QSym k, qMul q (M k 1) F = F ∧ qMul q F (M k 1) = F) ∧
    (∀ F : QSym k, TensorProduct.assoc k (QSym k) (QSym k) (QSym k)
        (TensorProduct.map (qCoprod k) LinearMap.id (qCoprod k F)) =
      TensorProduct.map LinearMap.id (qCoprod k) (qCoprod k F)) ∧
    (∀ F : QSym k,
      TensorProduct.lid k (QSym k) (TensorProduct.map (qCounit k) LinearMap.id (qCoprod k F)) = F ∧
      TensorProduct.rid k (QSym k) (TensorProduct.map LinearMap.id (qCounit k) (qCoprod k F)) = F) ∧
    (∀ F G : QSym k, qCoprod k (qMul q F G) = qTensorMul k q (qCoprod k F) (qCoprod k G)) ∧
    qCoprod k (M k 1) = M k 1 ⊗ₜ M k 1 ∧
    (∀ F G : QSym k, qCounit k (qMul q F G) = qCounit k F * qCounit k G) ∧
    qCounit k (M k 1) = 1 :=
  ⟨qMul_assoc q, fun F => ⟨qMul_one_left q F, qMul_one_right q F⟩, qCoprod_coassoc,
    fun F => ⟨qCounit_left F, qCounit_right F⟩, qCoprod_mul q, qCoprod_one, qCounit_mul q,
    by rw [qCounit_M, if_pos rfl]⟩

end OddMath.Frontier.EKFinal
