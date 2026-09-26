import OddMath.Frontier.OddBialgebraWindow

/-!
# The product of `K₀(ONH)` is induced by induction

EKL arXiv:1111.1320v1, §6, pp. 46–47: "the inclusions `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` give rise to
induction and restriction functors that equip `K₀(ONH)` with the structure of a
`q`-bialgebra". Here the induction half, on all graded projectives.

* For every `a, b` the block embeddings `ONH_a → ONH_{a+b} ← ONH_b` (strands `[0, a)` and
  `[a, a+b)`; `ONH_0 = ℤ`, `ONH_1 = OPol_1`) form a `SuperPair`, so graded idempotents induce:
  `Ind(n, s, e)(m, t, f) = (nm, s + t, e ⊠ f)` with the Koszul sign (`OddBialgebraKron`),
  compatible with Murray–von Neumann equivalence, `⊕` and shifts, and
  `indK0 a b : K₀(ONH_a) →ₗ K₀(ONH_b) →ₗ K₀(ONH_{a+b})` is `ℤ[q,q⁻¹]`-bilinear.
* `indK0_Eclass`: `Ind([E^{(a)}], [E^{(b)}]) = [E^{(a)}E^{(b)}]` (`indClass`, the class of
  `ONH_{a+b}(e_a ⊗ e_b){C(a,2)+C(b,2)}`), since `ι_L(e_a) ι_R(e_b) = e_a ⊗ e_b` and the Koszul
  sign of a `1 × 1` product is trivial.
* `single_mul_single_ind`, `mulK0_eq_indProd`: the product of `K₀(ONH)` (defined in
  `OddCategorification` on the basis `[E^{(a)}]` only) is the map induced by induction on
  arbitrary classes: `[P] · [Q] = [Ind(P ⊠ Q)]` for all graded projectives `P`, `Q`.
-/

noncomputable section
open Matrix LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open GradedK0 NilHeckeAction OnhWindow OddCategorification QuantumSl2Plus
open OddMath.SkewPolynomial (SkewPolynomial)

local notation "L" => LaurentPolynomial ℤ

/-! ### `1 × 1` idempotents -/

section Gelem

variable {R₁ R₂ S : Type*} [Ring R₁] [Ring R₂] [Ring S] {A₁ : ℤ → AddSubgroup R₁}
  {A₂ : ℤ → AddSubgroup R₂} {B : ℤ → AddSubgroup S} [SetLike.GradedMonoid A₁]
  [SetLike.GradedMonoid A₂] [SetLike.GradedMonoid B]

omit [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] in
/-- `Ind(R₁e{k} ⊠ R₂f{k'}) = S ι₁(e) ι₂(f) {k + k'}`. -/
theorem SuperPair.ind_gelem (P : SuperPair A₁ A₂ B) {e : R₁} {f : R₂} {g : S} (he : e ∈ A₁ 0)
    (hee : e * e = e) (hf : f ∈ A₂ 0) (hff : f * f = f) (hg : g ∈ B 0) (hgg : g * g = g)
    (hefg : P.ι₁ e * P.ι₂ f = g) {k k' m : ℤ} (hm : k + k' = m) :
    P.ind (gelem he hee k) (gelem hf hff k') ≈ gelem hg hgg m := by
  refine MvN.of_equiv (finCongr (Nat.one_mul 1)) (P.ind _ _).hom (P.ind _ _).idem
    (fun _ => hm.symm) (fun i j => ?_)
  show diagonal (fun _ => g) _ _ = P.kron _ _ _ _ _ (finProdFinEquiv.symm i)
    (finProdFinEquiv.symm j)
  generalize finProdFinEquiv.symm i = x
  generalize finProdFinEquiv.symm j = y
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  rw [diagonal_apply, if_pos (Subsingleton.elim (α := Fin 1) _ _), SuperPair.kron_apply]
  simp only [gelem, gdiag]
  rw [diagonal_apply, if_pos (Subsingleton.elim (α := Fin 1) _ _), diagonal_apply,
    if_pos (Subsingleton.elim (α := Fin 1) _ _), Int.negOnePow_even _ (Even.mul_right ⟨_, rfl⟩ _),
    one_smul, hefg]

end Gelem

theorem single_eq_gelem {R : Type*} [Ring R] {A : ℤ → AddSubgroup R} [SetLike.GradedMonoid A] :
    (GIdem.single 0 : GIdem A) = gelem SetLike.GradedOne.one_mem (one_mul 1) 0 := rfl

/-! ### The block embeddings `ONH_a → ONH_{a+b} ← ONH_b` -/

/-- `ℤ ⊗ ℤ → ℤ`. -/
def pairZZ : SuperPair intGrading intGrading intGrading :=
  SuperPair.intLeft (RingHom.id ℤ) id int_even

/-- `ℤ ⊗ OPol_1 → OPol_1`. -/
def pairZO : SuperPair intGrading opolGrading opolGrading :=
  SuperPair.intLeft (RingHom.id _) id opol_even

/-- `OPol_1 ⊗ ℤ → OPol_1`. -/
def pairOZ : SuperPair opolGrading intGrading opolGrading :=
  SuperPair.intRight (RingHom.id _) id opol_even

/-- `ℤ ⊗ ONH_{b+2} → ONH_{n+2}`, strands `[0, b+2)`. -/
def pairZW (b n : ℕ) (h : 0 + (b+2) ≤ n+2) : SuperPair intGrading (onhGrading b) (onhGrading n) :=
  SuperPair.intLeft (windowHom b n 0 h) (fun hy => winPiece_le _ _ _ (windowHom_mem h hy))
    onh_even

/-- `ONH_{a+2} ⊗ ℤ → ONH_{n+2}`, strands `[0, a+2)`. -/
def pairWZ (a n : ℕ) (h : 0 + (a+2) ≤ n+2) : SuperPair (onhGrading a) intGrading (onhGrading n) :=
  SuperPair.intRight (windowHom a n 0 h) (fun hx => winPiece_le _ _ _ (windowHom_mem h hx))
    onh_even

/-- `OPol_1 ⊗ OPol_1 → ONH_2`, `x ↦ x_0`, `y ↦ x_1`. -/
def pairOO : SuperPair opolGrading opolGrading (onhGrading 0) :=
  SuperPair.ofWin (dotHom 0 0) (dotHom 0 1) (dotHom_mem 0) (dotHom_mem 1) (by decide) opol_even
    opol_even

/-- `OPol_1 ⊗ ONH_{b+2} → ONH_{n+2}`, strands `{0}` and `[1, b+3)`. -/
def pairOW (b n : ℕ) (h : 1 + (b+2) ≤ n+2) : SuperPair opolGrading (onhGrading b) (onhGrading n) :=
  SuperPair.ofWin (dotHom n 0) (windowHom b n 1 h) (dotHom_mem 0) (windowHom_mem h) (by simp)
    opol_even onh_even

/-- `ONH_{a+2} ⊗ OPol_1 → ONH_{n+2}`, strands `[0, a+2)` and `{a+2}`. -/
def pairWO (a n : ℕ) (h : 0 + (a+2) ≤ n+2) (j : Fin (n+2)) (hj : j.val = a+2) :
    SuperPair (onhGrading a) opolGrading (onhGrading n) :=
  SuperPair.ofWin (windowHom a n 0 h) (dotHom n j) (windowHom_mem h) (dotHom_mem j) (by omega)
    onh_even opol_even

/-- `ONH_{a+2} ⊗ ONH_{b+2} → ONH_{n+2}`, strands `[0, a+2)` and `[a+2, a+b+4)`
(`OnhStructure.tensorMap`). -/
def pairWW (a b n : ℕ) (h : 0 + (a+2) ≤ n+2) (h' : (a+2) + (b+2) ≤ n+2) :
    SuperPair (onhGrading a) (onhGrading b) (onhGrading n) :=
  SuperPair.ofWin (windowHom a n 0 h) (windowHom b n (a+2) h') (windowHom_mem h)
    (windowHom_mem h') (by omega) onh_even onh_even

/-! ### Induction on `K₀(ONH)` -/

/-- Induction `K₀(ONH_a) ⊗ K₀(ONH_b) → K₀(ONH_{a+b})`, `[P] ⊗ [Q] ↦ [ONH_{a+b} ⊗ (P ⊠ Q)]`. -/
def indK0 : (a b : ℕ) → KONH a →ₗ[L] KONH b →ₗ[L] KONH (a + b)
  | 0, 0 => pairZZ.indK0
  | 0, 1 => pairZO.indK0
  | 0, b+2 => (pairZW b (0 + b) (by omega)).indK0
  | 1, 0 => pairOZ.indK0
  | 1, 1 => pairOO.indK0
  | 1, b+2 => (pairOW b (1 + b) (by omega)).indK0
  | a+2, 0 => (pairWZ a a (by omega)).indK0
  | a+2, 1 => (pairWO a (a+1) (by omega) ⟨a+2, by omega⟩ rfl).indK0
  | a+2, b+2 => (pairWW a b (a+2+b) (by omega) (by omega)).indK0

section Eclass
open SetLike.GradedOne (one_mem)
open ThickBubble (blockE_eq)

/-- **Induction on the indecomposables**: `Ind([E^{(a)}] ⊗ [E^{(b)}]) = [E^{(a)}E^{(b)}]`, the
class of `ONH_{a+b}(e_a ⊗ e_b){C(a,2) + C(b,2)}`. -/
theorem indK0_Eclass : ∀ a b, indK0 a b (Eclass a) (Eclass b) = indClass a b
  | 0, 0 => (pairZZ.indK0_of_of _ _).trans (K0.of_eq (pairZZ.ind_gelem one_mem (one_mul 1)
      one_mem (one_mul 1) one_mem (one_mul 1) (by simp [pairZZ, SuperPair.intLeft]) (add_zero 0)))
  | 0, 1 => (pairZO.indK0_of_of _ _).trans (K0.of_eq (pairZO.ind_gelem one_mem (one_mul 1)
      one_mem (one_mul 1) one_mem (one_mul 1) (by simp [pairZO, SuperPair.intLeft]) (add_zero 0)))
  | 1, 0 => (pairOZ.indK0_of_of _ _).trans (K0.of_eq (pairOZ.ind_gelem one_mem (one_mul 1)
      one_mem (one_mul 1) one_mem (one_mul 1) (by simp [pairOZ, SuperPair.intRight])
      (add_zero 0)))
  | 1, 1 => (pairOO.indK0_of_of _ _).trans (K0.of_eq (pairOO.ind_gelem one_mem (one_mul 1)
      one_mem (one_mul 1) (blockE_pair_mem 0 1 1) (ThickDecomposition.blockE_pair_idem rfl)
      (by
        show dotHom 0 0 1 * dotHom 0 1 1 = _
        rw [map_one, map_one, ThickBubble.blockE_one, ThickBubble.blockE_one]) (by norm_num)))
  | 0, b+2 => (SuperPair.indK0_of_of _ _ _).trans (K0.of_eq (SuperPair.ind_gelem _ one_mem
      (one_mul 1) (projector_mem b) ZeroHecke.projector_mul_projector
      (blockE_pair_mem (0+b) 0 (b+2)) (ThickDecomposition.blockE_pair_idem rfl)
      (by
        show ((1 : ℤ) : Presented (0+b)) * windowHom b (0+b) 0 _ (ZeroHecke.projector b) = _
        rw [← blockE_eq, Int.cast_one]
        rfl)
      (by push_cast; simp [Nat.choose])))
  | 1, b+2 => (SuperPair.indK0_of_of _ _ _).trans (K0.of_eq (SuperPair.ind_gelem _ one_mem
      (one_mul 1) (projector_mem b) ZeroHecke.projector_mul_projector
      (blockE_pair_mem (1+b) 1 (b+2)) (ThickDecomposition.blockE_pair_idem rfl)
      (by
        show dotHom (1+b) 0 1 * windowHom b (1+b) 1 _ (ZeroHecke.projector b) = _
        rw [← blockE_eq, map_one]
        rfl)
      (by push_cast; simp [Nat.choose])))
  | a+2, 0 => (SuperPair.indK0_of_of _ _ _).trans (K0.of_eq (SuperPair.ind_gelem _
      (projector_mem a) ZeroHecke.projector_mul_projector one_mem (one_mul 1)
      (blockE_pair_mem a (a+2) 0) (ThickDecomposition.blockE_pair_idem rfl)
      (by
        show windowHom a a 0 _ (ZeroHecke.projector a) * ((1 : ℤ) : Presented a) = _
        rw [← blockE_eq, Int.cast_one]
        rfl)
      (by push_cast; simp [Nat.choose])))
  | a+2, 1 => (SuperPair.indK0_of_of _ _ _).trans (K0.of_eq (SuperPair.ind_gelem _
      (projector_mem a) ZeroHecke.projector_mul_projector one_mem (one_mul 1)
      (blockE_pair_mem (a+1) (a+2) 1) (ThickDecomposition.blockE_pair_idem rfl)
      (by
        show windowHom a (a+1) 0 _ (ZeroHecke.projector a) * dotHom (a+1) ⟨a+2, _⟩ 1 = _
        rw [← blockE_eq, map_one]
        rfl)
      (by push_cast; simp [Nat.choose])))
  | a+2, b+2 => (SuperPair.indK0_of_of _ _ _).trans (K0.of_eq (SuperPair.ind_gelem _
      (projector_mem a) ZeroHecke.projector_mul_projector (projector_mem b)
      ZeroHecke.projector_mul_projector (blockE_pair_mem (a+2+b) (a+2) (b+2))
      (ThickDecomposition.blockE_pair_idem rfl)
      (by
        show windowHom a (a+2+b) 0 _ (ZeroHecke.projector a) *
          windowHom b (a+2+b) (a+2) _ (ZeroHecke.projector b) = _
        rw [← blockE_eq, ← blockE_eq])
      (by push_cast; simp [Nat.choose])))

end Eclass

/-! ### The product of `K₀(ONH)` -/

/-- The product `K₀(ONH) ⊗ K₀(ONH) → K₀(ONH)` induced by induction on all components:
`[P] ⊗ [Q] ↦ [Ind(P ⊠ Q)] ∈ K₀(ONH_{a+b})` for `P ∈ ONH_a-pmod`, `Q ∈ ONH_b-pmod`. -/
def indProd : K0ONH →ₗ[L] K0ONH →ₗ[L] K0ONH :=
  DFinsupp.lsum L fun a =>
    (DFinsupp.lsum L fun b => (indK0 a b).flip.compr₂ (DFinsupp.lsingle (a + b))).flip

theorem indProd_single (a b : ℕ) (x : KONH a) (y : KONH b) :
    indProd (DFinsupp.single a x) (DFinsupp.single b y) =
      DFinsupp.single (a + b) (indK0 a b x y) := by
  rw [indProd, DFinsupp.lsum_single, LinearMap.flip_apply, DFinsupp.lsum_single,
    LinearMap.compr₂_apply, LinearMap.flip_apply, DFinsupp.lsingle_apply]

/-- **The product of `K₀(ONH)` is induced by induction**: the `ℤ[q,q⁻¹]`-bilinear product of
`OddCategorification` (determined there on the basis `[E^{(a)}]`) equals `indProd`. -/
theorem mulK0_eq_indProd : mulK0 = indProd :=
  LinearMap.ext_basis basisK0 basisK0 fun a b => by
    rw [mulK0_basis, basisK0_apply, basisK0_apply, indProd_single, indK0_Eclass]

theorem mul_eq_indProd (x y : K0ONH) : x * y = indProd x y := by
  rw [mul_def, mulK0_eq_indProd]

/-- `[P] · [Q] = [Ind(P ⊠ Q)]` for arbitrary classes `x ∈ K₀(ONH_a)`, `y ∈ K₀(ONH_b)`. -/
theorem single_mul_single_ind (a b : ℕ) (x : KONH a) (y : KONH b) :
    (DFinsupp.single a x : K0ONH) * DFinsupp.single b y =
      DFinsupp.single (a + b) (indK0 a b x y) := by
  rw [mul_eq_indProd, indProd_single]

/-- The same, through `eq_6_3 : U_q^+(sl_2)_A ≅ K₀(ONH)`: the algebra structure transported from
`U_q^+(sl_2)_A` is induction of graded projectives. -/
theorem eq_6_3_mul (u v : DivPowAlg) : eq_6_3 (u * v) = indProd (eq_6_3 u) (eq_6_3 v) := by
  rw [map_mul, mul_eq_indProd]

end OddMath.Frontier.OddBialgebra
