/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Grading
import OddMath.SKM.CoveringDatum
import Categorification.QuantumGroup.UDotBlock
import Categorification.Diagrams.CL.Scalars
import Categorification.KLR.KL2.Datum

/-!
# Even data of `𝔘(𝔤)` as Khovanov–Lauda / Cautis–Lauda data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1: when every
colour is even (`|i| = 0`), Definition 1.5 is Rouquier's definition of the Kac–Moody
2-category, which J. Brundan, *On the definition of Kac–Moody 2-categories*, arXiv:1501.00350,
identifies with the presentation of A. D. Lauda, M. Khovanov (KL III, arXiv:0807.3250) and
S. Cautis, A. D. Lauda (arXiv:1111.1431). This file is the dictionary between the two sets of
data, used to compare the two presentations:

* `EvenBridge.Compatible D C`: the Cartan matrix of `D` is the one of the symmetric datum `C`,
  `⟨hᵢ, αⱼ⟩ = 2 (i·j)/(i·i)`;
* `EvenBridge.weightDatum`: the KL III weight datum `(X, Hom(X, ℤ))` with roots and coroots of
  `D`;
* `EvenBridge.clScalars`: the Cautis–Lauda scalars `(t, s, r = 1)` of the parameters of `D`;
* `EvenBridge.symmetrizer`: the symmetrizer `dᵢ = (i·i)/2` of the grading (1.31).

For a covering root datum `R` (`CoveringQuantum.RootDatum`, which carries a symmetrizer),
`catCartan R` is the symmetric datum `i·j = dᵢ aᵢⱼ`, compatible with `R.toSKM`
(`compatible_catCartan`), and `symmetrizer` is then `R.skmSymmetrizer`
(`symmetrizer_catCartan`).

The relevant numerical identities are `dij_eq_dn` (`d_{ij}` of KL II agrees with `dᵢⱼ` of
Brundan–Ellis, including `i = j`, where both are `0`) and `dot_eq_zero_iff`.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : Categorification.QuantumGroup.CartanDatum I)

/-- The Cartan matrix of `D` is the one of the symmetric datum `C`:
`⟨hᵢ, αⱼ⟩ = 2 (i·j)/(i·i)`. -/
def Compatible : Prop :=
  ∀ i j, D.h i (D.α j) = Categorification.QuantumGroup.UDot.A C i j

/-- Every colour of `D` is even. -/
def IsEven : Prop := ∀ i, D.parity i = 0

variable {D C}

theorem d_eq (hc : Compatible D C) (i j : I) :
    D.d i j = -Categorification.QuantumGroup.UDot.A C i j := by
  simp [Datum.d, hc i j]

/-- `d_{ij}` of KL II is `dᵢⱼ = (-⟨hᵢ, αⱼ⟩)₊` of Brundan–Ellis, for all `i, j`. -/
theorem dij_eq_dn (hc : Compatible D C) (i j : I) : C.dij i j = D.dn i j := by
  have hpos := C.dot_self_pos i
  obtain ⟨q, hq⟩ := C.dvd_two_mul i j
  have hA : Categorification.QuantumGroup.UDot.A C i j = q := by
    unfold Categorification.QuantumGroup.UDot.A
    rw [hq, Int.mul_ediv_cancel_left _ hpos.ne']
  have hneg : -2 * C.dot i j / C.dot i i = -q := by
    rw [neg_mul, hq, ← mul_neg, Int.mul_ediv_cancel_left _ hpos.ne']
  rw [Categorification.QuantumGroup.CartanDatum.dij, hneg, Datum.dn, d_eq hc, hA]

/-- `i·j = 0` if and only if `dᵢⱼ = 0`. -/
theorem dot_eq_zero_iff (hc : Compatible D C) (i j : I) : C.dot i j = 0 ↔ D.d i j = 0 := by
  have hpos := C.dot_self_pos i
  have h := Categorification.QuantumGroup.UDot.di_mul_A C i j
  have hdi := Categorification.QuantumGroup.UDot.di_pos C i
  rw [d_eq hc, neg_eq_zero, ← h]
  constructor
  · intro h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · omega
    · exact h1
  · intro h0; rw [h0, mul_zero]

variable (D C)

/-- The KL III weight datum `(X, Hom(X, ℤ))` of `D`: the pairing is evaluation, `i_X = αᵢ` and
`i = hᵢ`. -/
def weightDatum (hc : Compatible D C) :
    Categorification.QuantumGroup.UDot.WeightDatum C X (Module.Dual ℤ X) where
  pair :=
    { toFun := fun y => y.toAddMonoidHom
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  iX := D.α
  iY := D.cd.coroot
  pair_iY_iX i j := hc i j

@[simp] theorem weightDatum_pair (hc : Compatible D C) (y : Module.Dual ℤ X) (μ : X) :
    (weightDatum D C hc).pair y μ = y μ := rfl

@[simp] theorem weightDatum_iX (hc : Compatible D C) (i : I) :
    (weightDatum D C hc).iX i = D.α i := rfl

@[simp] theorem weightDatum_iY (hc : Compatible D C) (i : I) :
    (weightDatum D C hc).iY i = D.cd.coroot i := rfl

variable {k : Type w} [CommRing k]

/-- The Cautis–Lauda scalars of the parameters of `D`: the same `tᵢⱼ` and `sᵢⱼ^{pq}`, and
`rᵢ = 1` (the normalization of the nil-Hecke relations in Definition 1.5). -/
def clScalars (hc : Compatible D C) (Sc : Scalars D k) :
    Categorification.KL3.Diagram.CL.CLScalars C k where
  t := Sc.t
  s := Sc.s
  r _ := 1
  t_self := Sc.t_self
  t_symm i j h := Sc.t_symm_of_d_eq_zero i j ((dot_eq_zero_iff hc i j).1 h)
  s_symm := Sc.s_symm

@[simp] theorem clScalars_t (hc : Compatible D C) (Sc : Scalars D k) (i j : I) :
    (clScalars D C hc Sc).t i j = Sc.t i j := rfl

@[simp] theorem clScalars_s (hc : Compatible D C) (Sc : Scalars D k) (i j : I) (p q : ℕ) :
    (clScalars D C hc Sc).s i j p q = Sc.s i j p q := rfl

@[simp] theorem clScalars_r (hc : Compatible D C) (Sc : Scalars D k) (i : I) :
    (clScalars D C hc Sc).r i = 1 := rfl

/-- The symmetrizer `dᵢ = (i·i)/2` of the grading (1.31): then `x` has degree `i·i`, as the
dot of KL III. -/
def symmetrizer (hc : Compatible D C) : Symmetrizer D where
  d := Categorification.QuantumGroup.UDot.di C
  pos := Categorification.QuantumGroup.UDot.di_pos C
  symm i j := by
    rw [d_eq hc, d_eq hc, mul_neg, mul_neg,
      Categorification.QuantumGroup.UDot.di_mul_A_comm]

@[simp] theorem symmetrizer_d (hc : Compatible D C) (i : I) :
    (symmetrizer D C hc).d i = Categorification.QuantumGroup.UDot.di C i := rfl

theorem two_mul_symmetrizer_d (hc : Compatible D C) (i : I) :
    2 * (symmetrizer D C hc).d i = C.dot i i :=
  Categorification.QuantumGroup.UDot.two_mul_di C i

/-! ### Covering root data -/

section RootDatum

variable {I X : Type*} [AddCommGroup X] (R : CoveringQuantum.RootDatum I X)

/-- The symmetric datum `i·j = dᵢ aᵢⱼ` of a covering root datum. -/
def catCartan : Categorification.QuantumGroup.CartanDatum I where
  dot := R.dot
  symm := R.dot_comm
  dot_self_pos := R.dot_self_pos
  dot_self_even i := ⟨R.d i, by rw [R.dot_self]; ring⟩
  dot_nonpos _ _ h := R.dot_nonpos h
  dvd_two_mul i j := ⟨R.a i j, by rw [R.dot_self, CoveringQuantum.SuperCartanDatum.dot]; ring⟩

@[simp] theorem catCartan_dot (i j : I) : (catCartan R).dot i j = R.dot i j := rfl

theorem compatible_catCartan : Compatible R.toSKM (catCartan R) := fun i j => by
  rw [CoveringQuantum.RootDatum.toSKM_α, CoveringQuantum.RootDatum.toSKM_h, R.h_α]
  exact (R.two_mul_dot_div i j).symm

theorem di_catCartan (i : I) : Categorification.QuantumGroup.UDot.di (catCartan R) i = R.d i := by
  unfold Categorification.QuantumGroup.UDot.di
  rw [catCartan_dot, R.dot_self]
  omega

theorem symmetrizer_catCartan :
    symmetrizer R.toSKM (catCartan R) (compatible_catCartan R) = R.skmSymmetrizer := by
  have key : ∀ s t : Symmetrizer R.toSKM, s.d = t.d → s = t := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl
  exact key _ _ (funext fun i => by
    rw [symmetrizer_d, di_catCartan, CoveringQuantum.RootDatum.skmSymmetrizer_d])

end RootDatum

end OddMath.SKM.EvenBridge
