/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SlideNe

/-! # Two-factor Q transport through distinct-colour slides

Generic algebra for the reverse mixed braid in
`docs/Nondegeneracy/SwappedActionAssembly.md`, §3. The homogeneous dot slides used
here are the distinct-colour slides; there is no divided-difference correction.
The parity support of the scalar parameters removes the signs. Commutation of
the target Q factors is derived from the three target dot supercommutations,
rather than supplied as a centrality hypothesis.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir

open CategoryTheory StringDiagrams OddMath.SKM Supercategory

universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} (Sc : Scalars D k)
  {C : Type*} [Category C] [Preadditive C] [Linear k C]

private theorem reverse_zsign_eq {A B : C} (f g : A ⟶ B) (p : ZMod 2)
    (h : f = zsign k p • g) : g = zsign k p • f := by
  rw [h, smul_smul, zsign_mul_self', one_smul]

/-- Two Q factors sharing a spectator commute if the three dots supercommute.
No self-supercommutation relation on the spectator is needed. -/
theorem qExpr_pair_comp_comm {A : C} (x y z : End A) (i j r : I)
    (hxy : x ≫ y = zsign k (D.parity i * D.parity j) • (y ≫ x))
    (hxz : x ≫ z = zsign k (D.parity i * D.parity r) • (z ≫ x))
    (hyz : y ≫ z = zsign k (D.parity j * D.parity r) • (z ≫ y)) :
    qExpr Sc x z i r ≫ qExpr Sc y z j r =
      qExpr Sc y z j r ≫ qExpr Sc x z i r := by
  have hxQ : x ≫ qExpr Sc y z j r = qExpr Sc y z j r ≫ x := by
    apply comp_qExpr (Sc := Sc) x y z y z j r
      (zsign k (D.parity j * D.parity i))
      (zsign k (D.parity r * D.parity i))
    · simpa only [mul_comm] using hxy
    · simpa only [mul_comm] using hxz
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity j) (D.parity i)
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity r) (D.parity i)
  have hzQ : z ≫ qExpr Sc y z j r = qExpr Sc y z j r ≫ z := by
    apply comp_qExpr (Sc := Sc) z y z y z j r
      (zsign k (D.parity j * D.parity r)) 1
    · exact reverse_zsign_eq _ _ _ hyz
    · simp only [one_smul]
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity j) (D.parity r)
    · intro n _
      exact one_pow n
  symm
  apply comp_qExpr (Sc := Sc) (qExpr Sc y z j r) x z x z i r 1 1
  · simpa only [one_smul] using hxQ.symm
  · simpa only [one_smul] using hzQ.symm
  · intro n _
    exact one_pow n
  · intro n _
    exact one_pow n

/-- Transport and swap two Q factors using only homogeneous signed dot slides
and target dot supercommutation. For applications the two probe colours are
unequal; the algebra itself does not require an inequality once the slides are
provided. Source and target products below are categorical composites (the
opposite order to multiplication in `End`). -/
theorem qExpr_pair_swap_transport {A B : C} (g : A ⟶ B)
    (x y z : End A) (x' y' z' : End B) (i j r : I)
    (hx : x ≫ g = zsign k (D.parity i * D.parity j) • (g ≫ y'))
    (hy : y ≫ g = zsign k (D.parity i * D.parity j) • (g ≫ x'))
    (hz : z ≫ g = zsign k (D.parity i * D.parity j * D.parity r) • (g ≫ z'))
    (hxy : x' ≫ y' = zsign k (D.parity j * D.parity i) • (y' ≫ x'))
    (hxz : x' ≫ z' = zsign k (D.parity j * D.parity r) • (z' ≫ x'))
    (hyz : y' ≫ z' = zsign k (D.parity i * D.parity r) • (z' ≫ y')) :
    qExpr Sc x z i r ≫ qExpr Sc y z j r ≫ g =
      g ≫ qExpr Sc x' z' j r ≫ qExpr Sc y' z' i r := by
  have hz' : g ≫ z' =
      zsign k (D.parity r * (D.parity i * D.parity j)) • (z ≫ g) := by
    simpa only [mul_comm] using reverse_zsign_eq _ _ _ hz
  have hQi : g ≫ qExpr Sc y' z' i r = qExpr Sc x z i r ≫ g := by
    apply comp_qExpr (Sc := Sc) g x z y' z' i r
      (zsign k (D.parity i * D.parity j))
      (zsign k (D.parity r * (D.parity i * D.parity j)))
    · exact reverse_zsign_eq _ _ _ hx
    · exact hz'
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity i) (D.parity j)
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity r)
        (D.parity i * D.parity j)
  have hQj : g ≫ qExpr Sc x' z' j r = qExpr Sc y z j r ≫ g := by
    apply comp_qExpr (Sc := Sc) g y z x' z' j r
      (zsign k (D.parity j * D.parity i))
      (zsign k (D.parity r * (D.parity i * D.parity j)))
    · simpa only [mul_comm] using reverse_zsign_eq _ _ _ hy
    · exact hz'
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity j) (D.parity i)
    · exact zsign_pow_of_mul_eq_zero (k := k) (D.parity r)
        (D.parity i * D.parity j)
  calc
    qExpr Sc x z i r ≫ qExpr Sc y z j r ≫ g =
        qExpr Sc x z i r ≫ g ≫ qExpr Sc x' z' j r := by rw [hQj]
    _ = g ≫ qExpr Sc y' z' i r ≫ qExpr Sc x' z' j r := by
      rw [← Category.assoc, ← hQi, Category.assoc]
    _ = g ≫ qExpr Sc x' z' j r ≫ qExpr Sc y' z' i r := by
      rw [qExpr_pair_comp_comm Sc y' x' z' i j r
        (by simpa only [mul_comm] using reverse_zsign_eq _ _ _ hxy) hyz hxz]

end OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
