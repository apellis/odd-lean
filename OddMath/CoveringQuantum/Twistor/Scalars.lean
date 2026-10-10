import OddMath.CoveringQuantum.Twistor.Datum
import OddMath.CoveringQuantum.HalfAlgebra

/-!
# Scalar identities for the twisting comparison

For a unit `t` with `t² = -1`, the change `q ↦ tq` converts the `π = -1`
normalization to the ordinary one. The skew part of the ordered form gives the
corresponding ratio of bicharacters. Bar-consistency is essential here.
-/

namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {I k : Type*} [LinearOrder I] [CommRing k]
  (C : SuperCartanDatum I) (hC : C.BarConsistent) (q t : kˣ) (ht : t ^ 2 = -1)

include hC ht

/-- The ordered phases have the ratio required for the super bicharacter. -/
theorem twist_phase_ratio (i j : I) :
    t ^ C.twistPhi i j * (t ^ C.twistPhi j i)⁻¹ =
      t ^ C.dot i j * (-1 : kˣ) ^ ((C.parity i).val * (C.parity j).val) := by
  have ht4 : t ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = 2 * 2 by norm_num, zpow_mul]
    norm_num [ht]
  have hs : t ^ (C.twistPhi i j - C.twistPhi j i) =
      t ^ (C.dot i j + 2 * (C.parity i).val * (C.parity j).val) := by
    calc
      _ = t ^ ((C.twistPhi i j - C.twistPhi j i) % 4) := zpow_eq_zpow_emod _ ht4
      _ = t ^ ((C.dot i j + 2 * (C.parity i).val * (C.parity j).val) % 4) :=
        congrArg (fun n : ℤ ↦ t ^ n) (C.twistPhi_skew_mod_four hC i j)
      _ = _ := (zpow_eq_zpow_emod _ ht4).symm
  rw [← zpow_sub, hs, zpow_add]
  congr 1
  rw [show (2 : ℤ) * (C.parity i).val * (C.parity j).val =
    2 * (((C.parity i).val * (C.parity j).val : ℕ) : ℤ) by push_cast; ring,
    zpow_mul, zpow_ofNat, ht, zpow_natCast]

/-- The bicharacters at the two signs differ by the ratio of ordered phases. -/
theorem chi_twist (i j : I) :
    C.chi (t * q) 1 i j * (t ^ C.twistPhi i j * (t ^ C.twistPhi j i)⁻¹ : kˣ) =
      C.chi q (-1) i j := by
  rw [C.twist_phase_ratio hC t ht]
  have hp : (-1 : kˣ) ^ ((C.parity i).val * (C.parity j).val) =
      (-1 : kˣ) ^ (C.parity i * C.parity j).val := by
    rw [ZMod.val_mul, pow_eq_pow_mod _ (show (-1 : kˣ) ^ 2 = 1 by simp)]
  rw [hp]
  simp only [chi, one_pow, mul_one, mul_zpow, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]
  rw [show ((t ^ (-C.dot i j) : kˣ) : k) * ((q ^ (-C.dot i j) : kˣ) : k) *
      (((t ^ C.dot i j : kˣ) : k) * (-1) ^ (C.parity i * C.parity j).val) =
      (((t ^ (-C.dot i j) * t ^ C.dot i j : kˣ) : k)) *
        (((q ^ (-C.dot i j) : kˣ) : k) * (-1) ^ (C.parity i * C.parity j).val) by
    simp only [Units.val_mul]; ring]
  rw [← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]

omit [LinearOrder I] in
/-- The generator normalization is unchanged after the parameter twist. -/
theorem norm_twist (i : I) : C.norm (t * q) 1 i = C.norm q (-1) i := by
  have hp : (-1 : kˣ) ^ C.d i = (-1 : kˣ) ^ (C.parity i).val := by
    have hm := congrArg ZMod.val (hC i)
    simp only [ZMod.val_natCast] at hm
    rw [pow_eq_pow_mod _ (show (-1 : kˣ) ^ 2 = 1 by simp), hm]
  have ht' : (t ^ C.d i) ^ 2 = (-1 : kˣ) ^ (C.parity i).val := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ht, hp]
  simp only [norm, pii, one_pow, one_mul, qi, mul_pow, Units.val_mul,
    Units.val_pow_eq_pow_val]
  congr 2
  congr 1
  have h := congrArg (fun u : kˣ ↦ (u : k)) ht'
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using h

end OddMath.CoveringQuantum.SuperCartanDatum
