import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLeftCap
import OddMath.SKM.RouquierFTriangle

/-! # Negative-height normalization of the whole-weight probe counit

SwappedActionAssembly F2: retain the prescribed diagonal Koszul factor
of the whole-weight left adjunction. Multiplying its normalized counit
by that factor recovers the exact raw inverse cap. On missing blocks,
the cap is then the previously identified stored local row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
private theorem total_zsmul
    {k C A : Type*} [CommRing k] [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (η : F ⟶ G) (z : ℤ) (M : C) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc

/-- The diagonal parity factor exactly cancels the prescribed
negative-height normalization of the whole-weight left counit. -/
theorem probeOldLeftCounit_negative_sign (i : I) {x y : X}
    (h : x + D.α i = y) (hh : D.h i x < 0) :
    koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • ((T).leftAdjoints.adjL i h).counit =
      (probeOldWeightLoc D Sc m i Λ (sub_add_cancel x (D.α i)) h (hc i)).capL := by
  change koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • ((T).leftAdjoints.adjL i h).counit = (T).leftCap i h
  rw [SKM.RouquierFamily.leftAdjoints_counit, SKM.RouquierFamily.leftAdjScalar_inv_coe,
    ite_eq_left hh, mul_one, Int.cast_smul_eq_zsmul, smul_smul, koszulSign_mul_self, one_smul]

/-- At every missing output block, the normalized whole-weight counit,
with its prescribed pre-Hom parity factor, is the exact stored raw cap
under the specified successor chart. -/
theorem probeOldLeftCounit_missing (i : I) {x y : X}
    (h : x + D.α i = y) (hh : D.h i x < 0)
    (δ : WeightBlocks D Λ x)
    (hδ : ¬ ∃ β, blockSucc D Λ i (sub_add_cancel x (D.α i)) β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • (((T).leftAdjoints.adjL i h).counit.total M δ) =
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) ≫
        (probeMissingStoredLoc D Sc m δ.1.toList i
          (probeOldBlockTarget_perm D i Λ h δ (blockSucc D Λ i h δ) rfl)
          (by simpa only [Multiset.mem_toList] using
            (show i ∉ δ.1 from fun hm => hδ
              ((exists_blockSucc_iff D Λ i (sub_add_cancel x (D.α i)) δ).mpr hm)))).capL.total (M δ) := by
  have hf := probeOldLeftCounit_negative_sign D Sc m Λ hc i h hh
  have ht := congrArg (fun f : (T).E i h ≫ (T).F i h ⟶ 𝟙 ((T).obj x) => f.total M δ) hf
  have he : koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • (((T).leftAdjoints.adjL i h).counit.total M δ) =
      (probeOldWeightLoc D Sc m i Λ (sub_add_cancel x (D.α i)) h (hc i)).capL.total M δ := by
    have hz := congrFun (total_zsmul ((T).leftAdjoints.adjL i h).counit
      (koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x)) M) δ
    exact hz.symm.trans ht
  exact he.trans (probeOldWeightLoc_cap_missing D Sc m i Λ
    (sub_add_cancel x (D.α i)) h δ (hc i) hδ hh M)

end OddMath.QuiverHecke
