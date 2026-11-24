import GaugeFieldConstruction.Cream
import GaugeFieldConstruction.Provis
import GaugeFieldConstruction.TwoEyes

/-!
# Faithful reflection on this (degree + derivative) budget
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Window Vouchers Abacus Cauchy Row Phys Calibration Function Wick Raster Gap Finset Mirror Floor
open scoped BigOperators
lemma ticketsC : ∃ F:Window FIndex (Coin FIndex), Complete (bound 3) (iform true) F := by
  rw [← greaseC]; exact ⟨_, RateC.paid⟩
lemma ticketsR : ∃ F:Window FIndex (Coin FIndex), Complete (bound 3) (iform false) F := by rw [← greaseR]; exact ⟨_,RateR.paid⟩
lemma ticketsG : ∃ M:Window GIndex (Coin GIndex), Complete (formG 2) gico M :=by rw [← greaseG]; exact ⟨_, RateG.paid⟩

def truthful := Clock (formG 2) (bound 3)
/-- Ratio proof works here simply at unit time separation (opposites plus and minus one-half). -/
lemma price_positive (w : Shell) (p : w∈truthful) (h : w≠0) : 0 < (stare (couples (night w) w)).re := by
  obtain ⟨C,Q⟩:= ticketsC
  obtain ⟨R,H⟩:= ticketsR
  obtain ⟨M,V⟩:= ticketsG
  change 0 < (stare (Wick.pair (dress (night w)) _)).re
  rw [Mirror.total]; apply warmed Q H V (dress w) p; exact fun e=> h (cred (e.trans dress.map_zero.symm))
lemma illuminated {w : Shell} (p : w∈truthful) (h : couples (night w) w=0) : w=0 := by
  by_contra e; have k:= price_positive w p e; simp [h] at k
lemma mirror_positive (i : Floor) (z : UV i) (q : z≠0) :
    0<(stare (couples (shells i (shade i (spinFrame i mirror z))) (shells i z))).re := by
  rw [← Mirror.price]; apply price_positive _ (prim ..); exact fun e=> q (shell_in _ (e.trans (shells i).map_zero.symm))

/-- Probe UV5 in *external first position*, allow derivative in it. -/
def paper : Shell→ₗ[ℂ] UV five→ₗ[ℂ] SmoothGap := (couples.compl₁₂ (shells five) LinearMap.id).flip
lemma select {z : UV five} : paper (shells five z)=0 ↔ z=0 := by
  refine ⟨fun h=>?_,fun h=> by simp [h]⟩
  by_contra e
  have he:= mirror_positive five z e
  have h : couples _ _=0:= LinearMap.congr_fun h (shade five (spinFrame five mirror z)) -- adjust
  rw [LinearMap.id_apply] at h; rw [h,map_zero] at he; simp at he
/-- Cannot hear: also vanishes against derivatives of external slot. -/
lemma blank {p : Shell} (h : paper p=0) (b : UV five) (i : Axis) : couples (P i (shells five b)) p=0 := by
  have ht : couples (shells five b) p=0:= LinearMap.congr_fun h b
  rw [left_leg,ht,map_zero,neg_zero]
lemma silver (p : Shell) (h : paper p=0) (b : UV five) (i : Axis) : couples (night (P i (shells five b))) p=0 := by
  rw [time_P,price]; cases clockbit: Mirror.clock i <;> simp only [pay_true,pay_false, map_neg,blank h, LinearMap.neg_apply,neg_zero]
lemma point_ker (a : OneW × BothV) (k j) : paper (combMap a (k,j))=0 ↔ combMap a (k,j)=0 := by
  let p:= combMap a (k,j)
  refine ⟨?_,fun h=> by rw [h,map_zero]⟩; intro h
  apply illuminated
  · rw [Calibration.combo]; exact Submodule.sub_mem _ (Submodule.sum_mem _ fun i _=> principal ..) (principal ..)
  change couples (night _) p=0
  rw [Calibration.combo, map_sub, map_sum,map_sub,map_sum,LinearMap.sub_apply,LinearMap.sum_apply]
  have ht:=silver p h
  simp_rw [ht]; simp

lemma single_ker {a : UV five} (k : Axis) : paper (P k (shells five a))=0 ↔ P k (shells five a)=0 := by
  refine ⟨fun h=>illuminated (principal ..) (silver _ h a k), fun e=>by rw [e,map_zero]⟩
lemma poetry : Function.Injective (paper ∘ₗ shells five) := by
  intro a b h
  refine sub_eq_zero.mp (select.mp ?_)
  rw [map_sub, map_sub, show paper (shells _ a)=paper (shells _ b) from h, sub_self]

/-- Test as smooth kernels on punctured Euclidean four (equivalently we can use
 compactly supported tests later), z taking all second slots of the indicated type.
 No need to prescribe independent UV-six field for that equality. -/
def duos : (OneW×BothV) →ₗ[ℂ] Axis×Axis→(UV five→ₗ[ℂ] SmoothGap) := LinearMap.pi fun x=> paper ∘ₗ LinearMap.proj x ∘ₗ combMap
theorem separated_exact : LinearMap.ker duos=LinearMap.range previous := by
  rw [← exact_93]; ext1 x; simp only [LinearMap.mem_ker]
  refine ⟨fun h=>?_,fun h=>?_⟩
  · ext1 ⟨k,j⟩; exact (point_ker x k j).mp (congr_fun h (k,j))
  ext1 ⟨k,j⟩; exact (point_ker x k j).mpr (congr_fun h (k,j))
theorem separated_rank : Module.finrank ℂ (LinearMap.range duos)=59 := by
  letI : AddCommGroup ↥OneW := @Submodule.addCommGroup ℂ (Axis → UV five) _ _ _ OneW
  letI : AddCommGroup ↥BothV := @Submodule.addCommGroup ℂ (Raw.VS → UV five) _ _ _ BothV
  haveI := Module.Free.of_divisionRing ℂ ↥OneW
  haveI := Module.Free.of_divisionRing ℂ ↥BothV
  rw [← r93]
  have h:= @LinearMap.finrank_range_add_finrank_ker ℂ (OneW×BothV) _ _ _ (Axis×Axis→ UV five→ₗ[ℂ] SmoothGap) _ _ _ duos
  have p:= @LinearMap.finrank_range_add_finrank_ker ℂ (OneW×BothV) _ _ _ (Axis × Axis→Shell) _ _ _ combMap
  rw [exact_93] at p; rw [separated_exact] at h
  exact Nat.add_right_cancel (h.trans p.symm)

-- derivative squared reflected test
lemma solo_d (i : Axis) (x : SymT) (p : ∀ v,paper (shells five ((deriv i) (x.val v)))=0):x=0 := bright i 1 _ (fun v=>by
  have ht:= select.mp (p v);
  suffices E : P i (shells four (x.val v))=0 from by simpa using E
  rw [show P i (shells four (x.val v))=_ from Eq.symm (LinearMap.congr_fun (scene i) _),LinearMap.comp_apply,ht,map_zero]) -- tweak
lemma duo_d (i : Axis) (x : SymT) (p : ∀ v,paper (P i (shells five ((deriv i) (x.val v))))=0):x=0 := bright i 2 _ (fun v=>by
  have h : P i (shells four (x.val v))=_ := Eq.symm (LinearMap.congr_fun (scene i) (x.val v))
  change P i (P i (shells four _)) = 0
  rw [h]; exact (single_ker i).mp (p v))
end YM.GaugeFieldConstruction.Invoice
