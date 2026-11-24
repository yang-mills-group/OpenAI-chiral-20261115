import YM.SU5.FiniteGaugeData.LocalLimit.Local.Smoothing
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-! # Compact digest of whole L¹ unit ball sufficient for advancement estimates

Parameters only a list of predicted edge values in support and compact β range.
Capacity for number of tags never enters these estimates; advance evaluates each
possible prediction at each such tag with convex weights. Smooth probing on
product space.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Filter MeasureTheory Function
open scoped Topology BigOperators Classical BoundedContinuousFunction
namespace BoxGauge
variable {G:Gauge}(r:ℕ) {c f:Side} (S:StepData c f)(A B:paper G r)
local notation "Ω" => Space G r
variable (d:ℝ)
abbrev Pillow (G:Gauge)(r:ℕ)(d:ℝ) := Set.Icc (-d) d × Space G r
local notation "T" => Pillow G r d
local notation "μ" => credits G r
local notation "F" => (Ω →ᵇ ℂ)
-- dual smooth test measurement
def nib (p:Pillow G r d) : Space G r →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact ⟨snow r S p.1.val p.2, (snow_c (G:=G) r S).comp ((continuous_const (y:=(p.1.val,p.2))).prodMk continuous_id)⟩
lemma nib_c : Continuous (nib (G:=G) r S d) := by
 let N(x: T):= (nib r S d x).toContinuousMap; have he:Continuous N:= by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_; exact (snow_c r S).comp (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
 exact (ContinuousMap.isometryEquivBoundedOfCompact (Space G r) ℂ).continuous.comp he
-- estimate dual
private lemma int_mark (P: F): Integrable (fun i=>P i*A.val i) (credits G r):= ((Envelope.compactC P.continuous).mulC (paid r A).1).integrableC _
def ink : (Space G r →ᵇ ℂ)→ₗ[ℂ] ℂ where
 toFun f := ∫ i,f i*A.val i∂ μ
 map_add' P Q := by simp_rw [BoundedContinuousFunction.add_apply,add_mul,integral_add (int_mark _ A P) (int_mark _ A Q)]
 map_smul' c V:=by simp_rw [BoundedContinuousFunction.smul_apply, Algebra.smul_mul_assoc,integral_smul]; rfl
lemma ink_bill (P:F) : ‖ink r A P‖ ≤ weight r A * ‖P‖:= by
 let h:= int_mark r A P; apply (norm_integral_le_integral_norm ..).trans
 calc
   _ ≤ ∫ i, ‖A.val i‖ * ‖P‖ ∂μ:= by
       apply integral_mono h.norm (((paid r A).1.integrableC μ).norm.mul_const _); intro i; dsimp only; rw [norm_mul,mul_comm ‖A.val i‖]; exact mul_le_mul_of_nonneg_right (P.norm_coe_le_norm _) (norm_nonneg _)
   _ = _ := integral_mul_const ..
def priceInk : (Space G r →ᵇ ℂ)→L[ℂ] ℂ:= (ink r A).mkContinuous (weight r A) (ink_bill r A)
lemma ink_norm : ‖priceInk r A‖ ≤ weight r A := LinearMap.mkContinuous_norm_le _ (weight_pos ..) (ink_bill r A)
private def blkv : (Pillow G r d) →ᵇ ℂ:=BoundedContinuousFunction.mkOfCompact ⟨fun x=> priceInk r A (nib r S d x), (priceInk r A).continuous.comp (nib_c (G:=G) r S d)⟩
private lemma bv (u:Pillow G r d): blkv r S A d u=news r S A u.1 u.2:=rfl -- coe tune
variable {A}
def digest : ↥(paper G r) →ₗ[ℂ] (Pillow G r d →ᵇ ℂ) where
 toFun A := blkv r S A d
 map_add' A B:=by ext i:1; change news r S (A+B) _ _= priceInk r A _ + priceInk r B _; unfold news; simp_rw [Subalgebra.coe_add,Pi.add_apply,mul_add]; exact integral_add (int_mark r A (nib r S d i)) (int_mark r B (nib r S d i))
 map_smul' c V:=by ext i:1; change news r S (c • V) _ _= c • priceInk r V _; unfold news; simp_rw [Subalgebra.coe_smul, Pi.smul_apply,Algebra.mul_smul_comm]; exact integral_smul ..
local notation "W" => Set.range (fun x:{A : ↥(paper G r) // weight r A ≤ 1}=> digest r S d x.val)
variable (A)
lemma digest_at (x:Pillow G r d): digest r S d A x=news r S A x.1 x.2:=rfl
private lemma uniform_norm: ∃ Z:ℝ, 0 ≤ Z ∧∀ i: Pillow G r d, ‖nib r S d i‖ ≤ Z:= by
 obtain ⟨R,h⟩:= (isCompact_range (nib_c (G:=G) r S d).norm).bddAbove
 exact ⟨max 0 R,le_max_left ..,fun x=>(show ‖nib r S d x‖ ≤ R from h ⟨x,rfl⟩).trans (le_max_right ..)⟩
lemma digest_norm : ∃ C:ℝ, 0 ≤ C ∧ ∀ A:paper G r, ‖digest r S d A‖ ≤ weight r A * C:= by
 obtain ⟨K,p,h⟩:= uniform_norm (G:=G) r S d; refine ⟨K,p,fun A=>?_⟩
 apply (BoundedContinuousFunction.norm_le (mul_nonneg (weight_pos r A) p)).2; intro i
 exact le_trans (ink_bill r A (nib r S d i)) (mul_le_mul_of_nonneg_left (h i) (weight_pos r A))
lemma digest_compact : IsCompact (closure W):= by
 obtain ⟨c,v,hv⟩:= digest_norm (G:=G) r S d; apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:ℂ) c) (isCompact_closedBall ..)
 · rintro f1 x ⟨⟨A,h⟩,rfl⟩
   rw [Metric.mem_closedBall,dist_zero_right]; exact ((digest r S d A).norm_coe_le_norm x).trans ((hv A).trans (by nlinarith))
 intro x; apply Metric.equicontinuousAt_iff_right.mpr; intro ε y
 filter_upwards [((nib_c (G:=G) r S d).continuousAt (x:=x)).preimage_mem_nhds (Metric.ball_mem_nhds (nib r S d x) y)] with k q
 rintro ⟨F₀,⟨⟨A,h⟩,rfl⟩⟩; rw [dist_eq_norm]; change ‖ink r A (nib r S d x) - ink r A (nib r S d k)‖ < ε; rw [←map_sub]; apply lt_of_le_of_lt (ink_bill r A _)
 refine lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) h) ?_
 rw [←dist_eq_norm,dist_comm]; exact q
end BoxGauge
end YM.Push.GridApprox
