import YM.SU5.Reconstruction.UVPrice.Frequencies
/-!
# Actual spectrum on the budget subpart. Palette accountant via all stamps, any normalization.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
variable {Γ: AddSubgroup ℝ}
local notation "Q"=> Coupon a Γ
namespace Coupon
variable (q: Coupon a Γ)
local notation "P"=> S.ℚmeasure
local notation "μ" x:max => (P).diagonal x
noncomputable def tagT (x:H)(q: Coupon a Γ):ℂ:= inner ℂ x (cash S q x)
@[fun_prop] lemma tag_conti: Continuous (tagT (Γ:=Γ) S):= continuous_pi (fun i=> continuous_id.inner (cash S i).continuous)
lemma pays_t (x:H): tagT S x q = ∫ p,receipt p q∂ μ x:= (firm S q).awakes x
@[simp] lemma tag_zero (x:H) : tagT S x (0:Q) = (‖x‖^2:ℝ) := by rw [pays_t]; simp [Registers.size]
variable (Γ)
abbrev Population:Set (Coupon a Γ→ℂ) := closure (Set.range (tagT (Γ:=Γ) S))
variable {Γ}
-- approximate all receipts at once. localize to spectrum and pass on any unbounded tester
lemma climb (x:E4) (u:x∈Shelf S): receipt x ∈Population S Γ:=by
 let L (i:ℕ):=1/((i:ℝ)+1); let W(i:ℕ):= ball x (L i); have he(i):MeasurableSet (W i):= measurableSet_ball
 have ht:Tendsto L atTop (𝓝 0):=by unfold L; exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) -- tune
 have hw(i:ℕ) : ∃ v:H,‖v‖=1 ∧ (P).region (W i) v=v:= by
   have h:L i>0:= by unfold L; positivity
   obtain ⟨y,b,c⟩:= Metric.mem_closure_iff.mp u (L i) h
   obtain ⟨z,t⟩:= Set.mem_iUnion.mp b; have hu: y∈ W i:= Metric.mem_ball.mpr (by rw [dist_comm]; exact c)
   have hv : 0 < (P).diagonal z (W i):= Measure.mem_support_iff_forall y|>.1 t (W i) (isOpen_ball.mem_nhds hu) -- tune
   let T:= (P).region (W i) z; have hz: 0 < ‖T‖:= norm_pos_iff.mpr (fun q=> hv.ne' (((P).null_pair (he i) z).2 q))
   refine ⟨((‖T‖⁻¹:ℝ):ℂ) • T,?_,?_⟩
   · rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ hz.ne']
   rw [map_smul,show (P).region (W i) T=T from (P).idempotent (he i) z]
 choose f g h using hw
 have hk(i:ℕ): ∀ᵐ x∂ μ (f i), x∈ W i:=by nth_rw 1 [← h i]; rw [Registers.restricted S.ℚmeasure (he i)]; exact ae_restrict_mem (he i)
 refine mem_closure_of_tendsto (b:=atTop) (f:=fun i=> tagT (Γ:=Γ) S (f i)) ?_ (Eventually.of_forall (fun _=> mem_range_self _))
 refine tendsto_pi_nhds.mpr (fun p=> Metric.tendsto_nhds.mpr (fun ε e=> ?_))
 obtain ⟨δ,b,u⟩:= Metric.continuousAt_iff.mp ((durable p).continuousAt (x:=x)) (ε/2) (by positivity)
 filter_upwards [ht.eventually (gt_mem_nhds b)] with i t
 rw [pays_t, dist_eq_norm]
 have hs: receipt x p= ∫ _,receipt x p∂ μ (f i):= by simp [Registers.size,g]
 nth_rw 1 [hs]; rw [← integral_sub]
 · refine le_trans (b:=(ε/2)*((P).diagonal (f i)).real univ) ?_ ?_|>.trans_lt (show ε/2<ε by linarith) -- tune goal refactor
   apply norm_integral_le_of_norm_le_const (C:=ε/2) ?_
   swap; · simp [Registers.size,g]
   filter_upwards [hk i] with y hy; rw [← dist_eq_norm]; exact (u ((Metric.mem_ball.mp hy).trans t)).le -- dist→ norm def?
 · exact (firm S p).price.rent _ _
 exact integrable_const _
end Coupon
end YM.Roy
