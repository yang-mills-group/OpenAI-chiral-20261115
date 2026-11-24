import YM.SU5.Reconstruction.Trap.Shops
import YM.CF.BProof.Floral.Hol
import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
# Price of spectral integral of analytic data. Unbounded region in p.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X : Type*} [MeasurableSpace X] {H : Hilbert} (P : PVM H X)
local notation "𝔪" x:max => P.diagonal x
variable {D : Set ℂ} (h : IsOpen D) (F : ℂ→X→ℂ) (C :ℝ) (A : ℂ→ H.Op) (q :∀ z∈D, Registers P (F z) (A z))
variable (p:∀ x, DifferentiableOn ℂ (fun z=> F z x) D) (b:∀ z∈D,∀ x:X, ‖F z x‖≤ C)(v:∀ z:ℂ,Measurable (F z))
local notation "ω" x=> (fun z:ℂ=> F z x)
local notation "Ω" f=> (fun z:ℂ=> order P (f z)) -- maybe not
include h p C b
lemma roofs (z:ℂ) (t:z∈D): ∃ r>0, ball z r⊆ D ∧ ∀ x,∀ w∈ ball z r, ‖deriv (fun z=> F z x) w‖≤ C/r:= by
 obtain ⟨r,c,s⟩:= nhds_basis_closedBall.mem_iff.mp (h.mem_nhds t); let d:=r/2
 have he(t:ℂ)(p:t∈ ball z d): closedBall t d ⊆D:= by
   intro y y'; apply s; rw [mem_closedBall]; have hv := mem_closedBall.mp y'; have hb:= mem_ball.mp p; unfold d at *; linarith [dist_triangle y t z]
 refine ⟨d,half_pos c,fun x h=> he x h (mem_closedBall_self (half_pos c).le),fun x w s=> ?_⟩
 exact CF.Floral.c_deriv (p x) (half_pos c) (he _ s) (fun z u=> b z u x)
include v
lemma roofs_exact (z:ℂ) (t:z∈D): Tag (fun x=> deriv (fun z:ℂ=>F z x) z):= by
 refine ⟨measurable_of_tendsto_metrizable' (𝓝[≠] (0:ℂ)) (f:=fun y x=> y⁻¹ • (F (z+y) x-F z x)) (fun y=> by exact ((v (z+y)).sub (v z)).const_smul (y⁻¹ : ℂ)) (tendsto_pi_nhds.mpr fun x=> ((p x).differentiableAt (h.mem_nhds t)).hasDerivAt.tendsto_slope_zero),?_⟩
 obtain ⟨r,b',u,e⟩:= roofs h F C p b z t
 exact ⟨max 0 (C/r),le_max_left ..,fun x=> (e x z (mem_ball_self b')).trans (le_max_right ..)⟩
include q P
lemma ciel (z:ℂ)(t:z∈D) (x:H):
    HasDerivAt (fun z=> inner ℂ x (A z x)) (∫ p, deriv (fun z=>F z p) z ∂𝔪 x) z:= by
 obtain ⟨r,c,u,w⟩:= roofs h F C p b z t
 let V z x:= deriv (fun z=> F z x) z
 refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=V) (μ:=𝔪 x) (bound:=fun _=> C/r)
   (isOpen_ball.mem_nhds (mem_ball_self (x:=z) c)) (Eventually.of_forall fun x=> (v x).aestronglyMeasurable) ((q z t).price.rent P x)
   (roofs_exact h F C p b v z t|>.meas.aestronglyMeasurable) (ae_of_all _ (fun y=> w y)) (integrable_const _) (ae_of_all _ (fun y s hs=> ((p y).differentiableAt (h.mem_nhds (u hs))).hasDerivAt))).2.congr_of_eventuallyEq ?_
 exact Eventually.mono (h.mem_nhds t) fun _ x' => (q _ x').awakes x
local notation "Q" x=> ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space x))
lemma full_roofs : AnalyticOnNhd ℂ A D:= by
 refine lift_weak (Set.range fun x:H=> ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space x))) (fun x y v=> Rep.fact x y (fun z=>?_)) h ?_ ?_
 · rw [← inner_conj_symm _, ← inner_conj_symm (y z) z, show inner ℂ z (x z)= inner ℂ z (y z) from v _ ⟨z,rfl⟩] -- tune
 · intro z hz; obtain ⟨r,d,u,e⟩:= roofs h F C p b z hz; apply ContinuousAt.continuousWithinAt; refine Metric.tendsto_nhds.mpr (fun ε v'=>?_); let K:= C/r; let k:=max 1 K
   have hk : 0<k:= zero_lt_one.trans_le (le_max_left ..)
   filter_upwards [ball_mem_nhds z (ε:=ε/k) (by positivity),ball_mem_nhds z d] with y y' t
   rw [dist_eq_norm]
   refine (Registers.fare ((q _ (u t)).sub (q z hz)) (q:=k*‖y-z‖) (by positivity) ?_).trans_lt ?_
   · intro x; refine ( (convex_ball z r).norm_image_sub_le_of_norm_deriv_le (f:=fun z=> F z x) (fun i v=> (p x).differentiableAt (h.mem_nhds (u v))) (e x) (mem_ball_self d) t).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
   rw [← dist_eq_norm,mul_comm]; exact (lt_div_iff₀ hk).1 y'
 · rintro w ⟨x,rfl⟩ z t; exact (ciel P h F C A q p b v z t x).differentiableAt.differentiableWithinAt
lemma rooftop_deriv {f:X→ℂ}(z:ℂ)(w:z∈D) (u:∀ x, HasDerivAt (fun z=> F z x) (f x) z) : Registers P f (deriv A z):= by
 have he(x:X): f x=deriv (fun z=> F z x) z:=(u x).deriv.symm
 rw [funext he]; refine ⟨roofs_exact h F C p b v z w,fun x=>?_⟩
 have hs := (full_roofs P h F C A q p b v z w).differentiableAt.hasDerivAt
 let Qx := ((innerSL ℂ (E:=H.space) x).comp (ContinuousLinearMap.apply ℂ H.space x))
 exact ((Qx.hasFDerivAt.comp_hasDerivAt _ hs)).unique (ciel P h F C A q p b v z w x)
end YM.Multiplier
