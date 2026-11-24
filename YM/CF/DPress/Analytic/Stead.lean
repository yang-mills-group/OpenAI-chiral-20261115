import Mathlib.Analysis.Complex.MeanValue
/- eq JetDu. purchase via normalized circle measure. Noir pricing technique below tests scalar complex values of the functional; their real-side differentiations already in increment coordinates. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Analytic
open Function Set Filter Metric MeasureTheory Complex Real
open scoped Topology Classical ContDiff InnerProductSpace
abbrev Ω:= Set.Ioc 0 (2*Real.pi)
abbrev ωμ : Measure ℝ:= (ENNReal.ofReal (2*Real.pi)⁻¹) • volume.restrict Ω -- parsing
instance : IsProbabilityMeasure ωμ:=⟨by
 unfold ωμ Ω; rw [Measure.smul_apply,Measure.restrict_apply_univ, Real.volume_Ioc,sub_zero,smul_eq_mul, ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2*Real.pi), ENNReal.inv_mul_cancel]; · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
 exact ENNReal.ofReal_ne_top⟩
abbrev ank (L:ℝ):Set ℂ:=ball 0 L
def φ(R:ℝ)(z:ℝ):ℂ:= circleMap 0 R z
def tor (R:ℝ)(θ:ℝ):ℂ:= (φ R θ-1)⁻¹
@[fun_prop] lemma φ_C (R:ℝ) : Continuous (φ R):= continuous_circleMap 0 R
lemma β(R L:ℝ)(e:R<L)(v:0 ≤ R)(x:ℝ): φ R x∈ank L:= (sphere_subset_ball e) (circleMap_mem_sphere _ v _)
lemma γφ(R:ℝ)(e:1<R)(x:ℝ): R-1 ≤ ‖φ R x-1‖:=by have ht:= norm_circleMap_zero R x; change ‖φ R x‖= |R| at ht; simpa only [ht,abs_of_pos (by linarith : 0<R), norm_one] using (norm_sub_norm_le (φ R x) (1:ℂ))
lemma χ(R:ℝ)(e:1<R)(x:ℝ): φ R x -1 ≠ 0:= norm_ne_zero_iff.mp (lt_of_lt_of_le (sub_pos.mpr e) (γφ R e x)|>.ne') -- precedence check
lemma tor_C(R:ℝ)(h:1<R): Continuous (tor R):= ((φ_C R).sub continuous_const).inv₀ (χ R h)
lemma mft (R:ℝ)(e:1<R)(x:ℝ): ‖tor R x‖≤ (R-1)⁻¹:=by unfold tor; rw [norm_inv]; exact inv_anti₀ (sub_pos.mpr e) (γφ R e x)
-- seq. difference. jet costs.
structure Disc (r:ℝ)(f:ℂ→ℂ)(a:ℂ):Prop where
 χ : ∀ R:ℝ,1<R→R<r→ Integrable (fun x=>tor R x * f (φ R x)) ωμ
 read : ∀ R:ℝ,1<R→R<r→ ∫ x,tor R x * f (φ R x) ∂ ωμ=a
namespace Disc
variable {L R:ℝ}{F G:ℂ→ℂ}{u v:ℂ}
private lemma visQ (H:ℂ→ℂ)(R:ℝ): circleAverage H 0 R=∫ x,H (φ R x)∂ωμ:=by unfold circleAverage ωμ; rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity :0≤ (2*Real.pi)⁻¹), intervalIntegral.integral_of_le (by positivity)]; rfl
private lemma fine (f:ℝ → ℂ)(p:Continuous f): Integrable f ωμ:= (p.intervalIntegrable .. |>.1).smul_measure ENNReal.ofReal_ne_top
lemma ofDiff (p:DifferentiableOn ℂ F (ank L)): Disc L F (F 1-F 0):=by
 let q(R:ℝ)(h:0≤R)(e:R<L):= p.continuousOn.comp (φ_C R).continuousOn (t:=ank L) (s:=univ) (fun x _=> β R L e h _)
 have ht (R:ℝ)(h:1<R)(e:R<L): Integrable (fun x=>tor R x* F (φ R x)) ωμ:= fine _ ((tor_C R h).mul (continuousOn_univ.mp (q R (by linarith) e)))
 refine ⟨ht,fun R h e=>?_⟩; have hR:0<R:= lt_trans zero_lt_one h; have he: DiffContOnCl ℂ F (ank |R|) := by rw [abs_of_pos hR]; refine ⟨p.mono (ball_subset_ball e.le),p.continuousOn.mono ?_⟩; exact (closure_minimal ball_subset_closedBall isClosed_closedBall).trans (closedBall_subset_ball e)
 let K(z:ℂ):= z/(z-1)*F z; have hv:= he.circleAverage_smul_div (c:=(0:ℂ)) (R:=R) (w:=(1:ℂ)) (by simpa [mem_ball,abs_of_pos hR] using h); have hf:circleAverage K 0 R=F 1:=by simpa only [K,sub_zero,smul_eq_mul] using hv
 have h0:= he.circleAverage (c:=0) (R:=R); rw [visQ] at h0 hf; simp_rw [show ∀ x,K (φ R x)=tor R x * F (φ R x)+ F (φ R x) from fun x=> by unfold K tor; field_simp [_root_.id (YM.CF.DPress.Analytic.χ R h x)]; ring] at hf; rw [integral_add (ht R h e) (fine (fun i=> F (φ R i)) (continuousOn_univ.mp (q R hR.le e))),h0] at hf; exact eq_sub_of_add_eq hf -- tune proof args.
lemma value {a:ℝ}(p:Disc L F u)(f:∀ x∈ank L, ‖F x‖≤ a)(v:1<L): ‖u‖ ≤ a/(L-1):=by
 have h : ∀ R:ℝ,1<R→R<L → ‖u‖*(R-1) ≤ a :=by
    intro R h r; rw [←p.read R h r]; apply (le_div_iff₀ (sub_pos.mpr h)).1; exact (norm_integral_le_of_norm_le_const (C:=a/(R-1)) (μ:=ωμ) (ae_of_all _ fun x=> by rw [norm_mul,div_eq_mul_inv,mul_comm a]; exact mul_le_mul (mft R h x) (f _ (β R L r (by linarith) x)) (norm_nonneg _) (inv_pos.mpr (sub_pos.mpr h)).le)).trans_eq (by simp)
 suffices ∀ R∈Icc 1 L, ‖u‖*(R-1)≤ a by exact (le_div_iff₀ (sub_pos.mpr v)).2 (this L ⟨v.le,le_rfl⟩) -- tune `closureIoo`
 rintro R hR; have ht:IsClosed {R:ℝ| ‖u‖*(R-1) ≤ a}:= isClosed_le (continuous_const.mul (continuous_id.sub continuous_const)) (continuous_const (y:=a)); exact closure_minimal (s:=Ioo 1 L) (fun i p=>h i p.1 p.2) ht (closure_Ioo (show (1:ℝ) ≠ L from v.ne) |>.symm ▸ hR)
lemma zero : Disc L 0 0:=by refine ⟨fun _ _ _=> by simp,fun _ _ _=> by simp⟩
lemma plus (p:Disc L F u)(q:Disc L G v): Disc L (fun x=> F x+ G x) (u+v):=by refine ⟨fun R h e=> ?_,fun R h e=>?_⟩; simp_rw [mul_add]; exact (p.χ R h e).add (q.χ R h e); simp_rw [mul_add]; rw [integral_add (p.χ R h e) (q.χ R h e),p.read R h e,q.read R h e]
lemma scale (c:ℂ)(p:Disc L F u): Disc L (fun x=>c*F x) (c*u):=by refine ⟨fun R h e=> ?_,fun R h e=>?_⟩; simp_rw [mul_left_comm (tor R _) c]; exact (p.χ R h e).const_mul c; simp_rw [mul_left_comm (tor R _) c]; rw [integral_const_mul,p.read R h e]
lemma sum {I:Type*}(s:Finset I)(F:I→ℂ→ℂ)(u:I→ℂ)(h:∀ i∈s, Disc L (F i) (u i)) : Disc L (fun x=>∑ i∈s,F i x) (∑ i∈s,u i):=by
 open Finset in
 induction s using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; exact zero
 | insert x s r h'=> simp_rw [sum_insert r]; exact (h x (by simp)).plus (h' fun i p=>h i (mem_insert_of_mem p))
end Disc
end YM.CF.DPress.Analytic
