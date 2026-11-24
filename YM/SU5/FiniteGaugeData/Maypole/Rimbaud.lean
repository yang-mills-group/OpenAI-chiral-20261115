import YM.SU5.FiniteGaugeData.Celeritas.Sledge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
/-! # WP25: attempting elimination of spectral expense from RotReal alone (+ stamp/restore). Tools. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Vp
open Function Set MeasureTheory OS OS.Semigroup Complex Filter NormedSpace Metric Bornology
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {X:Type*}{u r t C:ℝ}{f:ℂ→ℂ}{n k i j:ℕ}
namespace Rimbaud
-- compressed HO price
local notation "D"=> 𝓝 (0:ℂ)
local notation "W"=> 𝓝 (0:ℝ)
local notation "D₁"=> 𝓝[>] (0:ℝ)
local notation "D₂"=> 𝓝[<] (0:ℝ)
lemma lensW : Tendsto ((↑):ℝ→ℂ) (𝓝[>] (0:ℝ)) (𝓝 0):= by exact continuous_ofReal.continuousAt.continuousWithinAt
lemma lensV : Tendsto ((↑):ℝ→ℂ) (𝓝[<] (0:ℝ)) (𝓝 0):= by exact continuous_ofReal.continuousAt.continuousWithinAt
-- case leading exponent: positivity on pos and negative rays means even.
lemma places(g:ℂ→ℂ)(u:g 0≠0)(h:AnalyticAt ℂ g 0) (t:∀ᶠ z:ℂ in 𝓝 0,f z=z^i*g z) (z:∀ᶠ x:ℝ in 𝓝 0, 0≤ f x) : Even i:=by
 by_contra hp; have e:Odd i:=Nat.not_even_iff_odd.mp hp
 have gt(x y:ℂ)(p:0<x)(q:0≤ x*y): 0≤y:= le_of_mul_le_mul_left (by rwa [mul_zero]) p -- complex partial
 have he: 0≤ g 0:=by
    refine ge_of_tendsto (h.continuousAt.tendsto.comp lensW) ?_; filter_upwards [lensW.eventually t,z.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x t qp iS; rw [t] at qp; exact gt _ _ (by exact_mod_cast (pow_pos (show (0:ℝ)<x from iS) i )) qp
 have hv:g 0≤0:=by
    refine le_of_tendsto (h.continuousAt.tendsto.comp lensV) ?_; filter_upwards [lensV.eventually t,z.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x t qp iS; rw [t] at qp; have hz:0< -((x:ℂ)^i):= neg_pos.mpr (by exact_mod_cast (e.pow_neg (show x<0 from iS))); have hx:= gt (-((x:ℂ)^i)) (-g x) hz (by rw [neg_mul_neg]; exact qp); exact neg_nonneg.mp hx
 exact u (le_antisymm hv he)
lemma smallLeft {g:ℂ→ℂ}(h0:i≤n)(v:Tendsto (fun s:ℝ=> f (s:ℂ) / (s:ℂ)^n) (𝓝[>] 0) (𝓝 0))(t:∀ᶠ z:ℂ in 𝓝 0, f z=z^i*g z) (p:AnalyticAt ℂ g 0): g 0=0:=by
 apply tendsto_nhds_unique (p.continuousAt.tendsto.comp lensW); obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le h0; rw [hk] at v; let g'(s:ℝ):= (s:ℂ)^k; have he:Tendsto g' D₁ (𝓝 (0^k)):= lensW.pow k; have hx:=v.mul he; rw [zero_mul] at hx; refine hx.congr' ?_; filter_upwards [lensW.eventually t,self_mem_nhdsWithin] with s p w; unfold Function.comp g'; rw [p,pow_add]; have ht:s>0:=w; field_simp -- tune
lemma upward (p:AnalyticAt ℂ f 0)(e:∀ᶠ x:ℝ in 𝓝 0,0≤ f x)(u:Tendsto (fun s:ℝ=> f (s:ℂ)/(s:ℂ)^(2*n)) D₁ (𝓝 0)) : ↑(2*n+2:ℕ) ≤ analyticOrderAt f 0 :=by
 generalize h: analyticOrderAt f 0=k; cases k with
 | top=>exact le_top
 | coe i=> obtain ⟨g,v,z,t⟩:= p.analyticOrderAt_eq_natCast.mp h; simp only [sub_zero,smul_eq_mul] at t; have hh:= Nat.lt_of_not_ge (show ¬ (i:ℕ) ≤ 2*n from fun h=> z (smallLeft h u t v)); obtain ⟨a,w⟩:=places g z v t e; exact_mod_cast (by omega :2*n+2 ≤ i) -- tune
open scoped Classical
lemma dimm(p:0<t)(h:AnalyticOnNhd ℂ f (closedBall 0 t))(q:∀ x∈ closedBall 0 t, ‖f x‖≤ C)(e: (n:ℕ∞) ≤ analyticOrderAt f 0):∀ x∈closedBall 0 t, ‖f x‖ ≤ C*(‖x‖/t)^n:=by
 obtain ⟨g,v,tg⟩:= (natCast_le_analyticOrderAt (h 0 (mem_closedBall_self p.le))).1 e; simp only [sub_zero,smul_eq_mul] at tg
 let G(x:ℂ):= if x=0 then g x else f x/x^n
 have he:∀ x,f x=x^n*G x:=by
    intro x; by_cases h:x=0; · unfold G; rw [if_pos h,h]; exact tg.self_of_nhds
    unfold G; rw [if_neg h]; field_simp
 have ht: AnalyticOnNhd ℂ G (closedBall 0 t) :=by
    intro x t; by_cases p:x=0; · subst x; exact v.congr (tg.mono fun x t=> by unfold G; split; rfl; rename_i hh; rw [t]; field_simp) -- orientation?
    apply AnalyticAt.congr ((h x t).div (analyticAt_id.pow n) (show x^n≠0 from pow_ne_zero _ p)); filter_upwards [eventually_ne_nhds p] with x hx; exact (if_neg hx).symm
 let U:= ball (0:ℂ) t; have hw:closure U=closedBall 0 t:= closure_ball _ p.ne'; intro x hx; have e:‖G x‖≤ C/(t^n):=by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U:=U) isBounded_ball (DifferentiableOn.diffContOnCl (s:=U) ?_) (fun y yv=>?_) (hw.symm ▸ hx)
    · rw [hw]; exact AnalyticOnNhd.differentiableOn ht
    unfold U at yv; rw [frontier_ball _ p.ne',mem_sphere, dist_zero_right] at yv
    have hq:= q y (mem_closedBall.mpr ((dist_zero_right _).trans_le yv.le)); rw [he y,norm_mul,norm_pow,yv] at hq; rw [le_div_iff₀ (pow_pos p n),mul_comm]; exact hq
 rw [he x,norm_mul,norm_pow]; exact (mul_le_mul_of_nonneg_left e (by positivity)).trans_eq (by rw [div_pow]; ring)
end Rimbaud
end YM.CF.Buffered.Afterglow.Hierarchy.Vp
