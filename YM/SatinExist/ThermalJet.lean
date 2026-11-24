import SatinThinJetsPrism

import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j) (Y : ℝ → H)
abbrev VacuumPower {M:Hilbert} (Y:ℝ→M):Prop:= ∃ K> (0:ℝ), ∃ m:ℕ,∀ᶠ e:ℝ in 𝓝[>] 0,‖Y e‖≤ K/e^m
variable {S Y}

private lemma quarter_pay : Tendsto (fun x:ℝ=>x/4) (𝓝[>] 0) (𝓝[>] 0):=by
 refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.mono (p:=fun s:ℝ=> s∈Ioi (0:ℝ)) self_mem_nhdsWithin ( fun x p=> show 0<x/4 from div_pos p (by norm_num))⟩
 have he: Tendsto (fun x:ℝ=>x/4) (𝓝[>] 0) (𝓝 ((0:ℝ)/4)):= ((show Continuous (fun x:ℝ=>x/4) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds
 simpa only [zero_div] using he

lemma VacuumPower.derivs (p:VacuumPower Y) (d:Positive S Y) (n:ℕ): VacuumPower (fun s:ℝ=> jet S Y n s):=by
 obtain ⟨K,g,m,t⟩:=p; let c:ℝ:= n.factorial; have hc:0<c:=by unfold c; positivity
 refine ⟨(c*K* 4^m)*2^n, mul_pos (mul_pos (mul_pos hc g) (by positivity)) (by positivity), m+n,?_⟩
 filter_upwards [self_mem_nhdsWithin,quarter_pay.eventually t] with s u h
 have hp:0 < s:=u; let q:= s/4; let R:= s/2; have hR:0<R:=half_pos hp
 let z:ℂ:=s; have hq:0<q:=by unfold q; linarith
 have he(w:ℂ)(p:w∈Metric.closedBall z R): q<w.re:=by
   rw [mem_closedBall_iff_norm] at p
   have hx:-(R)≤ w.re-z.re:=by have hb:= abs_re_le_norm (w-z); rw [sub_re] at hb; exact (abs_le.mp (hb.trans p)).1
   rw [show z.re = s from rfl] at hx; unfold q; unfold R at hx; linarith only [hp,hx]
 have ht: Metric.closedBall z R⊆ inside:=fun w t=> hq.trans (he w t)
 let F:=lifted S Y
 refine (norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f:=F) (C:=K/q^m) n hR ?_ ?_).trans_eq ?_
 · have d':= (lifted_analytic S Y d).differentiableOn.mono ht
   exact ⟨d'.mono ball_subset_closedBall,d'.continuousOn.mono closure_ball_subset_closedBall⟩
 · intro w p; unfold F; have hy:=he w (sphere_subset_closedBall p)
   rw [lifted_branch S Y d w q hq hy]; apply le_trans _ h
   exact ((S.F _).le_opNorm (Y q)).trans (mul_le_of_le_one_left (norm_nonneg _) (S.norm_row (show 0 < (w-(q:ℂ)).re from sub_pos.mpr hy)))
 unfold q R c; rw [pow_add]; field_simp [hp.ne']
 rw [div_pow,div_pow]; field_simp

lemma VacuumPower.plus (f g:ℝ→ H.space)(p:VacuumPower (M:=H) f)(q:VacuumPower (M:=H) g): VacuumPower (M:=H) (f+g):=by
 obtain ⟨K,hk,k,u⟩:=p; obtain ⟨G,g',m,v⟩:=q
 refine ⟨K+G,add_pos hk g',k+m,?_⟩
 filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one),u,v] with s p v' t z
 have hp:0<s:=p; have hv:s≤1:=v'; refine (norm_add_le (f s) _).trans ((add_le_add t z).trans ?_)
 rw [add_div]; exact add_le_add (div_le_div_of_nonneg_left hk.le (pow_pos hp _) (pow_le_pow_of_le_one hp.le hv (by omega))) (div_le_div_of_nonneg_left g'.le (pow_pos hp _) (pow_le_pow_of_le_one hp.le hv (by omega)))

lemma VacuumPower.line (p:VacuumPower Y) (z:ℂ): VacuumPower (fun i=>z • Y i):=by
 obtain ⟨K,hk,m,t⟩:=p
 refine ⟨(1+‖z‖)*K,mul_pos (by positivity) hk,m,?_⟩
 filter_upwards [t, self_mem_nhdsWithin] with i t k; rw [norm_smul]
 have hp:0 < i:=k; rw [mul_div_assoc]; exact mul_le_mul (le_add_of_nonneg_left zero_le_one) t (norm_nonneg _) (by positivity)

lemma VacuumPower.ticket (p:VacuumPower Y) (d:Positive S Y) (f:Prism): VacuumPower (prism S Y f):=by
 suffices h:∀ t:Finset ℕ, VacuumPower (fun i:ℝ=>∑ j∈t, f j • jet S Y (j+1) i) by exact h f.support
 intro t; induction t using Finset.induction_on with
 | empty=>
   simp only [Finset.sum_empty]; exact ⟨1,zero_lt_one,0,Eventually.of_forall fun x=> by simp⟩
 | insert a b g ih=> simp only [Finset.sum_insert g]; exact (p.derivs d (a+1)|>.line (f a)).plus _ _ ih
end YM.SatinJets
