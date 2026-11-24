import SatinThinSeven
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SatinJets
open Function Filter NormedSpace InnerProductSpace Finset Set MeasureTheory
open scoped Topology BigOperators Matrix ComplexOrder InnerProductSpace Classical
variable (L:Hilbert)
/-! # Stable founding of the seven modes. Only test one branch at these required precision rates. -/
abbrev marginD (A b p:ℝ): Prop:= ∀ i j:Seven,bill7 i j*(2*b*A+b^2) ≤ p /4
lemma common_margin (A p:ℝ)(h:0<p): ∃ b:ℝ,0<b ∧ b<1 ∧ marginD A b p:=by
 have he:∀ᶠ b:ℝ in 𝓝 0, marginD A b p:= by
    apply Filter.eventually_all.mpr; intro i; apply Filter.eventually_all.mpr; intro j; let f(b:ℝ):= bill7 i j*(2*b*A+b^2); have hp: Tendsto f (𝓝 0) (𝓝 0):= (by nth_rw 2 [show 𝓝 (0:ℝ)= 𝓝 (f 0) from congrArg nhds (by unfold f; ring)]; exact (show Continuous f from (by unfold f; fun_prop)).continuousAt) -- rw [show] changes both
    exact hp.eventually (ge_mem_nhds (by linarith : 0<p/4))
 let s:= nhdsWithin (0:ℝ) (Set.Ioi 0); haveI : s.NeBot := inferInstanceAs (nhdsWithin (0:ℝ) (Ioi 0)).NeBot; exact ((show ∀ᶠ t:ℝ in s, 0 < t from self_mem_nhdsWithin).and ((show ∀ᶠ t:ℝ in s, t < 1 from ((show ∀ᶠ t:ℝ in 𝓝 0,t<1 from gt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds).and (he.filter_mono nhdsWithin_le_nhds))).exists
lemma growth_draft (f:L.Op)(h:‖f‖ ≤1)(x:L): ‖f x‖≤ ‖x‖:= (f.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) h)
private lemma local_cost (v u:L.Op) (x y:L) (e:‖u‖≤1)(p:‖v‖≤1)(G:L.Op)(q:∀ z:L,‖G z‖=‖z‖) {b A:ℝ} (ha:0≤b)(z:‖x‖≤ A)(r:dist y x≤b): ‖inner ℂ (G (u x)) (v x)-inner ℂ (G (u y)) (v y)‖ ≤(2*b*A+b^2):=by
 let w:= y-x; let X:= G (u x); let U:=G (u w); have he:‖w‖ ≤ b:= by rwa [dist_eq_norm] at r
 have hx:‖X‖≤ A:= (q ..).trans_le ((growth_draft L u e x).trans z); have hv: ‖U‖≤ b:= (q ..).trans_le ((growth_draft L u e w).trans he); have hu:‖v x‖≤A:= (growth_draft L v p x).trans z; have hr:‖v w‖ ≤ b:= (growth_draft L v p w).trans he
 rw [show inner ℂ (G (u y)) (v y)=inner ℂ X (v x) + (inner ℂ (X+U) (v w)+inner ℂ U (v x)) from ?_]; swap; · rw (occs:=.pos [1,2]) [show y=x+w from (by unfold w; abel)]; simp only [map_add,inner_add_right,inner_add_left]; unfold X U; abel
 rw [show G (u x)= X from rfl,show ∀ a b:ℂ, a-(a+b)= -b from fun _ _=> by ring,norm_neg] -- lemma? 
 have hU: ‖X+U‖≤ A+b:= (norm_add_le ..).trans (add_le_add hx hv); refine le_trans ((norm_add_le ..).trans (add_le_add (norm_inner_le_norm ..) (norm_inner_le_norm ..))) ?_
 nlinarith only [mul_le_mul hU hr (norm_nonneg _) ((norm_nonneg _).trans hU),mul_le_mul hv hu (norm_nonneg _) ha]
lemma stable_plan (T:Seven → L.Op)(G:L.Op)(q:∀ v:L, ‖G v‖=‖v‖)(h:∀ i,‖T i‖≤1){b p A c:ℝ}(z:0≤ b) (x y:L)(hx: ‖x‖≤ A)(F:tempo (fun i=> T i x) (fun i=>G (T i x)) c (p/4)) (v:p≤ c) (g:0<p)(w:marginD A b p)(r:dist y x ≤ b) : LinearIndependent ℂ (fun i:Seven=> T i y):=by
 refine tempos_price (fun i=>T i y) (fun i=>G (T i y)) c (lt_of_lt_of_le g v) ?_ -- tactic implicit
 intro i j; let U: L→ ℂ:=fun i0=>(bill7 i j:ℂ)*inner ℂ (G (T i i0)) ((T j) i0); have ht :‖U x-c‖≤ p/4:= F i j; have he:‖U x-U y‖≤ p/4:=by
    unfold U; rw [← mul_sub,norm_mul, Complex.norm_real,Real.norm_of_nonneg (bill_p i j).le]; exact (mul_le_mul_of_nonneg_left (local_cost L (T j) (T i) x y (h i) (h j) G q z hx r) (bill_p ..|>.le)).trans (w i j)
 change ‖U y-(c:ℂ)‖ ≤_; rw [← dist_eq_norm] at *; have hv:= dist_triangle_left (U y) (U x) (c:ℂ) -- tune argument
 rw [dist_comm (U x)] at he; linarith only [ht,he,v,dist_triangle (U y) (U x) (c:ℂ)]
end YM.SatinJets
#print axioms YM.SatinJets.stable_plan
