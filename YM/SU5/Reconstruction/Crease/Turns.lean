import YM.SU5.Reconstruction.Crease.BackLight
/-! # anti in a gaussian clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap OS Semigroup Picket
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)(U:Flash H) (p:∀ t, U.shade (S.E t)= S.E t)
namespace Flash
include p
lemma timeback (t:ℝ): U.shade (trans S (t • basis a))=trans S (-t • basis a):= by
 have u(t:ℝ≥0)(x:H) : U.f (S.E t x)= S.E t (U.f x):= by rw [← U.shade_light, p]
 let f(x y:H)(z:ℂ):=inner ℂ x (S.F z y); have ht(x y:H):AnalyticOnNhd ℂ (f x y) inside:= fun z p=> (((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space y)).analyticAt _).comp (S.localHeat z p)
 have h(x y:H)(z:ℂ)(hz:z∈inside): f x y z=f (U.f y) (U.f x) z:= by
   have he(t:ℝ≥0)(h:0<t): f x y (duration t)=f (U.f y) (U.f x) (duration t):=by
     unfold f; rw [S.roots_heat h,← u, U.light, ← S.sym t, adjoint_inner_left, S.sym t]; -- tune wrong occurrences
   let F' := duration
   refine (ht x y).eqOn_of_preconnected_of_frequently_eq (ht _ _) (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0 |>.isPreconnected) (z₀:=F' 1) (by simp [F',duration,inside]) ?_ hz
   intro e
   have hw:Tendsto F' (𝓝[>] (1:ℝ≥0)) (𝓝[≠] (F' 1)):=by
     apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
     · exact (show Continuous F' from by unfold F' duration; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
     filter_upwards [self_mem_nhdsWithin] with i hi
     intro w; apply (mem_Ioi.mp hi).ne'; apply NNReal.coe_injective; simpa [F',duration] using congrArg Complex.re (show F' i=F' 1 from w)
   obtain ⟨k,v,q⟩:= ((hw.eventually e).and self_mem_nhdsWithin).exists
   exact v (he k (zero_lt_one.trans (mem_Ioi.mp q)))
 let z :ℂ:= duration 1+sideways t; have hz:z∈inside:= (OS.Semigroup.length).mpr zero_lt_one
 have hb:duration 1 + sideways (-t)=star z:= by apply Complex.ext<;> simp [z,duration,sideways]
 rw [trans_time,trans_time]; apply DFunLike.coe_injective; apply (S.whole 1).equalizer (U.shade _).continuous (S.edge (-t)).continuous
 funext x; dsimp only [Function.comp_apply]; rw [shade_at,u,S.high,S.high,hb]; apply ext_inner_right ℂ; intro y


 rw [U.cor,← S.flip_row hz,adjoint_inner_left]
 let h':= h (U.f y) (U.f x) z hz; rw [U.twice,U.twice] at h'; exact h'
end Flash
-- Mink reverses both time & monitored b. keep no hypothesis here.
variable (a b:Axis)
def turn (x:E4) : E4:= WithLp.toLp 2 fun i=> if i=a∨i=b then -x i else x i
lemma turn_at (x:E4)(i:Axis): turn a b x i= if i=a∨i=b then -x i else x i:=rfl
@[simp] lemma turn_add (x y:E4):turn a b (x+y)=turn a b x+turn a b y:=by ext1 i; simp only [PiLp.add_apply,turn_at]; split<;> abel
@[simp] lemma turn_neg (x:E4):turn a b (-x)= -turn a b x:=by ext1 i; simp only [PiLp.neg_apply,turn_at]; split<;> rfl
@[simp] lemma turn_turn(x:E4):turn a b (turn a b x)=x:=by ext1 i;simp only [turn_at]; split<;> simp
@[simp] lemma turn_zero:turn a b 0=0:=by ext1 i;simp [turn_at]
lemma turn_ray (x:ℝ)(i:Axis): turn a b (x • basis i) =(if i=a∨i=b then -x else x) • basis i:=by ext1 j; simp only [turn_at,PiLp.smul_apply]; by_cases h:i=j <;> subst_vars; split<;> simp; all_goals simp [Ne.symm h]
end YM.BridgeClub
