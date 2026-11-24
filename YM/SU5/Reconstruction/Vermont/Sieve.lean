import YM.SU5.Reconstruction.Vermont.Walnut
import YM.SU5.Reconstruction.Vermont.Seam
/-!
# Real-window payments from Wick's continued script. Support fixed; parameters simultaneous.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens.River
open Function Set Filter Spectral Analysis Metric OS.Semigroup ConePrice Sail MeasureTheory Complex CF.Floral
open scoped BigOperators Topology Interval InnerProductSpace
variable {a b c d w:ℝ}{f:ℂ→ℂ}
local notation "H"=> inside
local notation "j" u:max=> ((u:ℝ):ℂ)
local notation "Q"=> Ι 0 a
lemma lost (u:AnalyticOnNhd ℂ f inside)(p:a<b)(v:∀ x∈H,x.im∈ Ioo a b→‖f x‖≤ c*x.re):f 1=0:= by
 let U:= {x:ℂ| x.im∈ Ioo a b}; let P:= {x:ℂ|x.re<0}; obtain ⟨t,tA,tB⟩:= exists_between p; let z₁:ℂ:=⟨-1,t⟩; let z₂:ℂ:=⟨1,t⟩; have a1:z₁ ∈ U:= ⟨tA,tB⟩; have a2:z₂ ∈ U:= ⟨tA,tB⟩
 have hP:IsOpen P:= isOpen_lt continuous_re continuous_const; have hU:IsOpen U:= isOpen_Ioo.preimage continuous_im; have k1:z₁∈ P:= show (-1:ℝ)<0 by norm_num
 have k2:z₂∈H:=show (0:ℝ)<1 by norm_num
 let g(z:ℂ):= if 0< z.re then f z else 0
 have e1 : ∀ x∈P,g =ᶠ[𝓝 x] 0:= fun x v=> (show ∀ᶠ i in 𝓝 x,i∈ P from hP.mem_nhds v).mono fun i v=> if_neg (not_lt.mpr (show i.re<0 from v).le)
 have e2 : ∀ x∈H,g =ᶠ[𝓝 x] f:= fun x v=> (show ∀ᶠ i in 𝓝 x,i∈ H from open_inside.mem_nhds v).mono fun i h=> if_pos (show 0< i.re from h)
 have hc : ContinuousOn g U:= by
   intro x b'; rcases lt_trichotomy x.re 0 with v0|v0|v0
   · exact ((continuousAt_const (y:=(0:ℂ))).congr (e1 x v0).symm).continuousWithinAt -- orientation
   · have hz:g x=0:=if_neg (not_lt.mpr v0.le); apply Metric.tendsto_nhds.mpr; intro ε p; filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((isOpen_lt ((continuous_re).const_mul c) continuous_const).mem_nhds (show c*x.re< ε from (by rw [v0,mul_zero]; exact p)))] with y bY k0; rw [hz,dist_zero_right]; unfold g; split; rename_i e; exact lt_of_le_of_lt (v y e bY) (show c*y.re < ε from k0); simpa using p
   exact (((u x v0).continuousAt).congr (e2 x v0).symm).continuousWithinAt
 have ha:AnalyticOnNhd ℂ g U:= by
    apply DifferentiableOn.analyticOnNhd _ hU; apply seam_cement (t:=0) _ hc hU; intro z q r; rcases lt_or_gt_of_ne r with p|p
    · exact DifferentiableAt.congr_of_eventuallyEq (differentiableAt_const _) (e1 z p)
    exact (u z p).differentiableAt.congr_of_eventuallyEq (e2 z p)
 have h0:EqOn g 0 U:= ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero ((show Convex ℝ U from (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear a).inter (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear b)).isPreconnected) a1 (e1 z₁ k1)
 apply u.eqOn_zero_of_preconnected_of_eventuallyEq_zero ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected) k2 ((e2 z₂ k2).symm.trans ((show ∀ᶠ i in 𝓝 z₂,i∈ U from hU.mem_nhds a2).mono fun x k=>h0 k)) (show (1:ℂ)∈ H from (by change (0:ℝ)<1; norm_num))

variable (c0:0≤c) (f':ℕ→ℂ→ℂ) (U:∀ n x,0≤(x:ℂ).re→‖f' n x‖≤ c)(V:∀ n,Hol H (f' n))(D:∀ n,Continuous (f' n))
omit f'
-- tune include automatically used
include c0
private lemma wiggle (F:Continuous f) (p:0<a)(v:∀ x:ℂ,0≤ x.re→‖f x‖≤ c)(e:Hol H f) : ‖flux f a 1 - a • f 1‖ ≤ (c / (1/3) * a) * a:= by
 rw [flux,show a • f 1=(∫ t:ℝ in 0..a, f 1) from (by simp), ← intervalIntegral.integral_sub (f:=fun t:ℝ=> f (1+(t:ℂ)*I)) ((F.comp (show Continuous (fun t:ℝ=>1+(t:ℂ)*I) from by fun_prop)).intervalIntegrable _ _) intervalIntegrable_const]
 apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=c/(1/3)*a) ?_).trans_eq (congrArg (c/(1/3)*a *·) ((abs_of_pos (sub_pos.mpr p)).trans (sub_zero _)))
 intro x h; have g: 0<x ∧ x≤a:= (show x∈ Ioc 0 a from ((uIoc_of_le p.le) ▸ h)); exact (costs_vertical v e x).trans (mul_le_mul_of_nonneg_left ((abs_of_pos g.1).symm ▸ g.2) (by positivity)) -- include c0
local notation "F"=> f'
include c0 f' U V D
private lemma absence (h:∀ x∈ Ioo d b,Tendsto (fun i=>F i (x*I)) atTop (𝓝 0))(e : d+a < b)(p:0<a) : ∃ f:ℂ→ℂ, f 1=0 ∧ Tendsto (fun i=> flux (F i) a 1) ((Ultrafilter.of (atTop:Filter ℕ)) : Filter ℕ) (𝓝 (f 1)):= by
 let G(i:ℕ):= flux (F i) a
 obtain ⟨f,hf,b0⟩:=limit_chance G open_inside (fun i=> polish (U i) (V i) (D i) a) (fun i z t=> balance p (U i) z t); refine ⟨f,?_,b0 _ (show (1:ℂ)∈ H from show (0:ℝ)<1 from zero_lt_one)⟩ -- notation!
 have h0 (x:ℝ)(b': d<x)(g:x<b-a): Tendsto (fun i=> G i (x*I)) atTop (𝓝 0):= by
   let HF(i:ℕ)(t:ℝ):= F i ((x:ℂ)*I+t*I); have he: Tendsto (fun i=>∫ t:ℝ in 0..a, HF i t) atTop (𝓝 (∫ _:ℝ in 0..a,(0:ℂ))) := by
     refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>c) (Eventually.of_forall (fun i=>((D i).comp (show Continuous (fun t:ℝ=>(x:ℂ)*I+t*I) from by fun_prop)).aestronglyMeasurable)) (Eventually.of_forall fun i=> ae_of_all _ (fun u _=> U i _ (show 0≤ ((x:ℂ)*I+u*I).re from (by simp)))) intervalIntegrable_const ?_
     apply ae_of_all; intro t g'; have hm: 0<t ∧ t≤a:= (show t∈ Ioc 0 a from (uIoc_of_le p.le) ▸ g')
     simp_rw [HF,← add_mul,← Complex.ofReal_add]; exact h _ (show x+t∈ Ioo d b from ⟨by linarith [hm.1],by linarith [hm.2]⟩)
   simpa only [intervalIntegral.integral_zero,G,flux,HF] using he -- defeq powers
 apply lost hf (show d<b-a by linarith) (c:=c+c); intro z e k
 have hc : ∀ i, ‖G i z - G i ((j z.im)*I)‖ ≤ (c+c)*z.re:= fun i=> (beaches p (U i) (V i) (D i) z e).trans_eq (add_mul ..).symm
 simpa only [sub_zero] using le_of_tendsto' (((b0 z e).sub ((h0 z.im k.1 k.2).mono_left (Ultrafilter.of_le atTop))).norm) hc

lemma signal (h:a<b) (p0:0<c)(e:0<d)(φ:∀ᶠ n in atTop,d≤‖f' n 1‖): ∃ t∈ Ioo a b,∃ ε>0, ∃ᶠ i in atTop, ε≤ ‖F i (t*I)‖:=by
 by_contra v; have hi(x)(e':x∈Ioo a b): Tendsto (fun i=> F i ((j x)*I)) atTop (𝓝 0):= by
    apply Metric.tendsto_nhds.mpr; intro ε p; have hs := not_frequently.mp (show ¬∃ᶠ i in atTop, ε≤‖F i ((j x)*I)‖ from fun f=> v ⟨x,e',ε,p,f⟩); exact hs.mono fun i h=> (dist_zero_right (F i ((j x)*I))).symm ▸ (lt_of_not_ge h)
 let C:= c/(1/3); obtain ⟨u,hu,g⟩:= exists_between (show 0<min (b-a) (d/C) from lt_min (sub_pos.mpr h) (div_pos e (by unfold C; positivity)))
 have hx:= lt_min_iff.mp g
 obtain ⟨f,f0,T⟩:= absence c0 F U V D hi (show a+u<b from by linarith [hx.1]) hu
 have hC : C*u < d:= by unfold C; nlinarith [(lt_div_iff₀ (show 0<C by unfold C; positivity)).mp hx.2,
      (show c/(1/3)=C from rfl)] -- solve comm tune
 let A:=d-C*u; have hz:0<A*u:= mul_pos (sub_pos.mpr hC) hu
 apply (not_le.mpr hz); rw [f0] at T; suffices he: A*u≤ ‖(0:ℂ)‖ by simpa only [norm_zero] using he
 apply ge_of_tendsto T.norm; filter_upwards [φ.filter_mono (Ultrafilter.of_le atTop)] with i t
 have hA:= wiggle c0 (D i) hu (U i) (V i)
 have he := norm_sub_norm_le (u • F i 1) (flux (F i) u 1); rw [norm_sub_rev,norm_smul, Real.norm_eq_abs, abs_of_pos hu] at he
 change A*u ≤ ‖flux (F i) u 1‖; unfold A C; nlinarith
end YM.Lens.River
