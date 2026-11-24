import GaugeFieldConstruction.Sardana
import GaugeFieldConstruction.Eases
set_option autoImplicit false
set_option maxRecDepth 3100
set_option maxHeartbeats 90000
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators HopeC Finset CF.Crest CF.Vale.Veins
open Maxwell Analysis Lattice
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
open GaugeFieldConstruction GaugeFieldConstruction.Cauchy CF.Fock.Flux
open Gap GaugeFieldConstruction.Wick.Yacht Classical
attribute [local instance] propDecidable
variable (x:ℕ→ Lattice.Cover){f:ℕ→ℝ}{a:E4}(h:Tendsto f atTop (𝓝 0))(u:∀ᶠ i:ℕ in atTop,0<f i)
-- `X` measured in matter-lattice units; pp tends in gauge displacement (phase convention down leg).
variable (e:a≠0)(p:Tendsto (fun i:ℕ=> f i • ((2:ℝ) • off (x i))) atTop (𝓝 a))
include e p u h
abbrev ferryNX:= pairs SpecW SpecW
lemma gliderRomNX (l j:Cauchy.Spin): Tendsto (fun i:ℕ=> RomT (x i) l j /(f i:ℂ)^3) atTop (𝓝 ((Gap.eye a) (Wick.blend l j))):=by
 let S:= ferryNX
 let B:=Wick.blend l j
 have hz: off 0=0:=by ext i; simp [off]
 let g(z:E4 × E4)(y:E4):= -(0+z.1)+(y+z.2)
 let fn(i:ℕ)(z:E4×E4):E4:=f i • ((2:ℝ) • g z (off (x i)))
 have hk(i):menagerie 0 (x i)=HopeC.lift S (fun z=>g z (off (x i))) (by unfold g; fun_prop):=by
    unfold menagerie localeΨ; rw [hz,parallel,parallel]; apply commuted
 let Y(y:E4)(t:ℝ)(z:E4×E4):=y+t • ((2:ℝ) •(z.2-z.1)); have hynn(i z):Y (f i • ((2:ℝ) • off (x i))) (f i) z=fn i z:=by unfold fn Y g; module
 have hu(z):Continuous (fn z):= by unfold fn g; fun_prop
 have hτ(O:Set E4)(q:O∈𝓝 a):∀ᶠ i:ℕ in atTop,∀ z∈ S.site,fn i z∈O:=by
    let T:=(fun p: E4×ℝ=> fun z:E4×E4=> Y p.1 p.2 z)
    have hY(z:E4 × E4):ContinuousAt (Function.uncurry T) ((a,0),z):=by apply Continuous.continuousAt; change Continuous (fun p:(E4×ℝ)×E4×E4=> Y p.1.1 p.1.2 p.2); unfold Y; fun_prop
    have hV:∀ᶠ i:E4×ℝ in 𝓝 (a,0),∀ z∈S.site,T i z∈O:=by
      -- compact tube lemma
      have H(z:E4×E4): (fun p:(E4×ℝ)×E4×E4=> T p.1 p.2)⁻¹' O ∈ 𝓝 ((a,0),z):= (hY z) (by change O∈𝓝 (Y a 0 z); simpa only[Y,zero_smul,add_zero] using q) -- tune
      -- mathlib generalized.
      exact S.k.eventually_forall_of_forall_eventually fun z _=> H z
    filter_upwards [(p.prodMk_nhds h).eventually hV] with i w z u; rw [← hynn]; exact w z u
 have hr:∀ᶠ i:ℕ in atTop,∀ z∈S.site,fn i z≠0:=by
    exact hτ ({0}ᶜ:Set E4) (compl_singleton_mem_nhds e)
 let F(i:ℕ)(x:E4×E4):ℂ:= eye (fn i x) B
 have hc(i)(p:∀ z∈S.site,fn i z≠0):Integrable (F i) S.μ:= span_v S (F i) (fun z h=> ((healthy B (p z h)).continuousAt.comp (hu i).continuousAt).continuousWithinAt)
 have hΦ:∀ᶠ i:ℕ in atTop,RomT (x i) l j / (f i:ℂ)^3=(∫ z:E4 × E4, F i z∂S.μ):=by
   filter_upwards [u,hr] with i p he
   have hZ (z:E4)(v:z∈(menagerie 0 (x i)).site) : z≠0:=by
      rw[hk] at v -- invalid binder lambda
      obtain ⟨b,w,rfl⟩:=v; exact fun x=> he b w (by unfold fn; beta_reduce at x; rw[x, smul_zero,smul_zero])
   rw[show RomT (x i) l j= _ from ((congrArg (fun x=>RomT x l j) (sub_zero (x i)).symm).trans (Marne 0 (x i) l j (fun p=>hZ 0 p rfl)))] -- tune
   rw [hk, rolled]
   swap
   · intro z v
     refine ((healthy B (x:= (2:ℝ) • z) (smul_ne_zero (by norm_num) (hZ z ?_))).continuousAt.comp (f:=fun x:E4=> (2:ℝ)•x) (Continuous.continuousAt (by fun_prop))).continuousWithinAt
     rw [hk]; exact v
   rw[div_eq_iff (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr p.ne')),mul_comm,← integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun z=>?_
   let u:= (2:ℝ) • g z (off (x i))
   change Gap.eye u B= (f i:ℂ)^3*Gap.eye (f i • u) B
   -- homogeneity p: (t)^3 * eye (t*z) p = eye z p !!!! issue formula RomT x = integral over raw `u` so on RHS f^3 term. good.
   exact (Foulard p l j u).symm
 refine Filter.Tendsto.congr' (f₁:=fun i:ℕ=>∫ z:E4×E4,F i z ∂S.μ) (hΦ.mono fun i u=> u.symm) ?_ -- tune order
 rw [Metric.tendsto_nhds]
 intro A H
 let d:=A/2; have hd:0<d:= by unfold d; positivity
 let L(a:E4):= Gap.eye a B
 have t: ContinuousAt L a:= (healthy B e).continuousAt
 filter_upwards [hr, hτ _ (t (Metric.ball_mem_nhds _ hd))] with i hi y
 rw [dist_eq_norm]; change ‖(∫ z,F i z∂S.μ)-L a‖< _
 have ht: ‖(∫ z,F i z∂S.μ)-L a‖ ≤ ∫ _:E4×E4,d ∂S.μ:=by
    have hB: ∀ᵐ z ∂S.μ,‖F i z-L a‖≤ d := S.onA.mono fun z h=>le_of_lt (by rw [←dist_eq_norm]; exact Metric.mem_ball.mp (y z h))
    have hk:= norm_integral_le_of_norm_le (f:=fun z:E4×E4=>F i z-L a) (g:=fun _:E4×E4=>d) (integrable_const _) hB
    rw[integral_sub (hc i hi) (integrable_const _)] at hk; simpa only [integral_const, probReal_univ,one_smul] using hk -- tune
 simpa using ht.trans_lt (by simp; unfold d; linarith)
#print axioms gliderRomNX
end YM.StressFHeat
end
