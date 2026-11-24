import YM.SU5.FiniteGaugeData.ArchiveK.Bourne
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] lint_prob
open MeasureTheory.Measure
/- Horizon time-normal separation. Fubini-S reel. -/
section
variable (G:E4 ≃ₗᵢ[ℝ] E4) {p:Space3}(t:p≠0)
set_option quotPrecheck false
local notation "V"=> seedX G p
local notation "U" u:max => upright G (p,u)
local notation "T"=> sailX G
local notation "E"=> ‖p‖
def pulseG (p:Space3): Momentum:= brushQ (seedX G p)+ (Complex.I*‖p‖) • brushQ (sailX G)
abbrev depthG(x:E4):= inner ℝ (sailX G) x
abbrev crestG(p:Space3)(x:E4):= inner ℝ (seedX G p) x
lemma iron_q (p:Space3)(x:E4) : rise (pulseG G p) x= coastE (crestG G p x) * ↑(Real.exp (-‖p‖*depthG G x)) := by
 unfold crestG depthG pulseG rise coastE; rw [pis,pis]; push_cast; simp only [Pi.add_apply,Pi.smul_apply,brushQ,Fir.tmap,smul_eq_mul]; rw [← Complex.exp_add]; simp_rw [add_mul, Finset.sum_add_distrib, mul_add]; simp only [mul_assoc,← Finset.mul_sum]; ring_nf; simp [sub_eq_add_neg]
lemma loftB (p:Space3)(x:E4) : ‖rise (pulseG G p) x‖= Real.exp (-‖p‖*depthG G x) := by rw [iron_q,norm_mul,coast_pay,one_mul]; exact Complex.norm_of_nonneg (Real.exp_pos _).le -- tune
lemma bump : ‖leer (pulseG G p)^8‖≤ Real.exp (20*E):=by
 rw [←marrow]; refine (norm_integral_le_of_norm_le (integrable_const (Real.exp (20*E))) ?_).trans_eq ?_ -- tune
 · filter_upwards [lint_cost] with x hx; rw [loftB]; apply Real.exp_monotone; unfold depthG; have he:= abs_real_inner_le_norm T (foamQ x); rw [sail_size,one_mul] at he; rw [neg_mul,← mul_neg]; nlinarith only [mul_le_mul_of_nonneg_left ( (neg_le_abs (inner ℝ (sailX G) (foamQ x))).trans (he.trans hx)) (norm_nonneg p)] -- type
 simp
lemma upC : Continuous (fun u:ℝ=> upright G (p,u)) := by change Continuous (fun u:ℝ=> G (rectX (WithLp.toLp 2 (p,u)))); fun_prop
include t
-- moment real time function
abbrev kite (v:ℝ)(u:ℝ):= coastE (v*u)*amiX (upright G (p,u)) * (whey E u:ℂ) -- p implicit binding inferred from G? explicit below
lemma kite_I (v:ℝ): Integrable (kite G (p:=p) v):= by
 let U':= kite G (p:=p) v; have ht(u:ℝ): ‖U' u‖=2*rockF G p u 0:=by
    unfold U' kite rockF; rw [norm_mul,norm_mul,coast_pay,one_mul,Complex.norm_real,Real.norm_of_nonneg (show 0≤whey E u by unfold whey; positivity)]; unfold whey; ring
 refine ((side_full G p t 0 (by omega)).const_mul 2).mono' (by unfold kite; exact (show Continuous (kite G (p:=p) v) from Continuous.mul ((show Continuous (fun u:ℝ=>coastE (v*u)) by fun_prop).mul (ami_safe.comp (upC G (p:=p)))) (Complex.continuous_ofReal.comp (whey_C (norm_pos_iff.mpr t)))).aestronglyMeasurable) (Eventually.of_forall (fun u=> (ht u).le)) -- unfold glitch
lemma releaseG (v:ℝ) (p0:20<v): ∫ u, kite G (p:=p) v u=((τ/E:ℝ):ℂ)*weave E v * leer (pulseG G p)^8:=by
 let B(x:Brio):= V; let S(x:Brio):= foamQ x; have hv:= norm_pos_iff.mpr t; let f (u : ℝ) (x:Brio):= (coastE (v*u) * coastE (inner ℝ (upright G (p,u)) (foamQ x)))*(whey E u:ℂ)
 have he(u:ℝ): kite G (p:=p) v u=∫ x:Brio,f u x ∂lintZ:=by
    unfold kite f amiX; rw [integral_mul_const,integral_const_mul,←marrow]; apply congrArg (fun z'=> coastE (v*u)*z'*(whey E u:ℂ)); refine integral_congr_ae (ae_of_all _ fun x=>?_); exact rise_real .. 
 let N:=MeasureTheory.volume (α:=ℝ); let K:= N.prod lintZ; have hx:Integrable (uncurry f) K:= by
    refine Integrable.mono' (g:=fun x=>whey E x.1) ?_ ?_ ?_
    · convert (whey_I hv).mul_prod (integrable_const (μ:=lintZ) (1:ℝ)) using 1; rw [funext (show ∀ (x:ℝ × Brio), whey E x.1*(fun _=> (1:ℝ)) x.2=whey E x.1 from fun x=> mul_one _)] -- tune
    · apply (show Continuous (uncurry f) from ?_).aestronglyMeasurable; unfold uncurry f; apply Continuous.mul; apply Continuous.mul; fun_prop; exact contCoastE.comp (((upC G (p:=p)).comp continuous_fst).inner (foam_cont.comp continuous_snd)); exact (Complex.continuous_ofReal.comp (whey_C hv)).comp continuous_fst
    filter_upwards with x; obtain ⟨z,x⟩:=x; unfold uncurry f; simp only [norm_mul,coast_pay,one_mul,mul_one,norm_real]; rw [Real.norm_of_nonneg (show 0≤whey E z by unfold whey; positivity)]
 simp_rw [he,← marrow]; rw [integral_integral_swap hx,←integral_const_mul]; refine integral_congr_ae ?_; filter_upwards [lint_cost] with x hx
 let y:=foamQ x; let b:=depthG G y; let c:=crestG G p y; have h(v':ℝ): f v' x= coastE c * (coastE ((v+b)*v') * (whey E v':ℂ)):=by
    unfold f; rw [line_G]; change (coastE (v*v')*coastE (inner ℝ (V + v' • T) y))*_= _; rw [inner_add_left,real_inner_smul_left,←coast_add, ←mul_assoc,←coast_add]; unfold c b crestG depthG; ring_nf
 simp_rw [h, integral_const_mul]; unfold N; rw [whet hv (v+b)]; have hQ:0<v+b:=by
    have ht:= abs_real_inner_le_norm T y; rw [sail_size,one_mul] at ht; have hz: |b|≤20:= ht.trans hx; linarith only [(abs_le.mp hz).1,p0]
 rw [iron_q]; unfold weave; rw [abs_of_pos hQ,abs_of_pos (show 0<v by linarith)]; rw [mul_add,Real.exp_add]; push_cast; unfold b c y; ring
-- tune `ite` dec
#print axioms releaseG
def attar (p:Space3)(v u:ℝ):ℂ:= (Complex.I*u)*kite G (p:=p) v u
local notation "Q"=> attar G p
private lemma att_fee (v u:ℝ) : ‖(Q) v u‖=2*rockF G p u 1:= by
 unfold attar kite; rw [norm_mul,norm_mul,norm_mul,norm_mul,norm_I,coast_pay,one_mul,one_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (show 0≤whey E u by unfold whey; positivity),Real.norm_eq_abs]; unfold rockF whey; ring
@[fun_prop] private lemma att_c(v:ℝ): Continuous ((Q) v):=by
 let F:=kite G (p:=p) v; apply Continuous.mul (show Continuous (fun u:ℝ=> Complex.I*(u:ℂ)) from by fun_prop); unfold kite; apply Continuous.mul; apply Continuous.mul; fun_prop; exact ami_safe.comp (upC G (p:=p)); exact Complex.continuous_ofReal.comp (whey_C (norm_pos_iff.mpr t))
private lemma kite_D(v u:ℝ) : HasDerivAt (fun x:ℝ=>kite G (p:=p) x u) (attar G p v u) v:=by
 convert! (((((hasDerivAt_id' v).mul_const u).ofReal_comp.const_mul Complex.I).cexp.mul_const _).mul_const _) using 1; -- tune
 unfold attar kite coastE; simp [mul_comm]; ring -- tune
lemma kite_Dt (v:ℝ) : Integrable ((Q) v) ∧ HasDerivAt (fun x:ℝ=> ∫ u,kite G (p:=p) x u) (∫ u,(Q) v u) v:=
 hasDerivAt_integral_of_dominated_loc_of_deriv_le Filter.univ_mem (Eventually.of_forall fun i=>(kite_I G t i).1) (kite_I G t v) ((att_c G t v).aestronglyMeasurable) (Eventually.of_forall (fun i u _=>(att_fee G t u i).le)) ((side_full G p t 1 le_rfl).const_mul 2) (Eventually.of_forall (fun i z _=>kite_D G t z i)) -- binder order bound maybe u variable swapped.
omit t in
private lemma weave_der (R u:ℝ)(p:0<u): HasDerivAt (weave R) (-(R:ℂ)*weave R u) u:=by
 let f(x:ℝ):= Real.exp (-R*x); have hp:= (((hasDerivAt_id' u).const_mul (-R)).exp).ofReal_comp; let g(x:ℝ):=(f x:ℂ); have he:g=ᶠ[𝓝 u] weave R:= (lt_mem_nhds p).mono fun i h=>by unfold weave g f; rw [abs_of_pos h]
 have hx:= hp.congr_of_eventuallyEq he.symm; convert! hx using 1; unfold weave; rw [abs_of_pos p]; push_cast; ring

lemma ring_v (v:ℝ)(e:20<v): (∫ u,attar G p v u)=-(E:ℂ)*(((τ/E:ℝ):ℂ)*weave E v*leer (pulseG G p)^8):=by
 let f(x):=∫ u,kite G (p:=p) x u; let a:ℂ:= (τ/E:ℝ); let g(x):= a*weave E x* leer (pulseG G p)^8; let hV:= ((weave_der E v (by linarith)).const_mul a).mul_const (leer (pulseG G p)^8)
 have he:f=ᶠ[𝓝 v] g:= (lt_mem_nhds e).mono fun i z=>releaseG G t i z; exact (kite_Dt G t v).2.unique (hV.congr_of_eventuallyEq he) |>.trans (by unfold a; ring)
#print axioms ring_v
end
end YM.CF.Window.ArchiveK
