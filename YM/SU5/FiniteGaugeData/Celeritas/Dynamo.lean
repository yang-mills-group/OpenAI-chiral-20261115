import YM.SU5.FiniteGaugeData.Celeritas.Sledge
import YM.Analysis.Weak
import Mathlib.Analysis.InnerProductSpace.Dual
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a b: Axis}(S:OS.Semigroup H a)(v: OS.Cross a)(x p:E4)(t:ℝ)(u s:ℝ≥0)(w:H)
variable (P:Cinema S)(Q:‖v‖≤1)(c:ℝ) (h:0<u)(z:ℂ)
local notation "Pm"=>S.ℚmeasure
local notation "Po" x:max=> S.ℚmeasure.diagonal x
local notation "ρ" z:max=> S.U z
local notation "T"=>swingCone a
open scoped Classical
abbrev lanes(c:ℝ):Set ℂ:= {x| |x.im|<c}
lemma lanes_open : IsOpen (lanes c):= isOpen_lt continuous_im.abs continuous_const
lemma lanes_r(u:0<c) : (t:ℂ)∈lanes c:= by simpa [lanes]
lemma lane_v : Convex ℝ (lanes c):=by
 intro x hp y h a b ha hb z; change |(a • x+b • y).im|<_; change |x.im|<c at hp; change |y.im|<c at h; rw [add_im,real_smul,real_smul]; simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero]; apply lt_of_le_of_lt (abs_add_le ..); rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]; rcases eq_or_lt_of_le ha with rfl|ha; · simp at z; subst b; simp only [one_mul,zero_mul,zero_add]; exact h
 nlinarith only [mul_lt_mul_of_pos_left hp ha,mul_le_mul_of_nonneg_left h.le hb, show a*c+b*c=c from (by rw [←add_mul,z,one_mul])]
-- damped U complex extension
def hubK (v:Cross a)(u:ℝ≥0)(z:ℂ)(p:E4): ℂ:= Complex.exp (-(u:ℝ)*(p a:ℂ)+(ped p v:ℂ)*z*I)
include Q
lemma serve_K (y: z∈lanes c)(b:p∈ swingCone a) (e:c≤u) : ‖hubK v u z p‖≤ Real.exp (p a*(c-u)):=by
 let x:=p a; have he:= (cone_set p).1 b v Q; have hx:0≤ x:=(abs_nonneg _).trans he; let k:=ped p v; have ht:|z.im|<c:=y
 unfold hubK; rw [norm_exp]; apply Real.exp_monotone; -- complex expression `-(u:ℝ)*(p a:ℂ)` coe. simp
 simp; nlinarith only [(abs_le.mp (show |k*z.im|≤ x*c from (by rw [abs_mul]; exact mul_le_mul he ht.le (abs_nonneg _) hx))).1]
omit Q
@[fun_prop] lemma ped_c : Continuous (fun p=>ped p v):=by unfold ped; fun_prop
@[fun_prop] lemma hub_c : Continuous (hubK v u z):=by unfold hubK; fun_prop
include Q P
lemma hub_I (p:z∈lanes u): Integrable (hubK v u z) (Po w) ∧ ∀ᵐ x∂(Po w),‖hubK v u z x‖≤1 := by
 have he:∀ᵐ x∂(Po w),‖hubK v u z x‖≤1:= by filter_upwards [chinaK S P w] with x z; -- shadow
                                                               first| convert serve_K v x u Q _ _ p z le_rfl using 1; simp
 exact ⟨Integrable.of_bound (hub_c ..).aestronglyMeasurable 1 he,he⟩
def wheelB(z:ℂ)(x:H):= ∫ p,hubK v u z p ∂(Po x)
lemma wheel_bound(p:z∈ lanes u): ‖wheelB S v u z w‖≤ ‖w‖^2:=by
 apply le_trans (norm_integral_le_of_norm_le (g:=fun _=>1) (integrable_const _) (hub_I S v u w P Q z p).2) (le_of_eq ?_); rw [integral_const]; change (Po w).real univ • (1:ℝ)=_; rw [S.ℚmeasure.same MeasurableSet.univ,S.ℚmeasure.all]; simp
lemma wheel_r : wheelB S v u (t:ℂ) w=inner ℂ w (S.U (t • v) (S.E u w)):=by
 let y:ℂ:=↑(u:ℝ)* Complex.I; let x:=t • v.val; have he:= S.heat x w (z:=y) (show y∈Paley.high from (by change 0≤y.im; simp [y])); have hc:∀ p:E4,Complex.exp (↑(p a)*y*I)=(metal a u p:ℂ):=by
    intro p; unfold metal y; rw [ofReal_exp]; congr 1; push_cast; calc _ = ((p a:ℝ):ℂ)*(u:ℝ)*(I*I):=by ring
                                                                         _ = _:=by rw [I_mul_I]; ring
 simp_rw [hc] at he; change inner ℂ w ((S.unit.translation x) (S.edge y.re (S.E y.im.toNNReal w)))=(∫ x:E4, _ ∂(Po w)) at he; rw [show y.re=0 from by simp [y], S.birth,show y.im.toNNReal=u from by simp [y], ContinuousLinearMap.id_apply] at he
 let V(t:ℝ):=t • v; have hv:S.unit.translation x=S.U (V t):= vacancy S (t • v)
 refine Eq.trans ?_ (he.symm.trans (congrArg (fun A:H.Op=>inner ℂ w (A (S.E u w))) hv)); unfold wheelB; apply integral_congr_ae; filter_upwards with p;
 unfold hubK; rw [Complex.exp_add,show x=t • v.val from rfl,plane_rate]; unfold metal smack; push_cast; ring_nf
#print axioms wheel_bound
variable (u0:0<s)
local notation "C"=> lanes (u:ℝ)
private lemma eddy (t:z∈ lanes c)(g:c<u) (e:p∈T): ‖hubK v u z p*(ped p v:ℂ)*I‖ ≤ ((u:ℝ)-c)⁻¹:=by
 simp only [norm_mul,norm_I,norm_real,Real.norm_eq_abs,mul_one]
 let L:=(u:ℝ)-c; have hp:0≤p a:= (norm_nonneg _).trans e; have he:0<L:=sub_pos.mpr g
 refine (mul_le_mul (serve_K v p u Q c z t e g.le) ((cone_set _).1 e v Q) (abs_nonneg _) (Real.exp_pos _).le).trans ?_; rw [show p a*(c-u)=-(L*p a) from (by unfold L; ring),Real.exp_neg]; refine le_of_mul_le_mul_left ?_ (Real.exp_pos (L*p a)); rw [← mul_assoc,mul_inv_cancel₀ (Real.exp_pos _).ne',one_mul]; exact (le_inv_mul_iff₀ he).2 ((le_of_lt (lt_add_one _)).trans (Real.add_one_le_exp _)) |> fun h=> by rwa [mul_comm] at h -- tune
omit P Q in
private lemma has_K : HasDerivAt (fun z=>hubK v u z p) (hubK v u z p * (ped p v:ℂ)* I) z:=by
 unfold hubK; convert ((((hasDerivAt_id' z).const_mul (ped p v:ℂ)).mul_const I).const_add (-↑(u:ℝ)*(p a:ℂ))).cexp using 1 <;> (first|rfl|ring)
-- deriv bound easier continuation op
lemma arch (p:z∈ lanes (u:ℝ)):HasDerivAt (fun z=>wheelB S v u z w) (∫ y:E4, hubK v u z y*(ped y v:ℂ)*I ∂(Po w)) z:=by
 obtain ⟨c,h,hp⟩:=exists_between (show |z.im|<(u:ℝ) from p); exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F':=fun z y=>hubK v u z y*(ped y v:ℂ)*I) (μ:= Po w) (bound:=fun _=> ((u:ℝ)-c)⁻¹) ((lanes_open c).mem_nhds (show z∈lanes c from h)) (Eventually.of_forall (fun i=> (hub_c v u i).aestronglyMeasurable)) (hub_I S v u w P Q z p).1 (by fun_prop) ((chinaK S P w).mono (fun i p y t=> eddy S v i u P Q c y t hp p)) (integrable_const _) (Eventually.of_forall (fun i z _=> has_K v i u z))).2
lemma lap_hol : AnalyticOnNhd ℂ (fun z=>wheelB S v u z w) (lanes u):=DifferentiableOn.analyticOnNhd (fun z p=>(arch S v u w P Q z p).differentiableAt.differentiableWithinAt) (lanes_open u) -- order
omit P Q
-- identity theorem on lanes
lemma settleA {f g:ℂ→ℂ}(p:z∈lanes c)(F:AnalyticOnNhd ℂ f (lanes c))(h:AnalyticOnNhd ℂ g (lanes c))(y:∀ t:ℝ,f t=g t): f z=g z := by
 have he:0<c:=(abs_nonneg _).trans_lt (show _ < c from p); apply F.eqOn_of_preconnected_of_frequently_eq h (lane_v c).isPreconnected (lanes_r 0 c he) ?_ p; let x(t:ℝ):ℂ:=t; intro h
 have hp:Tendsto x (𝓝[>] 0) (𝓝[≠] 0):=by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f:=x) (l:=𝓝[>] 0) (a:=0) (s:={0}ᶜ) ?_ ?_; · exact continuous_ofReal.continuousAt.continuousWithinAt
    filter_upwards [self_mem_nhdsWithin] with i u; exact fun e=> (Set.mem_Ioi.mp u).ne' (by simpa [x] using e) -- tune ofRealCast
 have H: ∀ᶠ i:ℂ in 𝓝[≠] 0,f i≠g i:=h; obtain ⟨v,z'⟩:=(hp.eventually H).exists; exact z' (y v)
#print axioms arch
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
