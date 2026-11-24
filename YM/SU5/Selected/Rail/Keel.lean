import YM.SU5.Selected.Rail.Golf
/-! # Hankel over negative upper samples & positive X. Divergence vs null. *Every* k≥3.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
open Finset
variable {k:ℕ}(W:FaceL){p:ℕ}(Z:Fin p→ℂ)
-- no need normalization. hill = [-π,π]^3 rather than deck: no face costs.
def keystone (k:ℕ)(W:FaceL)(t:ℕ):ℂ:=∫ x in hill, grappa W x *hammer k t x
lemma dash_ship (A B s t:ℝ)(ha:0<A)(ht:s<t)(hp:0<s): ∀ᶠ n:ℕ in atTop, B*s^n< A*t^n:=by
 have he:0<t:=hp.trans ht; have hz:Tendsto (fun n:ℕ=> B*(s/t)^n) atTop (𝓝 0):=by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hp he).le (div_lt_one he|>.mpr ht)).const_mul B
 filter_upwards [hz.eventually (gt_mem_nhds ha)] with n p; rw [div_pow,mul_div_assoc'] at p; exact (div_lt_iff₀ (pow_pos he n)).mp p -- names
variable (h:3≤k)
abbrev hammerLand := volume.restrict hill
instance : IsFiniteMeasure hammerLand:= ⟨by rw [hammerLand,Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hill_compact.measure_lt_top⟩
lemma hammer_mem : ∀ᵐ x ∂hammerLand, x∈ Cliff:= by filter_upwards [ae_restrict_mem (μ:=volume) (hill_compact.measurableSet), Measure.ae_ne hammerLand 0] with t g b; exact ⟨g,b⟩
lemma act_hammer {V:Type*}[NormedAddCommGroup V]{f:Facet3→V}(p:ContinuousOn f hill): Integrable f hammerLand:=p.integrableOn_compact hill_compact
include h
private def taxes (t:ℕ)(x:Facet3):ℂ:= grappa W x*aero Z k t x -- explicit k?
lemma sails: ∀ n:ℕ, Integrable (taxes W Z (k:=k) n) hammerLand:=fun n=> act_hammer ((grappa_c W).continuousOn.mul (aero_c h Z)) -- h order
lemma towards (e:Z≠0): ∀ᶠ m:ℕ in atTop, 0< (∫ x, taxes W Z (k:=k) (4+m) x ∂hammerLand).re:=by
 classical
 let μ:=hammerLand; obtain ⟨H,y,C,R,T,hH,hC,hT,hR,ht,v,l⟩:=habitat k W Z e; let a:= Real.exp (-H); have ha:0<a:= Real.exp_pos _; have hp:0<T:=ha.trans ht
 let D:= ball (focus y) R; have hb: MeasurableSet D:=isOpen_ball.measurableSet; have hx:D ⊆ hill:=fun x p=> (l x p).2.1.1
 have hb':0<μ.real D:= ENNReal.toReal_pos (show μ D≠0 from (show 0<μ D from (by rw [show μ D=volume D from (by unfold μ hammerLand; rw [Measure.restrict_apply hb, Set.inter_eq_left.mpr hx])]; exact measure_ball_pos _ _ hR)).ne') ((measure_lt_top ..).ne) -- calc under args implicit
 let K:= fun x=>(aero Z k 4 x).re;
 have hK:Integrable K μ:= (act_hammer (aero_c (n:=4) h Z)).re;
 let B:=∫ x,K x ∂μ;
 filter_upwards [dash_ship (μ.real D*C) B a T (mul_pos hb' hC) ht ha] with i p
 let F:=fun x=> (taxes W Z (k:=k) (4+i) x).re
 have he : (∫ x, F x ∂μ)= (∫ x, taxes W Z (k:=k) (4+i) x ∂hammerLand).re:= integral_re (sails W Z h _) -- placeholder
 have hf: Integrable F μ:= (sails W Z h _).re
 let g(x:Facet3):= D.indicator (fun _=>C*T^i) x; let f(x:Facet3):= K x*a^i
 have hg:Integrable g μ:= (integrable_const (μ:=μ) _).indicator hb
 have hp':∀ᵐ x ∂μ, g x-f x ≤ F x:=by
    filter_upwards [hammer_mem] with x z
    have hx:0≤ f x:=mul_nonneg (studio Z z (gleam_nonneg Z z) (by omega)) (by positivity)
    by_cases c:x∈D
    · obtain ⟨h,_,w,t⟩:= l x c; apply le_trans (sub_le_self _ hx); unfold g; rw [Set.indicator_of_mem c]; exact stone_vibe (k:=k) Z i z hp.le w (v x h).le t -- order
    unfold g; rw [Set.indicator_of_notMem c,zero_sub]; rcases le_or_gt ‖x‖ H with k'|k';
    · apply le_trans (neg_nonpos.mpr hx); unfold F taxes; rw [Complex.mul_re,(flying Z (by omega) z).2,mul_zero,sub_zero]; exact mul_nonneg (v x k').le (studio Z z (gleam_nonneg Z z) (by omega))
    exact stone_halt Z _ z k'.le hH
 rw [←he]; have hv:= integral_mono_ae (hg.sub (hK.mul_const (a^i))) hf hp'
 change (∫ x,g x-K x*a^i ∂μ) ≤ _ at hv; rw [integral_sub hg (hK.mul_const _), show (∫ x,g x ∂μ)=μ.real D • (C*T^i) from integral_indicator_const _ hb, smul_eq_mul, integral_mul_const] at hv; change _ < (∫ x,F x ∂μ); unfold B at p; linarith
lemma outprice(n:ℕ): (∫ x,taxes W Z (k:=k) n x ∂hammerLand)=∑ i:Fin p,∑ j:Fin p, star (Z i)*(keystone k W (n+i.val+j.val)*Z j):=by
 let f(t):=fun x=> grappa W x*hammer k t x; have he(t:ℕ):Integrable (f t) hammerLand:= act_hammer ((grappa_c W).continuousOn.mul (hammer_c h t)); let g (i j:Fin p) (x:Facet3):= star (Z i)*(f (n+i.val+j.val) x*Z j)
 have hp(i j:Fin p):Integrable (g i j) hammerLand:= ((he _).mul_const _).const_mul _
 have ht(x): taxes W Z (k:=k) n x=∑ i:Fin p,∑ j:Fin p,g i j x:=by unfold taxes aero g f; simp_rw [mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
 simp_rw [ht]; rw [integral_finsetSum _ (fun (i:Fin p) _=> integrable_finsetSum _ (fun j _=> hp i j))]; apply sum_congr rfl; intro i _; rw [integral_finsetSum _ (fun j _=> hp i j)]; apply sum_congr rfl; intro j _; rw [show g i j=_ from rfl, show (∫ x,g i j x ∂hammerLand)=_ from ?_] -- tune
 unfold g; rw [integral_const_mul, integral_mul_const]; rfl
lemma tariff (e: Z≠0): ∀ᶠ m:ℕ in atTop,0< (∑ i:Fin p,∑ j:Fin p, star (Z i)*(keystone k W (4+m+i.val+j.val)*Z j)).re:= (towards W Z h e).mono fun i v=> (outprice W Z h (4+i)) ▸ v
-- legitimate for complex sheet. enough later span all combinations. rich output
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms tariff
#print axioms towards
#print keystone
