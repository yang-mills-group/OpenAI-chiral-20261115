import YM.SU5.FiniteGaugeData.Mist.Utah
import YM.Mink.Geometry
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a b: Axis}(S:OS.Semigroup H a)(v: OS.Cross a)(x:E4)(t:ℝ)(u s:ℝ≥0)
local notation "ξ" v:max=> (v:Cross a)
def ped(x:E4)(v:Cross a):ℝ:= inner ℝ x v.val
abbrev pace(x:E4):Cross a:= SEP a x
def swingCone (a:Axis):={x:E4| ‖(pace (a:=a) x)‖≤ x a}
lemma sep_fee (x:E4)(v:OS.Cross a):inner ℝ (pace x) v=ped x v:=by
 change inner ℝ (x-x a • basis a) v.val=_; rw [inner_sub_left, real_inner_smul_left,_root_.YM.basis_inner,show v.val a=0 from v.property,mul_zero,sub_zero]; rfl
lemma cone_set(x:E4): x∈swingCone a ↔ ∀ v:Cross a,‖v‖ ≤ 1→|ped x v| ≤ x a:=by
 constructor
 · intro h v p; rw [←sep_fee]; exact ((abs_real_inner_le_norm ..).trans (mul_le_of_le_one_right (norm_nonneg _) p)).trans h
 intro h; let v:Cross a:=pace x; let H:= ‖v‖; have he:0 ≤ x a:= le_trans (abs_nonneg _) (h 0 (by rw [norm_zero]; exact zero_le_one)); change H≤_; by_cases p:H=0; · rw [p]; exact he
 have hp:0<H:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm p); let z:=H⁻¹ • v; have hc:‖z‖=1:=by unfold z; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]; exact inv_mul_cancel₀ p
 have ht:=h z hc.le; rw [← sep_fee] at ht; change |inner ℝ v z|≤ _ at ht; rw [show inner ℝ v z=H from (by change inner ℝ v.val (H⁻¹ • v.val)=_; rw [real_inner_smul_right, real_inner_self_eq_norm_sq,pow_two,←mul_assoc,show H⁻¹* ‖v.val‖=1 from inv_mul_cancel₀ p,one_mul]; rfl),abs_of_pos hp] at ht; exact ht
lemma cone_c (a:Axis): IsClosed (swingCone a):= isClosed_le ((SEP a).continuous.norm) (by fun_prop)
lemma timeCone : swingCone timeAxis=Mink.cone:=by
 ext x; change ‖pace (a:=timeAxis) x‖≤_ ↔ ‖spatial x‖ ≤ _; have hp:‖pace (a:=timeAxis) x‖= ‖spatial x‖:=by
    change ‖(x-x timeAxis • basis timeAxis)‖=‖spatial x‖; apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [Mink.squares]; simp [sub_eq_add_neg,time] -- simp
 rw [hp]; rfl
lemma swing_t (u:ℝ≥0)(x:E4): S.unit.translation x*S.E u = S.E u*S.unit.translation x:=by
 obtain rfl|h:= eq_or_lt_of_le (show 0 ≤ u from by positivity); · rw [S.eZero]; rfl
 let v:=S.U (SEP a x); let B:=OS.Semigroup.duration u; let t:=x a; have hx:S.edge t*S.E u=S.E u*S.edge t:=by rw [← S.roots_heat h]; exact (S.along (dur.mpr h) t).trans (S.either (dur.mpr h) t).symm
 change (S.edge t*v)*S.E u=S.E u* (S.edge t*v); rw [mul_assoc,←show S.E u*v=v*S.E u from S.independent ..,←mul_assoc,hx,mul_assoc]
variable (w:H)(i u:ℝ≥0)
open scoped Classical
local notation "Q" => S.ℚmeasure
local notation "Qv" => (Q).diagonal w
local notation "Ux" x:max=> S.unit.translation x
def metal (a: Axis)(u:ℝ≥0)(p:E4):= Real.exp (-u * p a:ℝ) -- cast
local notation "Λ" u:max=> metal a u
lemma metal_add(i j:ℝ≥0)(x:E4): metal a (i+j) x=(Λ i) x*(Λ j) x:=by unfold metal; rw [show _*_= (-(i:ℝ)) *x a+ (-(j:ℝ))* x a from ?_,Real.exp_add]; push_cast; ring
lemma metal_p(i:ℝ≥0){x:E4}(v:0≤ x a):metal a i x ≤ 1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr i.coe_nonneg) v)
lemma metal_0(i:ℝ≥0)(x:E4):0≤ metal a i x:= (Real.exp_pos _).le
@[fun_prop] lemma mint(i:ℝ≥0): Continuous (metal a i):=by unfold metal; fun_prop
lemma mint_I(i:ℝ≥0): Integrable (metal a i) ((Q).diagonal w):= by apply Integrable.of_bound (mint i).aestronglyMeasurable 1; filter_upwards [S.bright w] with x p; rw [Real.norm_of_nonneg (metal_0 ..)]; exact metal_p _ p
-- real part.
lemma cape_P (z:E4): (inner ℂ w ((Ux z) (S.E u w))).re= ∫ x:E4,(Probe.plane x z).re * metal a u x ∂ (Qv):=by
 let y:ℂ:=↑(u:ℝ)* Complex.I; have he:= S.heat z w (z:=y) (show y∈Paley.high from (by change 0≤y.im; simp [y])); have hc: ∀ x:E4, Complex.exp (↑(x a)*y*I)=(metal a u x:ℂ):=by
    intro x; unfold metal y; rw [ofReal_exp]; congr 1; push_cast; calc _ = ((x a:ℝ):ℂ)*(u:ℝ)*(I*I):=by ring
                                                                         _ = _:=by rw [I_mul_I]; ring
 simp_rw [hc] at he; change inner ℂ w ((Ux z) (S.edge y.re (S.E y.im.toNNReal w)))=(∫ x:E4, _ ∂ Qv) at he; rw [show y.re=0 from by simp [y],S.birth,show y.im.toNNReal=u from by simp [y]] at he
 rw [ContinuousLinearMap.id_apply] at he; rw [he, ←RCLike.re_eq_complex_re,←integral_re]; apply integral_congr_ae; filter_upwards with x; simp
 let h:= Complex.ofRealCLM.integrable_comp (mint_I S w u); exact Integrable.bdd_mul h (Continuous.aestronglyMeasurable (plane_cont.comp (continuous_id.prodMk continuous_const))) (Eventually.of_forall (fun x=>le_of_eq (plane_norm x z))) -- tune
local notation "F" u:max=> S.E u w
local notation "G" x:max => (Probe.plane x)
lemma cape_deg (v:E4) : (inner ℂ (F i) ((Ux v) (F u))).re=∫ x:E4,(Probe.plane x v).re * metal a (i+u) x ∂Qv:=by
 refine Eq.trans (congrArg Complex.re ?_) (cape_P S w (i+u) v)
 rw [← ContinuousLinearMap.adjoint_inner_right, S.sym]; change _=inner ℂ w ((Ux v) _); refine congrArg (fun z:H.Op=>inner ℂ w (z w)) (show S.E i*((Ux v)*S.E u)=(Ux v)*S.E _ from (by rw [←mul_assoc, ← swing_t, mul_assoc, show S.E (i+u)=S.E i*S.E u from S.time ..]))
lemma cape_fee : (inner ℂ (F i) (F u)).re= ∫ x:E4, metal a (i+u) x ∂Qv:=by have he:= cape_deg S w i u 0; rw [S.unit.origin,ContinuousLinearMap.id_apply] at he; simpa using he
lemma Mint_I' (z:E4): Integrable (fun x:E4=> (Probe.plane x z).re* (Λ i) x) Qv:=by
 apply Integrable.bdd_mul (c:=1) (mint_I S w i) (Complex.continuous_re.comp (Probe.plane_cont.comp (continuous_id.prodMk continuous_const))|>.aestronglyMeasurable)
 filter_upwards with x; apply le_trans (Complex.abs_re_le_norm _); exact le_of_eq (plane_norm _ _)
def rateX(a:Axis)(z:E4)(i:ℝ≥0)(x:E4) := metal a (i+i) x * ‖Probe.plane x z-1‖^2
def rateT(a:Axis)(i j:ℝ≥0)(x:E4):=(metal a j x-metal a i x)^2
lemma paid_P (z:E4)(i:ℝ≥0): Integrable (rateX a z i) Qv ∧ ∫ x, rateX a z i x ∂Qv = dist ((Ux z) (F i)) (F i)^2:= by
 let f:= fun x:E4=> Probe.plane x z; let g:=Λ (i+i); let h(x:E4):=(f x).re*g x; have he:rateX a z i=fun x:E4=> 2*g x- 2*h x:=by ext1 x; let G':= f x; change g x*‖G'-1‖^2= _; have he:‖G'‖=1:=Probe.plane_norm ..; rw [norm_sub_sq (𝕜:=ℂ), RCLike.re_eq_complex_re,he,norm_one,one_pow, show inner ℂ G' 1=(starRingEnd ℂ G') from by change 1*_= _; rw [one_mul]; rfl,conj_re]; unfold h; unfold G'; ring
 have hx:= mint_I S w (i+i); have hg:Integrable h Qv:= Mint_I' S w (i+i) z; rw [he]; constructor; · exact (hx.const_mul 2).sub (hg.const_mul 2)
 rw [integral_sub (hx.const_mul 2) (hg.const_mul 2),integral_const_mul,integral_const_mul, show ∫ x,g x ∂Qv = ‖F i‖^2 from (Eq.trans (cape_fee S w i i).symm (inner_self_eq_norm_sq (𝕜:=ℂ) _)), dist_comm, dist_eq_norm, norm_sub_sq (𝕜:=ℂ), S.unit.unitary, RCLike.re_eq_complex_re]; -- tune
 rw [cape_deg]; unfold h f g; ring
lemma paid_T : Integrable (rateT a i u) Qv ∧ ∫ x, rateT a i u x ∂Qv=dist (F i) (F u)^2:=by
 let f:=Λ (i+i); let g:=Λ (u+u); let v:=Λ (i+u); have he:rateT a i u=fun x:E4=> f x-2*v x+g x:=by ext x; unfold rateT f v g; simp_rw [metal_add]; ring
 let hf:= mint_I S w (i+i); let hg:= mint_I S w (u+u); have hp:Integrable (fun x:E4=>2*v x) Qv:=(mint_I S w (i+u)).const_mul _; rw [he]; constructor; · exact (hf.sub hp).add hg
 rw [integral_add (f:=fun x=>f x-2*v x) (g:=g) (hf.sub hp) hg,integral_sub (f:=f) (g:=fun p=>2*v p) hf hp,integral_const_mul, dist_eq_norm,norm_sub_sq (𝕜:=ℂ), RCLike.re_eq_complex_re]; unfold f v g; rw [← cape_fee,←cape_fee,←cape_fee,show ∀ u:ℝ≥0,(inner ℂ (F u) (F u)).re=‖(F u)‖^2 from (by intro u; exact inner_self_eq_norm_sq (𝕜:=ℂ) _), show (inner ℂ (F u) (F u)).re=‖(F u)‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _]
#print axioms paid_P
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
