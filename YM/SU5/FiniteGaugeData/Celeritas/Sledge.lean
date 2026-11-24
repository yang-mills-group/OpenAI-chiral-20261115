import YM.SU5.FiniteGaugeData.Celeritas.Evan
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a b: Axis}(S:OS.Semigroup H a)(v: OS.Cross a)(x:E4)(t:ℝ)(u s:ℝ≥0)
local notation "Π" x:max=> Probe.plane x
local notation "Λ" x:max=> metal a x
abbrev smack (a t:ℝ):=Complex.exp (((t*a:ℝ):ℂ)*Complex.I)
lemma plane_rate (c:ℝ): Probe.plane x (c • v.val)=smack (ped x v) c:=by unfold Probe.plane ped smack; rw [real_inner_smul_right]
lemma smirk (a r:ℝ): HasDerivAt (smack a) (smack a r*((a:ℂ)*I)) r:= by
 let f(x:ℝ):=(((x*a:ℝ):ℂ)*I); have he: HasDerivAt f ((a:ℂ)*I) r:=by
    simp_rw [f,Complex.ofReal_mul]; convert ((Complex.ofRealCLM.hasDerivAt).mul_const (a:ℂ)).mul_const I using 1 <;> (first|rfl|change (_) * I = ↑(1 : ℝ) * _ * I; simp)
 simpa only [smack,f] using he.cexp
lemma mask(t v:ℝ): ‖smack t v‖=1:=by simp [smack, Complex.norm_exp]
@[simp] lemma mask_o(t): smack t 0=1:=by simp [smack]
lemma whiff (t a:ℝ) : ‖smack t a-1‖ ≤ |t| *|a|:=by
 have hv:= Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℝ) (f:=smack t) (s:=univ) (C:=|t|) (fun r _=>(smirk t r).differentiableAt) (fun x _=> (by rw [(smirk t x).deriv]; simp [mask])) (convex_univ) (mem_univ 0) (mem_univ a); rw [mask_o,sub_zero] at hv; exact hv
lemma flipPay (v:OS.Cross a){x:E4}(t: x∈ swingCone a) (h:‖v‖ ≤ 1): rateX a ((s:ℝ) • v.val) (u+s) x ≤ rateT a (u+s) u x:=by
 let D:= metal a (u+s) x; let E:= metal a u x; let V:= Real.exp ((s:ℝ)*x a:ℝ); have hp:= (cone_set x).1 t v h; have he:E=D*V:=by unfold D E V; unfold metal; rw [←Real.exp_add]; push_cast; ring_nf
 have hg:‖Probe.plane x ((s:ℝ) • v.val)-1‖ ≤ V-1:= by rw [plane_rate]; apply (whiff ..).trans; rw [abs_of_nonneg s.coe_nonneg]; nlinarith only [mul_le_mul_of_nonneg_left hp s.coe_nonneg, (show (s:ℝ)*x a+1 ≤ V from Real.add_one_le_exp _)]
 let ε:=‖Probe.plane x ((s:ℝ) • v.val)-1‖; have hD:0≤D:=metal_0 ..; unfold rateX; rw [metal_add,←pow_two]; change D^2*ε^2 ≤ (E -D)^2; rw [←mul_pow,he]; apply pow_le_pow_left₀ (mul_nonneg hD (norm_nonneg _)); nlinarith only [mul_le_mul_of_nonneg_left hg hD]
#check hasDerivAt_iff_tendsto_slope
-- may be strictly false outside
lemma slotPay {x:E4}(v:OS.Cross a)(p:x a < |ped x v|) (h:0 ≤ x a) (k:ℝ)(w:0<k) : ∃ s:ℝ≥0, 0<s ∧ (s:ℝ) ≤ k ∧ rateT a (u+s) u x < rateX a ((s:ℝ) • v.val) (u+s) x:=by
 let f(r:ℝ):= Real.exp (r*x a); let q:=ped x v; have he:= HasDerivAt.tendsto_slope (smirk q 0); rw [mask_o,one_mul] at he; have hx:HasDerivAt f (x a) 0:= by
    simpa only [id_eq,one_mul,zero_mul,Real.exp_zero] using ((hasDerivAt_id' (0:ℝ)).mul_const (x a)).exp
 have hv:=hasDerivAt_iff_tendsto_slope.mp hx
 have l: ‖x a‖ < ‖(q:ℂ)* I‖:= by simpa [Real.norm_eq_abs,abs_of_nonneg h,q] using p
 have η:= hv.norm.eventually_lt he.norm l; obtain ⟨r,⟨hl,hp⟩,ht⟩:= ((show ∀ᶠ i in 𝓝[>] (0:ℝ),i ∈ Ioc 0 k from Ioc_mem_nhdsGT w).and (show ∀ᶠ i:ℝ in 𝓝[>] (0:ℝ), ‖slope f 0 i‖< ‖slope (smack q) 0 i‖ from nhdsGT_le_nhdsNE _ η)).exists -- tuple pattern? Ioc∧ ; hp
 let t:ℝ≥0:= ⟨r,hl.le⟩; refine ⟨t,show 0<t from hl, hp,?_ ⟩
 let D:= metal a (u+t) x; let E:= metal a u x; let V:=f r; have hV:1 ≤ V:=Real.one_le_exp (by exact mul_nonneg hl.le h); have hg: E=D*V:=by unfold E D V metal f; rw [←Real.exp_add]; push_cast; change _=Real.exp (-((u:ℝ)+r)*_+r*_); ring_nf
 change _ < rateX a (r • v.val) (u+t) x; unfold rateX; rw [plane_rate,metal_add]; change (E-D)^2< D*D*‖smack q r-1‖^2; simp_rw [←pow_two]; rw [← mul_pow];
 rw [hg,mul_comm D V]; have hd:0<D:=Real.exp_pos _; apply pow_lt_pow_left₀ _ (by nlinarith only [mul_le_mul_of_nonneg_right hV hd.le]) (by norm_num)
 have hε:V-1< ‖smack q r-1‖:=by simp only [slope, vsub_eq_sub, norm_smul, mask_o, Real.norm_eq_abs, abs_inv,sub_zero] at ht; rw [show f 0=1 from (by unfold f; simp), abs_of_nonneg hl.le, abs_of_nonneg (sub_nonneg.mpr hV)] at ht; exact lt_of_mul_lt_mul_left ht (inv_nonneg.mpr hl.le)
 nlinarith only [mul_lt_mul_of_pos_left hε hd]
#print axioms slotPay
variable (x:H)(P: PVM H E4)
local notation "U" v:max=> S.U v
local notation "F" t:max=> S.E t
abbrev Velocity (u:ℝ≥0)(k:ℝ)(x:H): Prop := ∀ (v:Cross a), ‖v‖ ≤ 1 → ∀ (s:ℝ≥0), (s:ℝ)≤ k→ dist ((U ((s:ℝ) • v)) ((F (u+s)) x)) ((F (u+s)) x) ≤ dist ((F (u+s)) x) ((F u) x)
local notation "T"=>swingCone a
local notation "Pm"=> S.ℚmeasure
local notation "Po" x:max=> S.ℚmeasure.diagonal x
abbrev Cinema := S.ℚmeasure.region (swingCone a)ᶜ=0
@[fun_prop] lemma ratex(z:E4) : Continuous (rateX a z s):= (mint _).mul (((Probe.plane_cont.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow _)
@[fun_prop] lemma ratet : Continuous (rateT a u s):= ((mint _).sub (mint _)).pow _
lemma veer (k:ℝ) : Velocity S u k x ↔ ∀ (v:Cross a), ‖v‖ ≤ 1 → ∀ (s:ℝ≥0), (s:ℝ)≤ k→ (∫ p, rateX a ((s:ℝ) • v.val) (u+s) p ∂ (Po x)) ≤ (∫ p, rateT a (u+s) u p ∂ (Po x)):=by
 unfold Velocity; apply forall_congr'; intro v; apply forall_congr'; intro e; apply forall_congr'; intro s; apply forall_congr'; intro q
 rw [ (paid_P ..).2,(paid_T ..).2]; refine Iff.trans ?_ (sq_le_sq₀ (by positivity) (by positivity)).symm
 rw [←vacancy]; rfl
lemma chinaK (p:Cinema S)(w:H) : ∀ᵐ u∂Po w, u∈ T:= by rw [ae_iff]; exact ((Pm).null_pair (cone_c a).isOpen_compl.measurableSet w).2 (by rw [p]; rfl) -- tune arg
variable {k:ℝ}
lemma vell (p:Cinema S):Velocity S u k x :=(veer S u x k).2 (fun v e s _=> integral_mono_ae (paid_P ..).1 (paid_T ..).1 (Eventually.mono (chinaK S p x) (fun i p=> flipPay u s v p e))) -- tune
-- enough on dense via closed condition
lemma closed_v {K:ℝ}: IsClosed {x:H| Velocity S u K x}:=by
 simp_rw [Velocity,setOf_forall]; refine isClosed_iInter (fun i=> isClosed_iInter (fun _=> isClosed_iInter fun s=> isClosed_iInter (fun e=> isClosed_le ?_ ?_))); all_goals fun_prop
lemma sure_support {Q:PVM H E4}(s:Set E4)(h:IsOpen s)(p:IsClosed sᶜ) (x:H)(t:Q.diagonal x s≠0): let y:=Q.region s x; (∀ᵐ z ∂ Q.diagonal y,z∈ s) ∧ NeZero (Q.diagonal y):=by
 intro y; have hv:y≠0:= fun e=> t ((Q.null_pair h.measurableSet x).2 e); constructor
 · rw [ae_iff]; apply (Q.null_pair p.measurableSet y).2; change Q.region sᶜ y=0; unfold y; rw [← ContinuousLinearMap.comp_apply,Q.joins p.measurableSet h.measurableSet,compl_inter_self,Q.none]; rfl
 exact ⟨fun z=> hv (let t:= (Q.null_pair (s:=univ) MeasurableSet.univ y).1 (by rw [z]; rfl); by rwa [Q.all] at t) ⟩
lemma free_run (u0:0<k)(h:∀ x:H,Velocity S u k x) : Cinema S:=by
 have he(x:H) : (Po x).support ⊆ swingCone a:=by
    intro y p; rw [cone_set]; intro v t; by_contra! e
    obtain ⟨s,g,p',l⟩:= slotPay u v e (S.nonneg x p) k u0; let f:=rateX a ((s:ℝ) • v.val) (u+s); let g:=rateT a (u+s) u; let V:= {x| g x<f x}; have hz:IsOpen V:= isOpen_lt (ratet _ _) (ratex ..); have H0:(Po x) V≠0:= ne_of_gt ((Measure.mem_support_iff_forall y).1 p V (hz.mem_nhds l)) -- extra V arg
    obtain ⟨Ax,l⟩:= sure_support V hz hz.isClosed_compl x H0; let X:= (Pm).region V x; haveI hp:NeZero (Po X):=l
    have hL:g ≤ᵐ[Po X] f:= Ax.mono (fun i t=> (show g i<f i from t).le); have hf:Integrable f (Po X):=(paid_P ..).1; have hk:Integrable g (Po X):=(paid_T ..).1
    have hv:∫ z,g z ∂ (Po X)=∫ z,f z ∂(Po X):=le_antisymm (integral_mono_ae hk hf hL) ((veer S u X k).1 (h X) v t s p')
    obtain ⟨z,e,hz⟩:= (Ax.and ((integral_eq_iff_of_ae_le hk hf hL).1 hv)).exists; exact (show g z<f z from e).ne hz

 unfold Cinema; ext1 x; exact ((Pm).null_pair (cone_c a).isOpen_compl.measurableSet x).1 (measure_mono_null (compl_subset_compl.mpr (he x)) (measure_compl_support))
theorem correct (u0:0<k)(V:Set H) (p:Dense V): Cinema S ↔ ∀ x∈V,Velocity S u k x:= ⟨fun p x _=> vell S u x p,fun e=> free_run S u u0 fun x=> closure_minimal (t:={x| Velocity S u k x}) e (closed_v S u) (p x)⟩
#print axioms correct
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
