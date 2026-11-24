import ForceSatin.Vineyard
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
local notation "π" => Real.pi
open YM.Stationary (Gaia exileE cartWeight cart_weight_pos orbit_at)
open MeasureTheory
open scoped SchwartzMap FourierTransform
open Complex (ofReal)
open Stationary (earth_meas boundsEarth earth_bounded)
open scoped Classical
-- adaptation daylightK.Pie.M. fixed R, real cube Ω concentrated.Cap. no subselection poses.
variable {R:ℝ}{N:Side}{x:Gaia}{k:Site N}
private lemma shoutX (h:x∈ pie R k)(F:Site N→ℂ): april R F x=F k:=by
 rw [april,sum_eq_single k]; · rw [Set.indicator_of_mem h]
 · intro i l v; rw [Set.indicator_of_notMem (show x∉pie R i from fun g=>Set.disjoint_left.mp (Ember.clears v) g h|>False.elim)] -- tune
 simp
private lemma voidX (h:∀ k:Site N,x∉pie R k)(F:Site N→ℂ): april R F x=0:=sum_eq_zero fun i _=>Set.indicator_of_notMem (h _) _
private lemma polarX (F:Site N→ℂ)(p:0<R): (∫ x:Gaia,april R F x)= (R*2*pinch N)^4 • (∑ i,F i):=by
 unfold april; rw [integral_finsetSum, Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [integral_indicator (pies _ _),setIntegral_const,Measure.real,pea p i,ENNReal.toReal_ofReal (by have he:=pinch_pos N; positivity)]
 intro i _; apply (integrable_indicator_iff (pies _ _)).2 (integrableOn_const ?_); rw [pea p i]; finiteness
private lemma april_a (A:Site N→ℂ)(R:ℝ): AEStronglyMeasurable (april R A) volume:=by let F(i:Site N):=(pie R i).indicator (fun _=>A i); rw [show april R A=∑ i,F i by ext1 i; exact (Finset.sum_apply _ _ _).symm]; exact Finset.aestronglyMeasurable_sum (Finset.univ:Finset (Site N)) (fun i _=>(show AEStronglyMeasurable (fun _:Gaia => A i) volume from aestronglyMeasurable_const).indicator (pies R i))

section
lemma yard_one(k:Site N) : pie 1 k=cellH k:=by simp [pie]
structure Juno (s:Offset N):Prop where
 even:Even N.val
 fare(k:Site N): moor (glen s k)≠0 → pinch N ≤ ‖moor (glen s k)‖
def micaO (N:Side):Offset N:=⟨0,by simp only [Bound,norm_zero]; exact (pinch_pos _).le⟩
lemma juneB (N:Side)(e:Even N.val): Juno (micaO N):=⟨e,fun i _=>by unfold glen; simp only [micaO,add_zero]; exact torch i⟩
lemma juneC (N:Side)(e:Even N.val): Juno (rubyOff N):=by
 refine ⟨e,fun k x=>?_⟩; have hp:= pinch_pos N; let y:=moor (glen (rubyOff N) k); obtain ⟨i,u⟩:∃ i:Axis,y i≠0:=by by_contra! h; apply x; change y=0; ext i; exact h i
 have hv:y i= 2*(chert (k i):ℝ)*pinch N:=by change principal (k i)+-pinch N=_; rw [ch_price]; ring
 have he: 1 ≤ |(chert (k i):ℝ)|:=by exact_mod_cast (show (1:ℤ) ≤ |chert (k i)| from (by have he:chert (k i)≠0:=fun z=>u (by rw [hv,z]; simp); have hp:=abs_pos.mpr he; omega))
 apply le_trans _ (sed y i); rw [hv,abs_mul,abs_mul,abs_of_pos hp,abs_of_pos (by norm_num : 0 < (2:ℝ))]; nlinarith
lemma norm_r (z:Cover)(h:z≠0):1 ≤ ‖moor (shaftX z)‖:=by
 obtain ⟨i,e⟩:= Function.ne_iff.mp h; apply le_trans _ (sed (moor (shaftX z)) i); change 1≤|(z i:ℝ)|; exact_mod_cast (show (1:ℤ)≤|z i| from (by have h:=abs_pos.mpr (show z i≠0 from e); omega))
abbrev scape(z:Cover):Gaia:= moor (shaftX z)
lemma alias_ch(s:Offset N)(k:Site N)(z:Cover): charK s k z=burn (scape z) (moor (glen s k)):=by rw [cartR s z (R:=1) one_pos,one_smul,show riseX 1 z=scape z from (by unfold riseX scape; congr 1; ext1 i; simp [shaftX])]
open Spring Spring.SunPay
variable {F: Momentum→ℂ}{X:Gaia→ℂ}(H:SunPay F X)
abbrev Dawn(s:Offset N)(f:Momentum→ℂ)(z:Cover):=april 1 (fun i=> burn (scape z) (moor (glen s i))* low f (moor (glen s i)))
include H
lemma reign : ∃ B:ℝ,0<B∧∀ (z:Cover){N:Side}{s:Offset N},Juno s→∀ x:Gaia,x ≠ 0→‖Dawn s F z x‖ ≤ B*pet 1 x:=by
 obtain ⟨V,c,h⟩:=H.poly; let r:=2*Real.pi; let E:= closedBall (0:Gaia) r; obtain ⟨B,hb⟩:= (show IsCompact E from isCompact_closedBall ..).bddAbove_image c.1.continuous.norm.continuousOn; let G:=max B 1; let A:= r; let W:= Real.exp (A^2); have hp:= Real.pi_pos; have hx:0<A:=mul_pos two_pos hp; have hG:0<G:=lt_max_of_lt_right one_pos; have hW:0<W:=Real.exp_pos _; let B':=G* (5^2)*W
 refine ⟨B',by unfold B'; positivity,fun z {N} {s} g x p=> ?_⟩; let k:= ‖x‖; have hc:0<k:= norm_pos_iff.mpr p; have P:0≤pet 1 x:= by unfold pet tog; positivity
 by_cases e:∃ i:Site N,x∈ pie 1 i; swap; · push Not at e; unfold Dawn; rw [voidX e,norm_zero]; unfold B'; positivity
 obtain ⟨i,u⟩:=e; unfold Dawn; rw [shoutX u,norm_mul,iron,one_mul]; let y:=moor (glen s i); rw [yard_one] at u; have hv :x∈ boundsEarth:= forest i g.even u; unfold low; rw [h y]; let X:= ‖y‖; have hb':0≤blazing y:= fog.nonneg; change ‖(blazing y:ℂ) *_‖ ≤ _
 by_cases a:y=0
 · change ‖_* (V y *↑(pet 1 y))‖≤_; rw [a]; simp only [pet, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, Complex.ofReal_zero, mul_zero,norm_zero]; change 0≤_*pet 1 x; unfold B'; positivity
 rw [norm_mul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ((Complex.norm_real _).trans_le (show ‖blazing y‖ ≤ 1 from (Real.norm_of_nonneg hb').trans_le fog.le_one))); rw [norm_mul]; have hy:‖V y‖≤G:= (hb ⟨y,(mem_closedBall_zero_iff.mpr ((moor_z _).trans (mul_le_mul_of_nonneg_left (show ‖glen s i‖ ≤ Real.pi from orb i s g.even) (by norm_num)))),rfl⟩).trans (le_max_left ..); have ht: pinch N ≤ X:=g.fare i a; have hX:0<X:=norm_pos_iff.mpr a; change ‖V y‖*‖(pet 1 y:ℂ)‖ ≤ _; have h':0≤pet 1 y:=by unfold pet tog; positivity
 rw [Complex.norm_real,Real.norm_of_nonneg h']; apply (mul_le_mul_of_nonneg_right hy h').trans; have hz : k≤ 5*X:=by
    have hv := (norm_le_norm_sub_add x y).trans (add_le_add (moor_s (x:=s) u) (le_refl X)); linarith only [ht,hv]
 let w(x:ℝ):= Real.exp (-(x^2)); have hc'(v:ℝ):0≤w v:=(Real.exp_pos _).le; have ht:w X≤ W*w k:=by
    unfold w W; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; have hz: k≤A:= mem_closedBall_zero_iff.mp (earth_bounded _ hv); nlinarith only [hc,hx,hz,sq_nonneg X]
 have he:pet 1 y≤5^2 * W * pet 1 x:=by
    unfold pet tog; rw [neg_one_mul,neg_one_mul]; change w X/_ ≤ _ * (w k/_); apply (div_le_div_of_nonneg_right ht (sq_nonneg _)).trans; rw [← mul_div_assoc, div_le_div_iff₀ (show 0<X^2 by positivity) (show 0<k^2 by positivity)]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hz 2) (mul_nonneg hW.le (hc' k))).trans_eq (by ring)
 apply (mul_le_mul_of_nonneg_left he hG.le).trans_eq; unfold B'; ring
omit H in
lemma dormit(F: Momentum→ℂ)(s:Offset N)(z:Cover): skyPrice s (fun i=> Lyra.mango F (glen s i)) z= (cartWeight:ℂ) * ∫ x:Gaia,Dawn s F z x:=by
 unfold Dawn; rw [polarX _ one_pos]; change _ *((∑ i,_):ℂ)=_; simp_rw [alias_ch]; have hp:=Real.pi_pos; have he(k:Bin):gloom (moor k)=k:=rfl; unfold low Lyra.mango blazing glad; simp_rw [he]; rw [Complex.real_smul,←mul_assoc]; congr 1; unfold cartWeight pinch; push_cast; have he:(N.val:ℂ)≠0:=by exact_mod_cast N.prop.ne'; -- tune
 have h:(Real.pi:ℂ)≠0:=by exact_mod_cast hp.ne'; -- tune
 field_simp
lemma leaning (N:ℕ→Side)(s:∀ i:ℕ,Offset (N i))(Y:∀ i,Juno (s i))(A:Tendsto (fun i=>(N i).val) atTop atTop)(z:Cover): Tendsto (fun i=> skyPrice (s i) (fun j=> Lyra.mango F (glen (s i) j)) z) atTop (𝓝 (gorge (low F) (scape z))):=by
 let f(i:Gaia):= burn (scape z) i* low F i; obtain ⟨B,h,P⟩:= reign H; let K(i:ℕ):=Dawn (s i) F z; let x:=scape z; have hp: ∀ᵐ x:Gaia, x≠0 := by rw [ae_iff]; simp
 simp_rw [dormit]; unfold gorge; refine Tendsto.const_mul _ ?_; change Tendsto (fun n=> ∫ i, K n i) atTop (𝓝 (∫ i,f i)); apply tendsto_integral_filter_of_dominated_convergence (fun i=> B*pet 1 i) (Eventually.of_forall fun i=> april_a ..) (Eventually.of_forall (fun i=> hp.mono fun j h' => P _ (Y i) j h')) ((pen one_pos).1.const_mul B)
 filter_upwards [hp, ae_all_iff.mpr (fun i=> canopy (Y i).even)] with p p' g; by_cases v: p∈ boundsEarth; swap
 · have hf(n:ℕ): (K n) p=0 :=voidX (fun j w=> v (forest j (Y n).even (yard_one j ▸ w))) _; have hz: blazing p=0:=fog_far (gloom p) (le_of_not_gt (fun y=> v (fun i=> by -- tune blaze to cradle
    have he: |p i|< π/2 :=lt_of_le_of_lt (b_abs (gloom p) i) y; change (p i)∈ Set.Ioc _ _; obtain ⟨hr,ht⟩:=abs_lt.mp he; constructor <;> linarith [Real.pi_pos]))) ; change Tendsto (fun n=> K n p) atTop _; have hh:f p=0:=by simp [f,low,hz]; -- tune
   simp_rw [hf,hh]; exact tendsto_const_nhds
 have he(n:ℕ):∃ k:Site (N n), p∈ cellH k:= Set.mem_iUnion.mp ((show p∈ ⋃ k:Site (N n),cellH k from Eq.mpr (g n) v)); choose k hk using he
 let Z(n:ℕ):= moor (glen (s n) (k n)); have hz:Tendsto Z atTop (𝓝 p) := by rw [tendsto_iff_norm_sub_tendsto_zero]; have he:Tendsto (fun i=> pinch (N i)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp A); exact squeeze_zero (fun n=> norm_nonneg _) (fun n=> (norm_sub_rev ..).trans_le (moor_s (hk n))) (by simpa using he.const_mul 4)
 have hE: ContinuousAt f p:=by obtain ⟨V,hV,t⟩:=H.poly; unfold f low; simp_rw [t]; apply ContinuousAt.mul; unfold burn; fun_prop; apply ContinuousAt.mul; exact (Complex.continuous_ofReal.comp (fog_c.continuous.comp gloom.continuous)).continuousAt; refine ContinuousAt.mul hV.1.continuous.continuousAt (Complex.continuous_ofReal.continuousAt.comp (f:=pet 1) ?_); unfold pet tog; have hv:‖p‖^2≠0:=by positivity; -- tune
                               fun_prop (disch:=assumption)
 refine (hE.tendsto.comp hz).congr (fun i=> Eq.symm (shoutX (F:=_) (show p∈ pie 1 (k i) from by rw [yard_one]; exact hk i))) -- named
end
#print axioms leaning
end YM.Regis.Circuit.SpringDay
