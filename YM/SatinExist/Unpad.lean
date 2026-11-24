import YM.SatinExist.WeylMeter
import YM.SatinExist.ThermalJet

/-! ## Thermal points in spacetime on the orbit. Limit profile → vacuum-tempered
fields (NOT Y(0) from the original ports, NOT general operator existence). Earn
recovery with exact tune. Spectrum price all. -/
set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "ρ" => volume.restrict (Ioi (0:ℝ))
variable (Y:ℝ → H) (h:Positive S Y)

private lemma monotone_time (u t:ℝ) (Y:ℝ→H) (p:Positive S Y)(hu:0<u)(t':u≤t): ‖Y t‖≤‖Y u‖:= by
 rw [p u t hu t']; exact ((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))

include h
lemma within_time {s:ℝ}(p:0<s) : ContinuousAt Y s:=by
 have he:Y=ᶠ[𝓝 s] (fun x:ℝ=> lifted S Y x):=(lt_mem_nhds p).mono (fun x hp=> (lifted_heat S Y h (show 0<x from hp)).symm)
 exact (((lifted_analytic S Y h _ (show (s:ℂ)∈inside from p)).continuousAt).comp continuous_ofReal.continuousAt).congr he.symm

/-- No p=0 vector assumed. Norm power at one choice m, exponent can depend
    on the field. -/
lemma adding_cost (K:ℝ) (hK:0<K)(p:∀ᶠ e in Λ, ‖Y e‖ ≤ K/e^n):
    ∃ C:H, Tendsto (fun e:ℝ=> StampPower S n (Y e)) Λ (𝓝 C):=by
 obtain ⟨x,t,u⟩:= mem_nhdsGT_iff_exists_Ioc_subset.1 p
 let D:= thermalMass n
 let f(e v:ℝ):= (D v:ℂ) • S.E v.toNNReal (Y e)
 let F(v:ℝ):= (D v:ℂ) • Y v
 let a(v:ℝ):= (thermalMass 0 v) * K + D v * ‖Y x‖
 have g(v:ℝ)(hp:0<v):Tendsto (fun e:ℝ=> f e v) Λ (𝓝 (F v)):=by
   have he(e:ℝ)(u:0<e): f e v = (D v:ℂ) • Y (e+v):=by
     unfold f; rw [h _ _ u (le_add_of_nonneg_right hp.le),add_sub_cancel_left]
   have hx:Tendsto (fun e:ℝ=> e+v) Λ (𝓝 v):=by
     simpa only [zero_add,id] using ((tendsto_id (x:=𝓝 (0:ℝ))).mono_left nhdsWithin_le_nhds).add_const v
   apply ((((within_time S Y h hp).tendsto.comp hx).const_smul (D v:ℂ))).congr'
   filter_upwards [self_mem_nhdsWithin] with i g; exact (he i g).symm
 have hv(v e:ℝ)(h':0<v)(e':0<e): ‖f e v‖ ≤ a v:=by
   have hY:S.E v.toNNReal (Y e)= Y (e+v):=by rw [h e (e+v) e' (le_add_of_nonneg_right h'.le),add_sub_cancel_left]
   have ha:0≤D v:=mass_sign n h'.le
   unfold f; rw [norm_smul,hY, Complex.norm_real,Real.norm_of_nonneg ha]
   apply (mul_le_mul_of_nonneg_left (monotone_time S v (e+v) Y h h' (le_add_of_nonneg_left e'.le)) ha).trans
   unfold a; by_cases hx:v≤x
   · have he: ‖Y v‖≤ K/v^n:= u (show v∈Ioc 0 x from ⟨h',hx⟩)
     refine le_add_of_le_of_nonneg ((mul_le_mul_of_nonneg_left he ha).trans ?_) (mul_nonneg ha (norm_nonneg _))
     unfold D thermalMass; simp only [pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one]
     have hA:1≤(n.factorial:ℝ):=by exact_mod_cast n.factorial_pos
     rw [show Real.exp (-v)*v^n/ (n.factorial:ℝ)*(K/v^n)= Real.exp (-v)*K/(n.factorial:ℝ) from (by field_simp)]
     exact div_le_self (mul_pos (Real.exp_pos _) hK).le hA
   exact le_add_of_nonneg_of_le (mul_nonneg (mass_sign _ h'.le) hK.le) (mul_le_mul_of_nonneg_left (monotone_time S _ _ Y h t (le_of_not_ge hx)) ha)
 refine ⟨∫ v,F v ∂ρ,?_⟩
 have ht:= tendsto_integral_filter_of_dominated_convergence (l:=Λ) a (F:=f)
    (Eventually.of_forall fun i=> (heft S n (Y i)).aestronglyMeasurable)
    (?_ : ∀ᶠ i in Λ,∀ᵐ x ∂ρ, ‖f i x‖ ≤ a x) (((mass_set 0).mul_const K).add ((mass_set n).mul_const _)) ((ae_restrict_mem measurableSet_Ioi).mono fun v hp=> g v hp)
 exact ht
 filter_upwards [self_mem_nhdsWithin] with i h; exact (ae_restrict_mem measurableSet_Ioi).mono (fun x p=> hv x i p h)
omit h

-- normalize Fourier direction to real poses (not a change in P.pitch)

def exchange : Probe E4 →L[ℂ] Probe E4:= (↑(Probe.pref E4):ℂ) • Probe.port
lemma exchange_pay (f:Probe E4): SNAG.cut (exchange f)=f:=by
 unfold exchange SNAG.cut; simp only [_root_.smul_apply,map_smul,Probe.travels,smul_smul, ←ofReal_mul,SNAG.normer,mul_inv_cancel₀ Probe.prepos.ne',ofReal_one,one_smul]

def advancing (v:H): Probe E4 →L[ℂ] H.space:= (tuned S.unit v).comp exchange
lemma advancing_paid (u:Probe E4)(x:H): advancing S x u= SNAG.send S.unit (exchange u) x:= tuned_eq S.unit _ _
lemma advancing_eq (u:Probe E4)(x:H): advancing S x u=∫ p:E4,u p • S.unit.translation p x:= by
 rw [advancing_paid, SNAG.sending,exchange_pay]
lemma step_together (u:Probe E4)(x:H)(t:ℝ≥0): advancing S (S.E t x) u= S.E t (advancing S x u):=by simp only [advancing_paid]; exact DFunLike.congr_fun (adjoin S _ _) x
lemma shifting_points (u:Probe E4)(x:H)(v:E4): advancing S x (Probe.ahead v u)=S.unit.translation v (advancing S x u):=by
 have he:Integrable (fun p:E4=>u p • S.unit.translation p x):=by
    rw [← exchange_pay u]; exact SNAG.over S.unit (exchange u) x
 simp only [advancing_eq]; rw [←ContinuousLinearMap.integral_comp_comm _ he,← integral_add_left_eq_self (fun p:E4=> Probe.ahead v u p • S.unit.translation p x) v]
 congr 1; funext p; rw [map_smul,←ContinuousLinearMap.comp_apply,S.unit.sends,Probe.ahead_at,add_sub_cancel_left]

abbrev VacuumVector (H:Hilbert) := Probe E4 →L[ℂ] H.space
/-- `advancing` uses real Mink positions at standard normalization. `Rim`
 is the prescribed actual boundary also satisfying the heat-back test. -/
structure Rim (W:VacuumVector H) : Prop where
 costs (f:Probe E4) : Tendsto (fun e:ℝ=> advancing S (Y e) f) Λ (𝓝 (W f))
 pays (t:ℝ)(g:0< t)(f:Probe E4): S.E t.toNNReal (W f)=advancing S (Y t) f

include h
lemma unpad (p: VacuumPower Y) : ∃ W: VacuumVector H,Rim S Y W:=by
 obtain ⟨K,d,m,t⟩:=p
 obtain ⟨v,p⟩:= adding_cost S m Y h K d t
 let W:VacuumVector H:= ((tuned S.unit v).comp (winter j m)).comp exchange
 have hF(f:Probe E4):Tendsto (fun e:ℝ=> advancing S (Y e) f) Λ (𝓝 (W f)):=by
    change Tendsto (fun e=> advancing S (Y e) f) _ (𝓝 (tuned S.unit v _)); rw [tuned_eq]
    apply (((SNAG.send S.unit (winter j m (exchange f))).continuous.tendsto _).comp p).congr
    intro e; rw [advancing_paid]; change SNAG.send S.unit (winter j m (exchange f)) (StampPower S m (Y e))=_; rw [← ContinuousLinearMap.comp_apply _ _ (Y e),worth]
 refine ⟨W,hF,fun t d f=>?_⟩
 let a:= t.toNNReal
 have hp:Tendsto (fun i:ℝ=>i+t) Λ (𝓝 t):=by simpa only [zero_add,id] using ((tendsto_id (x:=𝓝 (0:ℝ))).mono_left nhdsWithin_le_nhds).add_const t
 have he : Tendsto (fun i:ℝ=> S.E a (advancing S (Y i) f)) Λ (𝓝 (advancing S (Y t) f)):=by
    simp only [advancing_paid]
    apply (((SNAG.send S.unit (exchange f)).continuous.tendsto _).comp ((within_time S Y h d).tendsto.comp hp)).congr'
    filter_upwards [self_mem_nhdsWithin] with i v
    change SNAG.send S.unit (exchange f) (Y (i+t))= _; rw [h i (i+t) v (by linarith only [d]), add_sub_cancel_left]; exact DFunLike.congr_fun (adjoin S _ _) _
 exact tendsto_nhds_unique ((Continuous.tendsto (S.E a).continuous _).comp (hF f)) he
omit h

variable {S Y}{W:VacuumVector H}
lemma Rim.shifts (G:Rim S Y W)(u:Probe E4)(v:E4): W (Probe.ahead v u)= S.unit.translation v (W u):= by
 let t:ℝ≥0:=1; apply sub_eq_zero.mp; apply S.heat_faithful t
 have hp:= fun x=> G.pays 1 zero_lt_one x
 change _=0; rw [map_sub,sub_eq_zero, ← ContinuousLinearMap.comp_apply _ _ (W u),S.overE, ContinuousLinearMap.comp_apply]; rw [show t=(1:ℝ).toNNReal by simp [t],hp,hp]; exact shifting_points ..

-- one recovery scheme (values Yt) on the entire positive half space, respecting estimates
noncomputable def stamperLet : Probe E4:=
  let B : ContDiffBump (0:E4):= ⟨1,2,by norm_num,by norm_num⟩
  (B.hasCompactSupport.comp_left (show ofReal 0=0 from rfl)).toSchwartzMap (ofRealCLM.contDiff.comp B.contDiff)
lemma stamperLet_self : stamperLet (0:E4)=1:=by
 let B : ContDiffBump (0:E4):= ⟨1,2,by norm_num,by norm_num⟩
 change (B 0:ℂ)=1; rw [B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)]; rfl
noncomputable def homePad (x:ℕ): Probe E4:= SNAG.cut (SNAG.wide stamperLet x)

lemma hears_right (g:Probe E4): exchange (SNAG.cut g)=g:=by
 unfold exchange SNAG.cut; simp only [_root_.smul_apply,map_smul,Probe.comes, smul_smul,←ofReal_mul,SNAG.normer,inv_mul_cancel₀ Probe.prepos.ne', ofReal_one,one_smul]

lemma Rim.reclaim (p:Rim S Y W)(s:ℝ)(d:0<s): Tendsto (fun i:ℕ=> S.E s.toNNReal (W (homePad i))) atTop (𝓝 (Y s)):=by
 simp_rw [p.pays s d, advancing_paid,homePad,hears_right]; exact SNAG.zooms _ _ stamperLet_self _

lemma Rim.exact {Y':ℝ→H}(p:Rim S Y W)(q:Rim S Y' W)(s:ℝ)(d:0<s): Y s=Y' s:= tendsto_nhds_unique (p.reclaim s d) (q.reclaim s d)

-- spectral support on all vacuum vectors
lemma clean_send (S:OS.Semigroup H j) (f:Probe E4) {U:Set E4} (p:∀ v:H, ∀ᵐ x ∂S.ℚmeasure.diagonal v,x∈U)(t:tsupport f ⊆ Uᶜ) : SNAG.send S.unit f=0:=by
 apply symmetrize_eq; intro v; rw [sent_money _ S.joint]; change _=inner ℂ v 0; rw [inner_zero_right]; exact integral_eq_zero_of_ae ( (p v).mono (fun x e=> image_eq_zero_of_notMem_tsupport (fun h=> t h e)))

lemma Rim.clean (p:Rim S Y W)(f:Probe E4){U:Set E4}(h:∀ v:H, ∀ᵐ x ∂S.ℚmeasure.diagonal v,x∈U)(t:tsupport f ⊆ Uᶜ) : W (Probe.hat f)=0:=by
 have hv:= p.pays 1 zero_lt_one (Probe.hat f)
 rw [advancing_paid,exchange,_root_.smul_apply,Probe.comes,map_smul,clean_send S f h t, smul_zero] at hv
 exact S.heat_faithful _ _ hv
lemma Rim.eastern (p:Rim S Y W)(f:Probe E4)(t: tsupport f⊆ {p:E4 | p j<0}) : W (Probe.hat f)=0:=p.clean f (S.bright) (fun x h a=> not_le.mpr (show x j<0 from t h) a)
end YM.SatinJets
