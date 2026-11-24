import YM.SU5.FiniteGaugeData.Largo.Soda
import YM.CF.Ember.Bud
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat Ember MeasureTheory
open scoped Topology BigOperators Pointwise ENNReal
variable {t:ℝ}{N:Side}
abbrev arena:= Set.Ioc (-Real.pi) Real.pi
abbrev bright:= Set.Icc (-Real.pi) Real.pi
lemma trip_h (k:Per N): volume (hue k)= ENNReal.ofReal (2*pinch N):=by rw [hue,Real.volume_Ioc]; congr 1; ring
lemma slideS (h:Even N.val)(k:Per N): hue k⊆ arena:=fun x p=> ⟨lt_of_le_of_lt (shelf _ h).1 p.1,p.2.trans (shelf _ h).2⟩
private lemma sideWalls: Pairwise (Function.onFun Disjoint (hue (N:=N))) := fun _ _ h=> Set.disjoint_left.mpr (fun _ a b=>h (overlaps a b))
lemma sidesB (h:Even N.val): (⋃ i:Per N,hue i)=ᵐ[volume] arena:=by
 let S:= (⋃ i:Per N,hue i); have he:S⊆ arena:=Set.iUnion_subset (slideS h); have hx: volume S=volume arena:=by
    rw [show S=_ from rfl,measure_iUnion sideWalls (fun i=> measurableSet_Ioc),tsum_fintype]; simp_rw [trip_h]; rw [sum_const,card_univ,arena,Real.volume_Ioc]; rw [nsmul_eq_mul,payH (N:=N),show _-(-(↑N.val*pinch N))=↑N.val*(2*pinch N) from ?_, ENNReal.ofReal_mul (Nat.cast_nonneg _)]; simp [Per,ZMod.card]; ring
 apply ae_eq_set.mpr; refine ⟨ae_le_set.mp (show S ≤ᵐ[volume] arena from Eventually.of_forall fun _ h=> he h),?_⟩; change volume (arena\S)=0
 rw [measure_sdiff he (MeasurableSet.iUnion (fun (i:Per N)=> (show MeasurableSet (hue i) from measurableSet_Ioc))|>.nullMeasurableSet) (hx.symm ▸ (show volume arena ≠ ⊤ from by unfold arena; rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)),hx,tsub_self]
variable (F:ℝ→ℂ) (u: ContinuousOn F bright)
abbrev approach(y:ℝ→ℂ)(N:Side):ℂ:= (N.val:ℂ)⁻¹*(∑ i:Per N,y (Lat.principal i))
def chamber (f:ℝ→ℂ):ℂ:= (τ:ℂ)⁻¹*(∫ x in arena,f x)
lemma inLight (i:Per N): Lat.principal i∈ bright:= Set.Ioc_subset_Icc_self (inZone i)
include u in
lemma cent (r:ℝ)(p:0<r): ∃ n:ℕ,∀ (M:Side), Even M.val → n ≤ M.val→ ‖approach F M-chamber F‖ ≤ r:= by
 obtain ⟨ε,t,H⟩:=Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous u) r p; obtain ⟨n,h⟩:=exists_nat_gt (Real.pi/ε); refine ⟨n,fun M v t'=>?_⟩; let g:=F; let m:= pinch M; let Q:(Per M)→ℂ:= fun i=>F (Lat.principal i); have hx:0<m:= pinch_pos _
 have he: IntegrableOn F arena:= (u.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self; have hp(k:Per M): IntegrableOn F (hue k):= he.mono_set (slideS v k)
 have hw: m < ε:=by unfold m pinch; rw [div_lt_iff₀ (nPos _)]; exact (mul_comm (M.val:ℝ) ε) ▸ (div_lt_iff₀ t).mp (lt_of_lt_of_le h (by exact_mod_cast t' : (n:ℝ)≤_))
 let d:=2*m; have hd:0≤ d:= mul_nonneg (by norm_num) hx.le
 have hz:τ=(M.val:ℝ)*d:=by unfold τ d m; rw [payH (N:=M)]; ring -- unfold m before d?
 have ht (k:Per M) : (∫ x in hue k,F x) - (d:ℂ)*Q k= ∫ x in hue k,F x-Q k:= by rw [integral_sub (hp k) (integrableOn_const (by rw [trip_h]; finiteness)),setIntegral_const,Measure.real,trip_h,ENNReal.toReal_ofReal (by positivity:(0:ℝ)≤d)]; rw [RCLike.real_smul_eq_coe_mul]; rfl
 have ht' (k:Per M): ‖(∫ x in hue k,F x)-(d:ℂ)*Q k‖ ≤ d*r:=by
    rw [ht]; refine (norm_setIntegral_le_of_norm_le_const ?_ (C:=r) (fun x t=> ?_)).trans (le_of_eq ?_) ; · rw [trip_h]; finiteness
    · rw [←dist_eq_norm]; refine le_of_lt (H x (Set.Ioc_subset_Icc_self (slideS v k t)) _ (inLight k) ?_); rw [Real.dist_eq,abs_lt]; obtain ⟨a,g⟩:= t; unfold m at hw; constructor <;> linarith
    rw [Measure.real,trip_h,ENNReal.toReal_ofReal hd]; ring
 have hC:= tau_pos; let Z:= chamber F - approach F M; let A:= (τ:ℂ); let s:= ∑ k:Per M, ((∫ x in hue k, F x)-(d:ℂ)*Q k); have hv:Z=A⁻¹*s:=by unfold Z A approach chamber s Q; rw [setIntegral_congr_set (sidesB v).symm,integral_iUnion_fintype (fun i:Per M=> (show MeasurableSet (hue i) from measurableSet_Ioc)) sideWalls hp, sum_sub_distrib, ←mul_sum, hz]; push_cast; have hu:=nPos M; have hx:0<d:=mul_pos (by norm_num) hx; field_simp [ofReal_ne_zero.mpr hx.ne']
 unfold approach; rw [norm_sub_rev]; change ‖Z‖ ≤ _; rw [hv,norm_mul,norm_inv,show ‖A‖= τ from ?_, inv_mul_eq_div,_root_.div_le_iff₀ hC]; swap; · rw [Complex.norm_real,Real.norm_of_nonneg hC.le]
 refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=>ht' i)).trans (le_of_eq ?_)); rw [sum_const,card_univ,nsmul_eq_mul,hz,show Fintype.card (Per M)=M.val from ZMod.card ..]; ring
variable {m:ℕ→Side}
lemma approach_le (f g:ℝ→ℂ)(M:Side)(p:∀ x∈bright,‖f x-g x‖ ≤ t): ‖approach f M -approach g M‖ ≤ t := by
 unfold approach; rw [←mul_sub,←sum_sub_distrib,_root_.norm_mul,norm_inv,Complex.norm_natCast,inv_mul_eq_div,_root_.div_le_iff₀ (nPos _)]; have he:=sum_le_sum (fun (i:Per M)(_:i∈ univ)=> p _ (inLight i)); simp only [sum_const,nsmul_eq_mul,card_univ,Per,ZMod.card] at he; exact (norm_sum_le ..).trans (he.trans_eq (mul_comm ..))
-- V approx on compact sequentially. no integrability of finite forms needed. only eventual comp. prices.
include u
lemma moneyL (p:∀ i,Even (m i).val)(h:Tendsto (fun i=>(m i).val) atTop atTop) (Q:ℕ→ℝ→ℂ)(H:∀ x∈bright,∀ r:ℕ→ℕ,StrictMono r→∀ y:ℕ→ℝ,(∀ i,y i∈bright)→Tendsto y atTop (𝓝 x)→Tendsto (fun k=>Q (r k) (y k)) atTop (𝓝 (F x))) : Tendsto (fun i=> approach (Q i) (m i)) atTop (𝓝 (chamber F)):= by
 apply Metric.tendsto_nhds.mpr; intro ε t; let e:= ε/4; have he:0<e:=by unfold e; positivity
 obtain ⟨n,V⟩:= cent F u e he
 have hv:∀ᶠ i:ℕ in atTop,∀ z∈bright,‖Q i z-F z‖ ≤ e:= by
    by_contra k; simp_rw [not_eventually] at k; push Not at k; obtain ⟨q,g,v⟩:= extraction_of_frequently_atTop k; choose o r eR using v; obtain ⟨s,g0,k,p,h⟩:= isCompact_Icc.isSeqCompact r; let U:= H s g0 (q ∘ k) (g.comp p) (o∘k) (fun i=>r _) h; have he0:Tendsto (fun i=>‖Q (q (k i)) (o (k i))-F (o (k i))‖) atTop (𝓝 0):=by simpa only [sub_self,norm_zero,Function.comp_apply] using (U.sub ((u s g0).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨h,Eventually.of_forall fun i=>r (k i)⟩))).norm
    obtain ⟨i,v'⟩:= (he0.eventually (ge_mem_nhds he)).exists; exact (not_lt_of_ge v') (eR (k i))
 filter_upwards [hv,h.eventually_ge_atTop n] with i v z; change dist (approach (Q i) (m i)) _ < _; rw [dist_eq_norm]; linarith only [approach_le (Q i) F (m i) v, V (m i) (p i) z, norm_sub_le_norm_sub_add_norm_sub (approach (Q i) (m i)) (approach F (m i)) (chamber F),show e+e<ε from (by unfold e; linarith)]
end YM.CF.Window.Largo
