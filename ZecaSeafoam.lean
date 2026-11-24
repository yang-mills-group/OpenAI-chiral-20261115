import ZecaTider
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Finset MeasureTheory Real
open scoped Classical
-- in namespace
structure Wavefront (v:ℕ→ℕ→ℝ):Prop where
 beach : ∀ (h:ℕ→ℝ) (D m C : ℝ),0≤ m → 8*m<C →
    Monotone h → (∀ n,h n ≤ D+m*n)→
    ∃ z:ℕ→ℕ,Tendsto z atTop atTop ∧
       (∀ᶠ r in atTop,Amble h C (z r)) ∧
       ∀ i,Tendsto (fun j=>v i (z j)) atTop (𝓝 0)

/-- a.e. electable with future growth control. -/
lemma waves {U:Type}[TopologicalSpace U][CompactSpace U][MeasurableSpace U][OpensMeasurableSpace U]
 (V:Measure U) [IsFiniteMeasure V]
 (d0:ℕ→ℕ→U→ℝ)(hc:∀ i n,Continuous (d0 i n))(hn:∀ i n x,0≤d0 i n x)
 (h:∀ i,Tendsto (fun n:ℕ=>∫ x,d0 i n x∂V) atTop (𝓝 0)):
  ∀ᵐ x∂V, Wavefront (fun i n=>d0 i n x):=by
 let a:= (1/2:ℝ)
 let d(m n:ℕ)(x:U):= ∑ i ∈ Finset.range m,d0 i n x
 have C'(m n):Continuous (d m n):=continuous_finsetSum _ (fun i _=>hc i n)
 have hp(m n x):0≤d m n x:= Finset.sum_nonneg (fun i _=> hn i n x)
 have hz(m:ℕ): Tendsto (fun n=>∫ x,d m n x∂V) atTop (𝓝 0):= by
    have l:= tendsto_finsetSum (Finset.range m) (fun i (_:i∈Finset.range m)=>h i)
    simp only [Finset.sum_const_zero] at l
    refine l.congr (fun n=> (integral_finsetSum _ (fun i _=>
       (hc i n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm)
 have ha:0<a:=one_half_pos

 have hex(m):∃ n:ℕ,m<n ∧ ∀ i,(∫ x,d m (n+i) x∂V)≤a^m:= by
   obtain ⟨n,lo⟩:=eventually_atTop.mp ((hz m).eventually (ge_mem_nhds (pow_pos ha m)))
   refine ⟨n+m+1,by omega,fun i=>lo _ ?_⟩; omega
 choose e h0 h1 using hex
 let f(m:ℕ)(x:U):=(∑ i ∈ range (e m),d m (e m+i) x)/(e m)
 have g0(m x):0≤f m x:=div_nonneg (sum_nonneg (fun i _=> hp _ _ _)) (Nat.cast_nonneg _)
 have g1(m):(∫ x,f m x∂V)≤a^m:=by
   unfold f
   rw [integral_div, integral_finsetSum]
   · have e0:0<(e m:ℝ):=Nat.cast_pos.mpr ((Nat.zero_le m).trans_lt (h0 m))
     apply (div_le_iff₀ e0).mpr
     apply le_trans (sum_le_sum (fun (i:ℕ) _=>h1 m i))
     simp [mul_comm]
   · exact fun i _=> (C' m (e m+i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have fg(m): Continuous (f m):= Continuous.div_const (continuous_finsetSum _ (fun i _=>C' m (e m+i))) _
 have hg:Tendsto (fun m=>∫ x,f m x∂V) atTop (𝓝 0):=
    squeeze_zero (fun m=>integral_nonneg (g0 _)) g1
       (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le (show a<1 from by norm_num [a]))
 have ht(m):Integrable (f m) V:=
    (fg _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have dx:TendstoInMeasure V f atTop 0:=by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p:=1) one_ne_zero
     (fun m=> (ht m).aestronglyMeasurable) (aestronglyMeasurable_zero)
    have hx:Tendsto (fun m=>ENNReal.ofReal (∫ x,f m x∂V)) atTop (𝓝 (ENNReal.ofReal 0)):=
       ENNReal.continuous_ofReal.continuousAt.tendsto.comp hg
    rw [ENNReal.ofReal_zero] at hx
    refine hx.congr fun m=>?_
    change ENNReal.ofReal (∫x,f m x∂V)= eLpNorm (f m-0) 1 V
    rw [sub_zero,eLpNorm_one_eq_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal (ht m)
       (Eventually.of_forall (g0 _))]
    exact lintegral_congr (fun x=> by rw [← ofReal_norm_eq_enorm,Real.norm_of_nonneg (show 0≤f m x from g0 _ _)])
 obtain ⟨n,ns,r⟩:=dx.exists_seq_tendsto_ae

 have et:Tendsto e atTop atTop:= tendsto_atTop_mono (f:= id) (fun i=>(h0 i).le) tendsto_id
 refine r.mono fun x u => ⟨fun H D m C pm pc hm hb=>?_⟩
 have ux:= et.comp ns.tendsto_atTop
 let b:=e ∘ n
 have l:∀ᶠ r in atTop, ∃ s, b r≤ s ∧ Amble H C s ∧ d (n r) s x≤4*f (n r) x:=by
    filter_upwards [ux.eventually (billow pm pc hm hb)] with r t
    obtain ⟨i,_,Q,v⟩:=t (fun i=>d (n r) (b r+i) x) (fun i=> hp _ _ _)
    exact ⟨_,Nat.le_add_right ..,Q,v⟩
 obtain ⟨r₀,l'⟩:=eventually_atTop.mp l
 have l0:∀r,∃s,r₀≤r → b r≤ s ∧ Amble H C s ∧ d (n r) s x≤4*f (n r) x:=by
   intro r
   by_cases y:r₀≤r
   · obtain ⟨s,t⟩:=l' r y
     exact ⟨s,fun _=>t⟩
   exact ⟨1,fun p=>False.elim (y p)⟩
 choose z t using l0
 have r' := eventually_ge_atTop r₀
 refine ⟨z, tendsto_atTop_mono' atTop (f₁:=b) (r'.mono (fun j p=>(t _ p).1)) ux,
     r'.mono (fun r p=>(t _ p).2.1),fun i=>?_⟩
 change Tendsto (fun r=> f (n r) x) atTop (𝓝 0) at u
 have k:=u.const_mul 4
 rw [mul_zero] at k
 refine squeeze_zero' (Eventually.of_forall (fun _=> hn _ _ _)) ?_ k
 filter_upwards [r',ns.tendsto_atTop.eventually_gt_atTop i] with j p w
 refine le_trans ?_ (t _ p).2.2
 exact Finset.single_le_sum (f:=fun i=>d0 i (z j) x) (fun _ _=>hn _ _ _) (Finset.mem_range.mpr w)
#print axioms waves
#check exists_nat_pow_near
