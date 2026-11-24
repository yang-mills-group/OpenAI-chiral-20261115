import Organdy.Domaine
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Organdy
open Function Filter MeasureTheory Lattice Wilson RG
variable (G : Gauge)
open scoped Matrix.Norms.Frobenius Matrix Topology


private lemma away [Nontrivial G.Color]:∃ v:G.Color, 0<G.chord (G.lieExp v):=by
 obtain ⟨v,j⟩:=exists_ne (0:G.Color)
 have b:Tendsto (· • v:ℝ→G.Color) (𝓝[≠] 0) (𝓝 0):=by
    rw [←zero_smul ℝ v]
    exact tendsto_id.mono_left nhdsWithin_le_nhds|>.smul tendsto_const_nhds
 obtain ⟨t,h,l⟩:=((b.eventually G.plog_left).and self_mem_nhdsWithin).exists
 refine ⟨t•v,div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) (Real.sqrt_pos.mpr (by exact_mod_cast G.dimPos))⟩
 -- tune underscore
 intro g
 rw [g,Gauge.plog_one] at h
 exact smul_ne_zero (by simpa using l : t≠0) j h.symm

private lemma falls (v:G.Color)(τ:ℝ)
   (h:τ*2 < G.chord (G.lieExp v)) (u:G.El):
    ∀ᶠ t:ℝ in 𝓝[≠] 0, G.chord (G.lieExp (t•v) * u) ≠ τ:=by
 by_cases hg:τ<0
 · exact Eventually.of_forall fun i=>ne_of_gt (hg.trans_le (G.chord_nonneg _))
 let Y:ℝ→G.El:=fun t=>G.lieExp (t•v)*u
 let f:ℝ→ℝ:=fun t=>2*(G.price (Y t))
 have an: AnalyticOnNhd ℝ f Set.univ:=by
    intro t a
    let i := Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap

    have k :AnalyticAt ℝ (fun d:ℝ=>i (G.mat (Y d))) t:=by
       unfold Y
       simp only [Gauge.mat_mul,Gauge.mat_lieExp,map_smul]
       let c:=G.colorMat v
       have a:AnalyticAt ℝ (fun d:ℝ=>d•c) t:=analyticAt_id.smul analyticAt_const
       exact (i.analyticAt _).comp (((NormedSpace.exp_analytic _).comp a).mul (analyticAt_const (v:=G.mat u)))
    have q:=k.mul (analyticAt_const (v:=(G.repDim:ℝ)⁻¹))
    unfold f Gauge.price
    simp only [div_eq_mul_inv]
    exact analyticAt_const.mul (analyticAt_const.sub q)
 by_contra! k
 have j:f=(fun _=>τ^2):=an.eq_of_frequently_eq analyticOnNhd_const (k.mono (fun t hv=>(G.chord_price (Y t)).symm.trans (congrArg (· ^ 2) hv)))
 have u0(t):G.chord (Y t)=τ:=
   (sq_eq_sq₀ (G.chord_nonneg _) (le_of_not_gt hg)).mp ((G.chord_price _).trans (congrFun j t))
 have t:=u0 0; have r:G.chord u=τ:=by
    have p:G.lieExp 0=1:=G.mat_injective (by simp [Gauge.mat_lieExp])
    simpa [Y,p] using t
 have i:=G.chord_triangle (Y 1) u⁻¹
 rw [u0,Gauge.chord_inv,r] at i
 have : G.chord (G.lieExp v)≤τ+τ:=by simpa [Y] using i
 linarith only [h,this]

variable {n:Side}
-- one link injection
private def tup (p:Face (Per n))(u:G.El)(X:Config G n):Config G n := fun i=>
   (if i=(p.1,p.2.val.1) then u else 1)* X i
private lemma wet_preserve(p:Face (Per n))(u:G.El):
 MeasurePreserving (tup G p u) (prior G n) (prior G n):=by
 unfold tup
 exact measurePreserving_pi _ _ (f:=fun i x=>
   (if i=(p.1,p.2.val.1) then u else 1)*x)
   fun i=> measurePreserving_mul_left _ _

private lemma wet_paint(p:Face (Per n))(u:G.El)(h:n.val≠1)(X):
 faceValue (tup G p u X) p=u*faceValue X p:=by
 have hx:p.2.val.2 ≠ p.2.val.1 := ne_of_gt p.2.property
 have hs(j:Axis): (step j:Site n)≠0:= by
    intro k
    exact h (ZMod.one_eq_zero_iff.mp (by simpa [step] using congrFun k j))
 simp [faceValue,square,travel, Step.read, Step.used, Step.vec, add_assoc,hs, posDir, negDir, tup,hx, mul_assoc] 
 intro h
 exact (hs p.2.val.2 (by
      rw [←add_assoc] at h
      calc _ = (p.1+step p.2.val.1+step p.2.val.2-step p.2.val.1 : Site n)-p.1 :=by abel
           _=0:=by rw [h,sub_self])).elim

-- endpoint costs via analyticity and dominant convergence
abbrev Drier (τ:ℝ)(U:Config G n):Prop:=∀p:Face (Per n),G.chord (faceValue U p) ≠ τ
lemma drier_paid [Nontrivial G.Color]:∃ d>0, ∀ n:Side, n.val≠1 → ∀ τ<d, ∀ᵐ U ∂prior G n,Drier G τ U:=by
 classical
 obtain ⟨v,h⟩:=away G
 refine ⟨G.chord (G.lieExp v)/2, half_pos h,?_⟩
 intro n h τ j; apply ae_all_iff.mpr; intro p
 let L(t:ℕ):ℝ:=1/(t+1:ℝ)
 have hL:Tendsto L atTop (𝓝[≠] 0):=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_one_div_add_atTop_nhds_zero_nat
       (.of_forall (fun t=>show L t ≠ 0 by unfold L;positivity))
 let μ:=prior G n
 let s:Set (Config G n):={U| G.chord (faceValue U p)=τ}
 let e t:=tup G p (G.lieExp (L t • v))
 have m:MeasurableSet s:=isClosed_eq (by unfold faceValue;fun_prop) continuous_const|>.measurableSet
 have E(t):MeasurePreserving (e t) μ μ:=wet_preserve ..
 let A t:Config G n→ℝ:= ((e t) ⁻¹' s).indicator 1
 have H(t):(∫x,A t x∂μ)= μ.real s:= by rw [show (∫ x,A t x∂μ)=_ from integral_indicator_one ((E t).measurable m), Measure.real,(E t).measure_preimage m.nullMeasurableSet]; rfl

 have k:Tendsto (fun _ :ℕ=> μ.real s) atTop (𝓝 0):=by
    suffices Tendsto (fun t=>∫x,A t x∂μ) atTop
         (𝓝 (∫ _x:Config G n, (0:ℝ) ∂μ)) by simpa [H] using this
    refine tendsto_integral_of_dominated_convergence (fun _=>1) ?_ (integrable_const _) ?_ ?_
    · exact fun t=>(measurable_one.indicator ((E t).measurable m)).aestronglyMeasurable
    · intro t
      filter_upwards with x
      unfold A
      simp [Set.indicator]; split <;> simp
    filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [hL.eventually (falls G v τ ((lt_div_iff₀ zero_lt_two).mp j) (faceValue x p))] with i b
    have g:x∉e i ⁻¹' s:= by change G.chord (faceValue (tup G p _ _) _)≠τ; rw [wet_paint G p _ h]; exact b
    exact (Set.indicator_of_notMem g _).symm
 have k':μ.real s=0:=tendsto_nhds_unique tendsto_const_nhds k
 exact ae_iff.mpr (by simp only [not_not];exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp k')

lemma drier_set(τ:ℝ): MeasurableSet {X:Config G n|Drier G τ X}:=by
 simp only [Drier,Set.setOf_forall]
 refine MeasurableSet.iInter (fun p=> MeasurableSet.compl ?_)
 exact (isClosed_eq (f:=fun x=> G.chord (faceValue x p)) (by unfold faceValue;fun_prop) continuous_const).measurableSet

lemma drier_gauge(τ:ℝ)(g:Site n→G.El)(U):Drier G τ (gauge g U) ↔ Drier G τ U:=by simp [Drier]
