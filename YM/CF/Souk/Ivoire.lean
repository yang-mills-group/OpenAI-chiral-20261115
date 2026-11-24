import YM.CF.Souk.Ken
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort MeasureTheory AnalyticBridge.RelativeLogdet
open Summit Finset
section
variable {f:Fish ι × ℝ→ℝ}{x:Fish ι}
lemma lib_b (j:Fin n→ι) (h:Arc f n x)(p:∀ t∈Isle, |Uniform.entry (fun y=> f (y,t)) x j| ≤ C)(he:0≤C) : |Uniform.entry (fun y=> ∫ t in Isle,f (y,t)) x (j:Fin n →ι)| ≤ C:=by
 let v:= Uniform.bolt (ι:=ι); let W:=List.ofFn j; let Z(t:ℝ):=Ink.over v f W (x,t); let F(y):=∫ t in Isle,f (y,t)
 have hT: W.length=n:= List.length_ofFn
 have he : Arc f W.length x:= hT ▸ h
 have ht: Uniform.entry F x j =∫ t in Isle, Z t:=by
    rw [show Uniform.entry F x j=FreeResolvent.TestD.jet v F W x from (FreeResolvent.Stars.list_result v j F x).symm]; exact he.report v W
 rw [show Uniform.entry _ x j=Uniform.entry F x j from rfl, ht]
 have hp: Arc (Ink.over v f W) 0 x:=fun i hi=> over_smooth _ _ ((h i hi).of_le (by simp [hT]))
 apply le_trans (norm_integral_le_integral_norm (f:=Z) ..); apply le_trans (integral_mono_ae hp.int.norm (integrable_const C) ((ae_restrict_mem (μ:=volume) measurableSet_Icc).mono ?_)) (by simp [Isle,interval]); intro t ht; unfold Ink.over W; dsimp only; erw [FreeResolvent.Stars.list_result]; exact p t ht
end
abbrev ShelfQ(x:Type):=Neige.Shelf x
section price
variable {A:E→ShelfQ τ}{P:E→ℝ → ShelfQ τ}{x:E}
abbrev petX(A:ShelfQ τ)(P:ℝ→ShelfQ τ)(n:ℕ)(t:ℝ):= (A*P t * (tea_r A P t)^n * (1- tea_r A P t)⁻¹).trace
-- tail identity amplitude
lemma gel (A:ShelfQ τ)(P:ℝ→ShelfQ τ)(n:ℕ)(t:ℝ)(h:IsUnit (1-tea_r A P t).det)(hp:IsUnit (edgeM A t).det):
 ((edgeM A t)⁻¹ * A).trace -∑ i∈Finset.range n,(grind A P i t).trace= petX A P n t:=by
 let Z:= tea_r A P t; let U:=edgeM A t; let W:=1-Z; have hZ:(Z * W)= W*Z:=by unfold W; rw [Matrix.sub_mul, Matrix.mul_sub, mul_one, one_mul]
 have he: Z*W⁻¹=W⁻¹* Z:=by calc
    _=W⁻¹*W*Z*W⁻¹:=by rw [Matrix.nonsing_inv_mul _ h,Matrix.one_mul]
    _=_:=by rw [Matrix.mul_assoc W⁻¹,←hZ,←Matrix.mul_assoc W⁻¹,Matrix.mul_assoc (W⁻¹ * Z), Matrix.mul_nonsing_inv _ h,mul_one]
 have hz: A*U⁻¹=A*P t*W⁻¹:=by rw [Matrix.mul_assoc]; apply congr_arg; apply Matrix.inv_eq_right_inv; rw [← Matrix.mul_assoc,show U*P t=W from (sub_sub_cancel ..).symm]; exact Matrix.mul_nonsing_inv _ h -- tune
 let T:=A*P t
 have hK(n:ℕ): A*U⁻¹-(∑ i∈Finset.range n, T*Z^i)= T*Z^n * W⁻¹:=by induction n with
    | zero=>simpa [T] using hz
    | succ i ih=>
       rw [sum_range_succ, ← sub_sub,ih,pow_succ,←Matrix.mul_assoc T,Matrix.mul_assoc (_*_^i)]; let M:= T*Z^i; change M*W⁻¹-M=M*(Z*W⁻¹); have ht:Z*W⁻¹=W⁻¹ -1:=by
        rw [eq_sub_iff_add_eq]; rw [show (1:ShelfQ τ)=W *W⁻¹ from (Matrix.mul_nonsing_inv _ h).symm]; rw [← Matrix.add_mul,show Z+W=1 from by unfold W; abel,Matrix.one_mul]
        -- 
       rw [ht,Matrix.mul_sub,mul_one]
 rw [Matrix.trace_mul_comm]; unfold grind petX; rw [← Matrix.trace_sum, ← Matrix.trace_sub]; exact congr_arg trace (hK n)
def lastT(A:E→ ShelfQ τ)(P:E→ℝ→ShelfQ τ) (n:ℕ)(x:E):= Real.log (1+A x).det-∑ i∈Finset.range n,pulseX (A x) (P x) i
private lemma eclipse (h:Arc (fun u:E × ℝ=>edgeM (A u.1) u.2) n x)(p:∀ t∈Isle,IsUnit (edgeM (A x) t).det):∀ᶠ y in 𝓝 x,∀ t∈Isle, IsUnit (edgeM (A y) t).det:=by
 let P(p:E×ℝ):=edgeM (A p.1) p.2; refine onward (r:=fun z:E×ℝ=> IsUnit (P z).det) fun t ht=>?_ ; have he: ContinuousAt (fun y=>(P y).det) (x,t):= (Loops.det_contDiff.continuous.continuousAt).comp (f:=P) (h t ht).continuousAt; exact (he.eventually (isOpen_ne.mem_nhds (show _≠(0:ℝ) from (p t ht).ne_zero))).mono fun y hy=> isUnit_iff_ne_zero.mpr hy -- tune
lemma petals (h:PriceW A P n x C t)(hp:0≤C)(ht: t ≤1/2)(hg: ContDiffAt ℝ n A x)(l:ℕ):
 let Q(y:E×ℝ):=petX (A y.1) (P y.1) l y.2
 Arc Q n x ∧ lastT A P l =ᶠ[𝓝 x] fun y=>∫ t in Isle,Q (y,t):=by
 intro Q; let U(p:E×ℝ):=1-tea_r (A p.1) (P p.1) p.2; have hh(t':ℝ)(ht':t'∈Isle): IsUnit (U (x,t')).det:=by
    have hp:=h.paid t' ht'; let X:=tea_r (A x) (P x) t'; apply (low_invP _ _).1; rw [show U (x,t')-1=-X by unfold U X; abel,map_neg,norm_neg]; exact hp.2.value.trans ht
 let L: ShelfQ τ→L[ℝ] ℝ:= (Matrix.traceLinearMap τ ℝ ℝ).toContinuousLinearMap
 have hM(l:ℕ): Arc (fun y:E×ℝ=>grind (A y.1) (P y.1) l y.2) n x:=fun t ht=> (h.St t ht).mul ((h.Tag t ht).pow l)
 have hB:Arc U n x:=fun t ht=> contDiffAt_const.sub (h.Tag t ht)
 have hQ: Arc Q n x:=fun t ht=> (L.contDiff.contDiffAt.comp (f:=fun y:E×ℝ=>grind (A y.1) (P y.1) l y.2*(U y)⁻¹) _ ((hM l t ht).mul (AnalyticBridge.RelativeLogdet.reflected (hB t ht) (hh t ht))))
 have hK : ∀ᶠ y in 𝓝 x,∀ t∈Isle, IsUnit (U (y,t)).det := onward (r:=fun z:E×ℝ=> IsUnit (U z).det) (fun t ht=> by
    have he: ContinuousAt (fun y=>(U y).det) (x,t):=(Loops.det_contDiff.continuous.continuousAt).comp (f:=U) (hB t ht).continuousAt
    exact (he.eventually (isOpen_ne.mem_nhds (show _≠(0:ℝ) from (hh t ht).ne_zero))).mono fun y hy=> isUnit_iff_ne_zero.mpr hy)
 let V(z:E×ℝ):=edgeM (A z.1) z.2
 have he: Arc V n x:=fun t ht=> contDiffAt_const.add (contDiffAt_snd.smul (hg.comp _ contDiffAt_fst))
 refine ⟨hQ,?_⟩
 filter_upwards [hK,eclipse he h.heart,h.pre.persists, hQ.persists] with y hy hx hh hF; unfold lastT
 let T:=A y; let Y:= P y
 let F(u:ℝ):=∑ i∈Finset.range l,(grind T Y i u).trace; let Z(u:ℝ):=(V (y,u))⁻¹; let K(u:ℝ):=(Z u*T).trace
 have he(i:ℕ): IntegrableOn (fun t=>(grind T Y i t).trace) Isle:= (tepid T Y hh.slice i).integrableOn_Icc
 have hL: IntegrableOn F Isle:= integrable_finsetSum _ (fun i _=> he i)
 have hSum: ∑ i∈Finset.range l,pulseX T Y i=∫ t in Isle,F t:= (integral_finsetSum _ (fun i _=>he i)).symm; rw [show ∑ i∈Finset.range l,pulseX (A y) (P y) i =_ from hSum]
 have hv: Real.log (1+A y).det= ∫ t in Isle,K t:=by
    have hp:= AnalyticNext.ConnectedActivity.ResolventVolume.invoice 1 T (fun u hu=> (hx u hu).ne_zero); rw [Matrix.det_one, Real.log_one,sub_zero,intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at hp; exact hp.symm
 have hf: EqOn (fun u=> K u) (fun i=> Q (y,i)+F i) Isle:= fun i hi=> sub_eq_iff_eq_add.mp (gel T Y l i (hy i hi) (hx _ hi))
 rw [hv, setIntegral_congr_fun measurableSet_Icc hf,integral_add hF.int hL,add_sub_cancel_right] -- tune
end price
end YM.CF.Souk
