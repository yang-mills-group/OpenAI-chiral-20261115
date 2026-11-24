import YM.CF.Souk.Done
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
variable {X Y: Fish ι→ Neige.Shelf τ}{x:Fish ι}{M:ℝ}
lemma tyLower (h:Vital X x C M)(hp:C ≤1/2):
 let G(y:Fish ι):=1-X y; Vital (fun y=>(G y)⁻¹) x 20 (20*M):=by
 intro G; have h₁: ContDiffAt ℝ 2 G x:=contDiffAt_const.sub h.smooth; have hm:0 ≤ M:= h.chargeM; have hX(i:ℕ)(hi:i<2)(v:Fin (i+1)→ι):= typed_e (h.paidP i hi v) hp le_rfl
 have hv:‖paintO (τ:=τ) (G x -1)‖≤1/2:=by
    rw [show G x-1= -X x from by unfold G; abel,map_neg,norm_neg]; exact h.reader.trans hp
 obtain ⟨hH,hK⟩:=low_invP _ hv; let S(y:Fish ι):= (G y)⁻¹; have ht:ContDiffAt ℝ 2 S x:= ((Loops.inv_contDiffAt _ hH).of_le le_top).comp (f:=G) x h₁
 have hu:(fun y=> S y*G y)=ᶠ[𝓝 x] fun _=>1:=by
    have hh:ContinuousAt (fun y=> Matrix.det (G y)) x:=(Loops.det_contDiff.continuous.continuousAt).comp (f:=G) h₁.continuousAt
    filter_upwards [hh.eventually (isOpen_ne.mem_nhds hH.ne_zero)] with y hy; exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy)
 have hh(n:ℕ)(i:Fin (n+1)→ι): pS (n+1) (fun y=>S y * G y) i x=0:=by unfold pS Uniform.entry; erw [(hu.iteratedFDeriv ℝ (n+1)).eq_of_nhds,iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply]; rfl
 have hj(i:ℕ)(hi:i<2)(j:Fin (i+1)→ι): pS (i+1) G j x=-pS (i+1) X j x:=by unfold pS Uniform.entry G; erw [iteratedFDeriv_sub_apply contDiffAt_const (h.smooth.of_le (by norm_cast)),iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply, zero_sub]; rfl
 let Q:= S x; have hy : G x*Q=1:= Matrix.mul_nonsing_inv _ hH
 have hQ(i:Fin 1→ι): pS 1 S i x=Q*pS 1 X i x*Q:=by
    have hMt:=hh 0 i; rw [fasta_p (ht.differentiableAt (by norm_num)) (h₁.differentiableAt (by norm_num)),hj 0 (by decide) i, mul_neg] at hMt -- tune
    rw [← show pS 1 S i x* G x=Q*pS 1 X i x from by symm; exact eq_of_neg_add_eq_zero hMt,Matrix.mul_assoc,hy,Matrix.mul_one]
 have hw(i:Fin 1→ι):Typed (pS 1 S i x) 2 (4*M):=by
    rw [hQ]
    exact typed_e (wep (wel (hX 0 (by decide) i) hK hm) hK (by positivity)) (by norm_num) (by linarith)
 refine ⟨ht,hK.trans (by norm_num),by positivity,?_⟩; intro i hi j; interval_cases i
 · exact typed_e (hw j) (by norm_num) (by linarith)
 let V:=pS 2 S j x; let U:=pS 2 X j x; let a:Fin 1→ι:=fun _=> j 0; let b:Fin 1→ι:=fun _=> j 1; let L(u:Fin 1→ι):= pS 1 S u x; let Z(q:Fin 1→ι):=pS 1 X q x
 have hd : V=(Q*U+ L a * Z b+ L b * Z a)*Q:=by
    have hp:=hh 1 j; rw [speer_m ht h₁] at hp; change Q*pS 2 G j x+ L a*pS 1 G b x + (L b*pS 1 G a x+ V*G x)=0 at hp; rw [hj 1 (by decide) j,hj 0 (by decide) a,hj 0 (by decide) b] at hp
    simp only [mul_neg] at hp; change -(Q * U) + -(L a*Z b)+ (-(L b*Z a)+V*G x)=0 at hp; rw [←show V*G x=Q*U+L a*Z b+L b*Z a from ?_,Matrix.mul_assoc,hy,mul_one]
    apply sub_eq_zero.mp; rw [←hp]; abel
 change Typed V _ _; rw [hd]; exact typed_e (wep (typed_a (typed_a (wel (hX 1 (by decide) j) hK hm) (wel (hX 0 (by decide) b) (hw a).1 hm)) (wel (hX 0 (by decide) a) (hw b).1 hm)) hK (by positivity)) (by norm_num) (by linarith only [hm])
lemma TraceAt (h: Vital X x C Q)(v: Fin 2→ι):
 let V(y):= (X y).trace
 |Uniform.entry V x v| ≤ Q:=by
 intro V; let L:Neige.Shelf τ→L[ℝ] ℝ:= (Matrix.traceLinearMap τ ℝ ℝ).toContinuousLinearMap
 have hv:Uniform.entry V x v=L (Uniform.entry X x v):=by unfold Uniform.entry; change iteratedFDeriv ℝ _ (L ∘ X) _ _=_; erw [L.iteratedFDeriv_comp_left h.smooth (by norm_num)]; rfl
 rw [hv]; have ht:‖paintO (1:Neige.Shelf τ)‖ ≤ 1:=by rw [paint_one]; exact ContinuousLinearMap.norm_id_le
 have hq:=(h.paidP 1 (by decide) v).2 1; rw [Matrix.mul_one] at hq; exact hq.trans (mul_le_of_le_one_right h.chargeM ht)
end YM.CF.Souk
