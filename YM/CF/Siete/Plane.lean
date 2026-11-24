import YM.CF.Siete.Pilot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{P:Teller G}{S: StepData c f}{F: Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support f}{T:Tube G S}{Y:Support c}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z:LogArray G (Active A x F))
variable {a s C J w Q:ℝ}
private def valve (o:Site c)(r:ℕ) : Directions G c →L[ℝ] Directions G c:= ContinuousLinearMap.pi (fun i=> if separation o i.1≤r then ContinuousLinearMap.proj i else 0)
set_option maxHeartbeats 400000 in
lemma swoop{V:Config G c}{P:BudgetPoint}{o:Site c}{R:Type}[NormedAddCommGroup R][NormedSpace ℝ R]{p:Config G c→R}{r:ℕ}(h:P.threshold=temp x)(hv:Allows n (p ∘ Vmove x V) 0 C)(v: ∀ A B:Config G c,AgreeNear id o r A B→p A=p B): Guide _ (P.dirBound o) 0 (p∘ increment V) n (C*((1+(r:ℝ))^(P.power*n))):=by
 let L : Directions G c →L[ℝ] Directions G c:= (temp x)⁻¹ • valve o r
 have he : p ∘ increment V=p ∘ Vmove x V ∘ L:=by
   funext y; apply v; intro i hh; change increment V y i= Vmove x V (L y) i; unfold Vmove; rw [increment,increment, Pi.smul_apply]; congr 2; change _ = _ • ((((temp x)⁻¹:ℝ) • (valve o r) y) i); simp only [valve, Pi.smul_apply, ContinuousLinearMap.pi_apply]; rw [if_pos (show separation o i.1 ≤ r from hh),ContinuousLinearMap.proj_apply,smul_inv_smul₀ (h ▸ P.threshold_pos.ne')]
 rw [he]; -- tune direction
 refine ⟨((show ContDiffAt ℝ (n:ℕ∞ω) (p ∘ Vmove x V) (L 0) from (L.map_zero).symm ▸ hv.smooth).comp (f:=L) 0 L.contDiff.contDiffAt),fun i z g hk=>?_ ⟩
 change ‖iteratedFDeriv ℝ i ((p∘Vmove x V)∘ L) 0 g‖≤_
 rw [Push.Uniform.iter_lin_at (show ContDiffAt ℝ (i:ℕ∞ω) (p∘Vmove x V) (L 0) by rw [map_zero]; exact hv.smooth.of_le (Nat.cast_le.mpr z)),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 let t:= (1+(r:ℝ))^P.power; have ht:∀ i,‖L (g i)‖≤t:=by
    intro i; apply (pi_norm_le_iff_of_nonneg (show 0≤ t by unfold t; positivity)).mpr; intro j; unfold L valve; simp only [ContinuousLinearMap.smul_apply,Pi.smul_apply, ContinuousLinearMap.pi_apply]; split_ifs with l
    · rw [ContinuousLinearMap.proj_apply,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (h▸P.threshold_pos)).le,inv_mul_le_iff₀ (h▸P.threshold_pos)]; rw [←h]; apply (hk i j).trans; unfold t; rw [separation_comm] at l; have hz:=P.threshold_pos.le; gcongr
    simp; unfold t; positivity
 have he:=ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hv.norm_le i z) ht; simp only [prod_const, card_univ,Fintype.card_fin] at he; rw [pow_mul]; exact he.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_pow₀ (by simp)) z) hv.nonneg)
lemma usher (o:Site c)(r:ℕ)(p:RG.BudgetPoint)(h:p.threshold=temp x)(hg:∀ i:I,separation o (incF M i) ≤ r)(V: Config G c) (hr:Ready T x)(hp:1000 ≤ radiusB x)(u:Allows n (traceU T M β k q d l B Z ∘ Vmove x V) 0 C): Guide _ (p.dirBound o) 0 (traceU T M β k q d l B Z ∘ increment V) n (C*((1+((r+(l+50)*radiusB x):ℕ):ℝ)^(p.power*n))):=by
 refine swoop h u ?_; intro U W v; apply getT T M β k q d l B Z hr hp _ _ _ Z (fun _ _=>rfl); intro i; exact v.shrink (Nat.add_le_add_right (hg i) _)
-- ^ exponent cast tune
end YM.CF.Siete
