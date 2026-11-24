import YM.CF.Atala.Crept
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Err
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
-- abstract regularity lift from affine stencil
section
variable {E F D Q:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup D][NormedSpace ℝ D]{I:Type}[Fintype I][DecidableEq I]
lemma dialX {A:E→Matrix I I ℝ}{p:E}(h:ContDiffAt ℝ (↑l) A p)(g:IsUnit (A p)):ContDiffAt ℝ (↑l) (fun x=>(A x)⁻¹) p∧∀ᶠ x in 𝓝 p,A x*(A x)⁻¹=1:=by
 have ht : ContDiffAt ℝ (↑l) Ring.inverse (A p):=by obtain ⟨u,hu⟩:=g; rw [←hu]; exact contDiffAt_ringInverse ℝ u -- tune
 have hp:= h.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds g)
 constructor; simp_rw [Matrix.nonsing_inv_eq_ringInverse]; exact ht.comp _ h
 filter_upwards [hp] with x p; rw [Matrix.nonsing_inv_eq_ringInverse,Ring.mul_inverse_cancel ..]; exact p -- tune
lemma plod(H:E→ Q→ F)(L:E→Q→ I→ℝ)(x:E) (y:D→E)(X:D)(z:D→Q)(o_ :Q)(p:I→Q)(A:E→ (I→ℝ)→ₗ[ℝ]F)(P:∀ a u,H a u-H a o_= A a (L a u-L a o_))(g:y X=x) (h:IsUnit (Matrix.of (fun i j=> L x (p j) i-L x o_ i))) (hx:ContDiffAt ℝ (↑l) y X)(hf:ContDiffAt ℝ (↑l) (fun i=> L (y i) (z i)) X)(hl:∀ v:Q, ContDiffAt ℝ (↑l) (fun i=> L i v) x)(hp:∀ v:Q, ContDiffAt ℝ (↑l) (fun i=> H i v) x):ContDiffAt ℝ (↑l) (fun v=>H (y v) (z v)) X:=by
 let Z (a:D):= Matrix.of (fun i j=> L (y a) (p j) i-L (y a) o_ i)
 have ht(u:Q):ContDiffAt ℝ (↑l) (fun i=>L (y i) u) X:= (g.symm ▸ hl u).comp X hx
 let KQ : (I→ I→ℝ)≃L[ℝ] Matrix I I ℝ:=(ofLinearEquiv ℝ).toContinuousLinearEquiv
 have he': ContDiffAt ℝ (↑l) (fun x i j=> L (y x) (p j) i - L (y x) o_ i) X:=contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr fun j=>(contDiffAt_pi.mp (ht _) i).sub (contDiffAt_pi.mp (ht _) i)
 have he: ContDiffAt ℝ (↑l) Z X:= KQ.contDiff.contDiffAt.comp X he'
 let S(i:D):=(L (y i) (z i)- L (y i) o_)
 let W(v):=(Z v)⁻¹ *ᵥ S v
 obtain ⟨ht',hf'⟩:=dialX he (by unfold Z; rw [g]; exact h)
 have hk: ContDiffAt ℝ (↑l) W X:=by
    have ht:ContDiffAt ℝ (↑l) S X:= hf.sub (ht _); apply contDiffAt_pi.mpr; intro i; exact ContDiffAt.sum (s:=Finset.univ) fun j _=> (contDiffAt_pi.mp (contDiffAt_pi.mp (KQ.symm.contDiff.contDiffAt.comp X ht') _) j).mul (contDiffAt_pi.mp ht _)
 let M(v):=∑ i,W v i • (H (y v) (p i) - H (y v) o_)
 have hv:F=F:=rfl; have hs(j:Q): ContDiffAt ℝ (↑l) (fun v=> H (y v) j) X:= (g.symm ▸ hp j).comp X hx
 apply ContDiffAt.congr_of_eventuallyEq ((show ContDiffAt ℝ (↑l) M X from ContDiffAt.sum (s:=Finset.univ) (fun j _=> (contDiffAt_pi.mp hk j).smul ((hs _).sub (hs _)))).add (hs o_))
 filter_upwards [hf'] with v hv; change _=M v+_; unfold M; apply sub_eq_iff_eq_add.mp; simp_rw [P,← map_smul]; rw [← map_sum]; apply congr_arg _
 change S v= _; have ht: S v= Z v *ᵥ W v:=by unfold W; rw [mulVec_mulVec,hv,one_mulVec] -- W global
 rw [ht]; ext1 i; rw [Finset.sum_apply]; exact sum_congr rfl fun j _=>mul_comm ..
end
end YM.CF.Err
