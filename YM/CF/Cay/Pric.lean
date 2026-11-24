import YM.CF.Cay.Top
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open Matrix Far
lemma crank(T:Tube G S)(M:ζ)(q:Chi)(x d β:ℝ)(l:ℕ): ∑ e, spring (adjust T x q d l β) e M= adjust T x q d l β M :=by
 simp_rw [loomU (T:=T) _ _]; let Q:=wrench M x; let U := Q M.z; let P:= fullV T M.key M.park M.k q d x (M.bush x) l M.V*ᵥ U; let K:=Dira T M.key M.park M.k q d x (M.bush x) l M.V; let r:=-(coupling β)⁻¹
 change (∑ e:Bond f,(r*(Q (arrow e M.z) ⬝ᵥ K)- (Q (arrow e M.z) ⬝ᵥ P)/2))=r*(K ⬝ᵥ U)+ (-(U ⬝ᵥ P)/2);
 have hp(v:Prices G (Active M.key x M.park)):(∑ i,(Q (arrow i M.z) ⬝ᵥ v))=U ⬝ᵥ v:=by
    simp_rw [dotProduct_comm _ v,← HD v]; rw [← map_sum,←map_sum,bolt_m]
 rw [sum_sub_distrib, ← mul_sum,hp,← sum_div,hp,dotProduct_comm K]; ring
-- exact extraction independent of receipts. far selection j
lemma massP(T:Tube G S)(M:ζ)(q:Chi)(x d β:ℝ)(l j:ℕ): let S₀:= rush x M.key; let g(s:Signed)(i:Along S):= dense T x q d l β s i;
 -β*averaged (fun s=>∑ i∈ S₀ s j,g s i M) + adjust T x q d l β M= -β*averaged (fun s=>∑ i∈ S₀ s j,g s i (rough M 0))+ -β*averaged (fun s=>∑ i∈ S₀ s j,shotB (g s i) M)+(∑ e:Bond f,opus T x q d l β j e M):=by
 intro Q g; have he : ∀ v:ζ→ℝ,v M=v (rough M 0)+ shotB v M+∑ e,spring v e M:=by
    intro z; rw [bean_m]; let D:=z ∘ rough M; unfold shotB ash; dsimp only [secT]; rw [Function.comp_apply,Function.comp_apply]; rw [show rough M M.z=M from rfl]; ring
 unfold opus; rw [sum_add_distrib,crank]; unfold averaged; let X(s:Signed)(i:Along S)(e:Bond f):=spring (g s i) e M; let A:= ∑ s:Signed,∑ i∈Q s j,g s i (rough M 0); let B:= ∑ s:Signed,∑ i∈Q s j,shotB (g s i) M; let P:= ∑ e:Bond f, ∑ s:Signed,∑ i∈Q s j,X s i e; have hp:(∑ s:Signed,∑ i∈Q s j,g s i M)= A+B+P:=by
    unfold A B P; rw [sum_comm (s:=(univ:Finset (Bond f))) (t:=(univ:Finset Signed)),←sum_add_distrib,←sum_add_distrib]; apply sum_congr rfl; intro s hs; rw [sum_comm (s:=(univ:Finset (Bond f))) (t:=Q s j),← sum_add_distrib,←sum_add_distrib]; exact sum_congr rfl fun i _=>he _
 rw [hp,←mul_sum,←mul_sum]; let t:=(Fintype.card Signed:ℝ)⁻¹; change _*(t*(A+B+P))+_= _*(t*A)+_*(t*B)+(-β*(t*P)+_); ring
end YM.CF.Cay
