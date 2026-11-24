import YM.CF.Cay.Buns
import YM.CF.Souk.Seal
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
open Push.Uniform (lowerCol Primary Positions block Slope bolt)
open Matrix
section corner
variable {ι τ:Type}[Fintype ι][Fintype τ]
abbrev hdot (f:E→A)(q:E):= fderiv ℝ (fderiv ℝ f) q
lemma slog (f:Fish (ι ⊕ τ)→ℝ)(q:Fish (ι ⊕ τ))(x:Fish τ): fderiv ℝ f q (lowerCol x)= (x ⬝ᵥ Slope f q) :=by
 let H:= (fderiv ℝ f q).comp lowerCol; change H x=_; rw [Push.Uniform.by_row]; unfold Slope dotProduct Push.Uniform.entry; simp_rw [H, ContinuousLinearMap.comp_apply,Push.Uniform.lower_bolt,iteratedFDeriv_one_apply]; rfl
lemma stint (f:Fish (ι ⊕ τ)→ℝ)(q:Fish (ι ⊕ τ))(x z:Fish τ): hdot f q (lowerCol x) (lowerCol z) =(z ⬝ᵥ ((block f q) *ᵥ x)):=by
 let U:= hdot f q; have hh(i j:τ):hdot f q (lowerCol (bolt i)) (lowerCol (bolt j))= block f q j i:=by unfold Push.Uniform.block Push.Uniform.entry; rw [Matrix.of_apply,iteratedFDeriv_two_apply]; rw [Push.Uniform.lower_bolt,Push.Uniform.lower_bolt]; rfl
 conv_lhs=>rw [← Push.Uniform.combine x,← Push.Uniform.combine z]
 rw [map_sum,map_sum,_root_.sum_apply]; simp_rw [map_sum,map_smul,_root_.smul_apply,hh]; unfold dotProduct Matrix.mulVec; change (∑ t: τ,∑ i:τ,z i • (x t • (block f q i t)))=(∑ i:τ,z i*(block f q i ⬝ᵥ x)); rw [sum_comm]; unfold dotProduct; simp_rw [mul_sum,smul_eq_mul,mul_comm (x _)]
def heatDot (v: Fish ι): Fish ι →L[ℝ] ℝ:=∑ i:ι,v i • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i -- change def
lemma HD(v w:Fish ι): heatDot v w=v ⬝ᵥ w:=by simp [heatDot, dotProduct,ContinuousLinearMap.sum_apply] -- tune
lemma gradB(f:E→L[ℝ] Fish ι)(x:E): HasFDerivAt (fun i=> (f i ⬝ᵥ f i)/2) ((heatDot (f x)).comp f) x:=by
 let H(i:ι): E→L[ℝ] ℝ:= (ContinuousLinearMap.proj i).comp f; let U(i:ι): E→ ℝ:= fun p=> H i p * H i p
 let z:= f x; let y(p):= (∑ i:ι,U i p)/2; have ht (i:ι): HasFDerivAt (U i) _ x:= (H i).hasFDerivAt.mul (H i).hasFDerivAt
 have hp := (HasFDerivAt.fun_sum (u:=univ) fun i _=> ht i).const_smul ((2:ℝ)⁻¹)
 have he(i:E):(f i ⬝ᵥ f i)/2= (2:ℝ)⁻¹ • (∑ t:ι,U t i):=by change _= (2:ℝ)⁻¹* (f i ⬝ᵥ f i); ring
 simp_rw [he]; rw [show (heatDot (f x)).comp f=(2:ℝ)⁻¹ • (∑ i:ι,(H i x • H i+ H i x • H i)) from ?_]; exact hp
 ext y; simp [heatDot,H,sum_add_distrib]; ring
lemma laySq (Q: E→L[ℝ] Fish ι)(u v:E): let f(i):=(Q i ⬝ᵥ Q i)/2
 ContDiff ℝ ω f ∧ fderiv ℝ f 0=0 ∧ hdot f 0 u v=Q v ⬝ᵥ Q u:=by
 intro z; have hh:ContDiff ℝ ω z:=by unfold z dotProduct; let f(i:ι):= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i).comp Q; exact (ContDiff.div_const (ContDiff.sum (fun i _=> (f i).contDiff.mul (f i).contDiff)) _)
 refine ⟨hh,?_ ,?_⟩
 · rw [(gradB Q 0).fderiv]; ext x; change heatDot _ _=0; rw [HD,map_zero,zero_dotProduct]
 let U:= (heatDot (Q v)).comp Q; have he :(fun y:E=> fderiv ℝ z y v)=U:=by funext y; rw [(gradB Q y).fderiv]; change heatDot _ _= _; rw [HD,dotProduct_comm]; exact (HD _ _).symm
 rw [hdot,Souk.tierX z u v (hh.contDiffAt.of_le le_top), he,U.fderiv]; exact HD _ _
end corner
end YM.CF.Cay
