import YM.CF.Appel.Test
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open SectorNext.Remainder.Affine Oriented Presented
abbrev globe (S:StepData c f): Window S:=⟨Finset.univ,Finset.univ,Finset.univ,Finset.univ⟩
lemma Gsum(s:Signed)(u:Config G f): (globe S).work T x (pull s 0 u) (choice s k) (pull s 0 V)=Rows.actual T x V k u s:=by unfold Window.work SectorNext.Remainder.onWindow globe Rows.actual; dsimp only; simp_rw [Finset.sum_add_distrib]; abel
lemma gsum {u v w:ℝ}(h:T.up.Bounds T.high v u w)(a:Prices G (Active A x F))(q:Chi): averaged (fun s:Signed=>columns V x k T F A q d Y a s (globe S))= Rows.guide T x V k (shots S x) A F q d Y a:= (Rows.guide_rows _ _ _ _ _ _ _ _ _ _ h a).symm -- tune
-- algebra matching directly within same Y.V
open Rows
lemma chalk(q:Chi)(Y:LinkArray G (Frozen A x F)){β:ℝ}(h:0<β)(hT:T.up.Bounds T.high s v K)(z:Prices G (Active A x F))(he : Offset.b T x k A F q d Y V=blame T x V k (shots S x) A F q d Y) (l:ℕ):
 let M:=credW T A F k q d x Y l V
 let w:=M *ᵥ z
 let g:=coupling β
 let u:=liftN T x V k A F q d Y l
 let a:=u+g • w
 let U:=landed x A F V Y a;
 -β*Rows.fee T x V k A U + (z ⬝ᵥ z)/2= emission T V x A k F q d Y (fun _=>globe S) β u w - g⁻¹ *((Dira T A F k q d x Y l V) ⬝ᵥ z)-(z ⬝ᵥ (fullV T A F k q d x Y l V *ᵥ z))/2:=by
 intro M w g u a U; let R:= gram T x V k (shots S x) A F; let L:=Rows.guide T x V k (shots S x) A F q d Y
 have hx:emission T V x A k F q d Y (fun _=>globe S) β u w= -β*(Rows.fee T x V k A U-L a)-L u/g^2:=by
    unfold emission ownedAt; dsimp only; trace_state; simp_rw [Gsum]; rw [av_sub,exact_fee,gsum hT,gsum hT]
 have hw:= adjusted T x V k (shots S x) A F q d Y (1:Gaussian.Table (Rows.In x A F (G:=G))) u w (coupling_pos h)
 have hR: z ⬝ᵥ (fullV T A F k q d x Y l V*ᵥ z)=w ⬝ᵥ (R *ᵥ w)-z ⬝ᵥ z:=by change z ⬝ᵥ ((M.transpose*R*M-1)*ᵥ z)= w ⬝ᵥ _-_; rw [sub_mulVec,dotProduct_sub,one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,dotProduct_comm _ (M *ᵥ _)] -- tune
 let P:=bankG T A F k q d x Y l V
 have hz:(eta T x V k (shots S x) A F q d Y u g) ⬝ᵥ w= -g⁻¹*((Dira T A F k q d x Y l V) ⬝ᵥ z):=by
    rw [eta,smul_dotProduct]; rw [← he]; congr 1; rw [Dira,dotProduct_comm ((credW T A F k q d x Y l V).transpose *ᵥ _), Matrix.dotProduct_transpose_mulVec] -- tune
 rw [hx,hR]; unfold adjustment at hw; change -L u/g^2+ _+_=force _ w/2-L a/g^2 at hw; rw [hz] at hw; simp only [force, inv_one,Matrix.sub_mulVec, Matrix.one_mulVec,dotProduct_sub] at hw
 have hv : ∀ v:ℝ,v/g^2=β*v:=by intro v; rw [div_eq_mul_inv, show (g^2)⁻¹=β from by_coupling h,mul_comm];
 rw [hv,hv] at hw; rw [hv]; linarith only [hw]
end YM.CF.Appel
