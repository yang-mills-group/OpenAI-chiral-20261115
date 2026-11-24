import YM.CF.Cay.Atoll
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
open Matrix
open Push.Uniform (lowerCol Primary Positions block Slope bolt)
section affine
variable{ι τ:Type}[Fintype ι][Fintype τ]
lemma affineZ(f:E→ℝ)(p:E)(L:A→L[ℝ] E)(h:ContDiffAt ℝ ω f p)(g:A→ℝ)(ht:ContDiffAt ℝ ω g 0)(r s:ℝ): let a(i):=r*(f (p+L i)-s)+g i
 ContDiffAt ℝ ω a 0 ∧ ∀ (n:ℕ), n≠0→iteratedFDeriv ℝ n a 0=r • (iteratedFDeriv ℝ n f p).compContinuousLinearMap (fun _=> L)+iteratedFDeriv ℝ n g 0:=by
 intro a; let X(v):= f (p+L v)- f p; have hx:a = (r • X+ g)+fun _=>r*(f p-s):=by funext x; unfold X a; change _= r* _+g x+_; ring
 have hA:p+L 0=p:=by simp
 have hH: ContDiffAt ℝ ω X 0:=((show ContDiffAt ℝ ω f (p+L 0) from hA.symm ▸ h).comp (f:=fun x=>p+L x) _ (contDiffAt_const.add (L.contDiff.contDiffAt))).sub contDiffAt_const; have h₁:ContDiffAt ℝ ω (r • X) 0:= contDiffAt_const.smul hH; rw [hx]; refine ⟨(h₁.add ht).add contDiffAt_const,fun i hi=>?_ ⟩
 rw [iteratedFDeriv_add_apply (f:=r • X+ g) ((h₁.add ht).of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne hi,Pi.zero_apply, add_zero, iteratedFDeriv_add_apply (h₁.of_le le_top) (ht.of_le le_top),iteratedFDeriv_const_smul_apply (hH.of_le le_top),iter_affine f p L h i hi]
lemma amass (f:Fish (ι ⊕ τ)→ℝ)(p:Fish (ι ⊕ τ))(M:Neige.Shelf τ)(P:E→L[ℝ] Fish τ)(h:ContDiffAt ℝ ω f p)(r s:ℝ)(ht:0<r)[DecidableEq τ](u v:E): let g:= coupling r; let Q:= fun i:E=> p+lowerCol (g • (M*ᵥ P i)); let a:=fun i=> -r*(f (Q i)-s)+(P i ⬝ᵥ P i)/2
 ContDiffAt ℝ ω a 0 ∧ fderiv ℝ a 0 u=-r*g*(P u ⬝ᵥ (M.transpose *ᵥ Slope f p)) ∧ hdot a 0 u v= -(P v ⬝ᵥ (perturb M (block f p) *ᵥ P u)):=by
 intro g Q a; let U:= lowerCol (ι:=ι) (τ:=τ); let V:= (paintO M).comp P; let F:= fun y=> (P y ⬝ᵥ P y)/2; let L:=U.comp (g•V); obtain ⟨h1,h2,h3⟩:=laySq P u v; obtain ⟨h₁,h₂⟩:= affineZ f p L h F h1.contDiffAt (-r) s
 refine ⟨h₁,?_ ,?_⟩
 · rw [show fderiv ℝ a 0 u=iteratedFDeriv ℝ 1 a 0 ![u] from by rw [iteratedFDeriv_one_apply]; rfl, show iteratedFDeriv ℝ 1 a 0= _ from h₂ 1 (by decide)]; rw [_root_.add_apply,_root_.smul_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]; change -r* (fderiv ℝ f p (lowerCol (g • (M *ᵥ P u)))) + fderiv ℝ F 0 u=_; rw [slog, show fderiv ℝ F 0=0 from h2,_root_.zero_apply,add_zero,Matrix.dotProduct_transpose_mulVec,smul_dotProduct,dotProduct_comm (Slope f p)]; simp only [smul_eq_mul]; ring -- tune
 rw [show hdot a 0 u v=iteratedFDeriv ℝ 2 a 0 ![u,v] from by rw [iteratedFDeriv_two_apply]; rfl, show iteratedFDeriv ℝ 2 a 0= _ from h₂ 2 (by decide)]; rw [_root_.add_apply,_root_.smul_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; let X:= M *ᵥ P u; let Y:=M *ᵥ P v; let H:=block f p; change -r* hdot f p (lowerCol (g • X)) (lowerCol (g • Y))+ hdot F 0 u v=_; rw [stint,h3]; unfold perturb fuseQ; rw [sub_mulVec,one_mulVec,dotProduct_sub, ←mulVec_mulVec,←mulVec_mulVec, dotProduct_transpose_mulVec,mulVec_smul,smul_dotProduct,dotProduct_smul]; rw [show r=(g^2)⁻¹ from (by_coupling ht).symm]; unfold X Y; have he:0<g:=coupling_pos ht; simp only [smul_eq_mul];  rw [dotProduct_comm (M *ᵥ P v)]; field_simp; ring -- tune orientation dot
end affine
end YM.CF.Cay
