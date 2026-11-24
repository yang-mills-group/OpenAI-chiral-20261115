import YM.CF.Cay.Tear
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
open Matrix AnalyticBridge.RelativeLogdet.Ink
-- Euler jets & application
section
variable {C L M:ℝ}{p:E}
abbrev secT(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (f:E→ℝ)(u:E):= strut f u u
def ash(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (f:E→ℝ)(u:E): ℝ:= f u-f 0-secT E f u
lemma ash_l(L:E→L[ℝ] A)(a:A)(x:E)(f:A→ℝ)(h:ContDiffAt ℝ ((2:ℕ):ℕ∞ω) f a): let F(y):= f (a+L y); fderiv ℝ F 0 x= fderiv ℝ f a (L x) ∧ hdot F 0 x= (hdot f a (L x)).comp L:=by
 intro F; let H(t:A):= f (a+t); have he:ContDiffAt ℝ (2:ℕ) H (L 0):=by
    rw [map_zero]; exact (show ContDiffAt ℝ (2:ℕ) f (a+0) from (add_zero a).symm ▸ h).comp (f:=fun p:A=>a+p) (0:A) (contDiffAt_const.add contDiffAt_id)
 have hp(k:ℕ)(hk:k ≤ 2): iteratedFDeriv ℝ k F 0= (iteratedFDeriv ℝ k f a).compContinuousLinearMap (fun _=> L):=by
    change iteratedFDeriv ℝ k (H ∘ L) 0= _; rw [Push.Uniform.iter_lin_at (L:=L) (he.of_le (by exact_mod_cast hk)),map_zero]; unfold H; rw [iteratedFDeriv_comp_add_left,add_zero]
 constructor
 · rw [show fderiv ℝ F 0 x=iteratedFDeriv ℝ 1 F 0 ![x] from by rw [iteratedFDeriv_one_apply]; rfl, hp _ (by omega), ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_one_apply]; rfl
 ext y; rw [show hdot F 0 x y=iteratedFDeriv ℝ 2 F 0 ![x,y] from by rw [iteratedFDeriv_two_apply]; rfl, hp _ le_rfl,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply]; rfl
lemma expandC (x:E)(f:A→ℝ)(a:A)(L:E→L[ℝ] A)(h:ContDiffAt ℝ ((2:ℕ):ℕ∞ω) f a): let F(y):= f (a+L y);
 ash E F x= f (a+L x)-f a - fderiv ℝ f a (L x)- hdot f a (L x) (L x)/2:=by
 intro F; obtain ⟨hx,hv⟩:=ash_l L a x f h; unfold ash secT strut; rw [hx,hv,ContinuousLinearMap.comp_apply]; unfold F; simp only [map_zero,add_zero]; ring
variable (f:A→ℝ)(n k:ℕ)(x a:E→A)(L M C:ℝ)
def rill (y:A)(v:A):= f (y+v)-f y- tear 1 f y v - tear 2 f y v/2
def ravel (y:A)(v:A):= rill f y v - tear 3 f y v/6
lemma tuneK(L:E→L[ℝ] A)(x:E)(f:A→ℝ)(u:A)(h:ContDiffAt ℝ ((2:ℕ):ℕ∞ω) f u): ash E (fun y=> f (u+L y)) x= rill f u (L x):= expandC x f u L h
lemma rplus(y:A)(x:A): rill f y x+rill f y (-x)= ravel f y x+ravel f y (-x):=by unfold ravel; rw [show tear 3 f y (-x)= -tear 3 f y x from ?_]; ring; simp [tear]
structure MastQ (f:A→ℝ)(x a:E→A) (C M L:ℝ)(p:E)(k n:ℕ): Prop where
 cut : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ (n:ℕ∞ω) x y ∧ Allows n a y L ∧ ∀ u∈ interval,Allows n (fun y=> x y+u•a y) y M ∧ Allows (n+(k+1)) f (x y+u • a y) C
-- structure generated without K? F variables
variable [FiniteDimensional ℝ E]
lemma cubic(h:MastQ f x a C M L p 2 n) : Allows n (fun y=> rill f (x y) (a y)) p ((2^n*L)^3*composeCost n C M):=by
 apply (tale_p f n 2 x a p C M L h.cut).germ; filter_upwards with y; unfold tale rill grade; simp [sum_range_succ,Nat.factorial,tear]; ring
lemma quadT(h:MastQ f x a C M L p 3 n): Allows n (fun y=> ravel f (x y) (a y)) p ((2^n*L)^4*composeCost n C M):=by
 apply (tale_p f n 3 x a p C M L h.cut).germ; filter_upwards with y; unfold ravel rill tale grade; simp [sum_range_succ,Nat.factorial,tear]; ring
end
end YM.CF.Cay
