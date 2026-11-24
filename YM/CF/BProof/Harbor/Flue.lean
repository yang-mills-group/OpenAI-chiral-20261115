import YM.Push.GRID_APPROXIMATION.KernelLocal
import YM.CF.BProof.Harbor.Arbor
import YM.CF.Rill.Peak
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory ProbabilityTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Skye Half Arbor Rush AnalyticBridge.GaussianFieldAlignment
namespace RillW
variable {c f n m:Side} (S:StepData c f) (s:Signed) (b:Site c)
attribute [local instance] Wager.measureVal Wager.billVal
open Wager
local notation "θK"=> SU.group
open Push -- to use GridApprox notation
variable (p:S.patch.Branches S.kernel SU.group)(β:ℝ) (U:Config θK f)
include p
lemma density_E: Envelope (S.density β U):= Law.pull (q:=fun V:Config θK c=>(U,V)) (GridApprox.den_env (S.isKernel p β)) measurable_prodMk_left
variable {E I Y:Type}[Fintype I][DecidableEq I]
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] [MeasurableSpace Y](V:Y→ Config θK f)
abbrev flow_b {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](F: Config θK c → Y)(U: Config θK f):=avg (prior θK c) (S.density β U) F
lemma true_b(v:Y→ Config θK c → E)(h:Envelope (Function.uncurry v))(g:Measurable V):Envelope (fun z=> flow_b S β (v z) (V z)):=by exact Law.fund (f:=fun i:Y × Config θK c=> S.density β (V i.1) i.2 • v i.1 i.2) (prior _ _) (Wager.fee h (Law.pull (q:=fun i:Y × Config θK c=>(V i.1,i.2)) (GridApprox.den_env (S.isKernel p β)) (by fun_prop))) -- tune h uncurry
variable {T:StepData (More n) (More m)}(v:T.patch.Branches T.kernel SU.group)
omit p
include v
lemma lay_cue (F:Pane n→E)(h:Envelope F)(i:Axis)(V:Pane m): flow_b T β (F ∘ Fixed.reflConfig n i) V= flow_b T β F (Fixed.reflConfig m i V):=by
 let X:Pane m:= Fixed.reflConfig m i V; let C:=Fixed.reflConfig n i; let Ψ:= T.density (G:=SU.group) β; have hp(u:Pane n):Ψ X (C u)=Ψ V u:=by have h:= T.channel v (Signed.mirror i) 0 β V u; rw [show T.ratio.embed 0= _ from (map_zero T.ratio.root)] at h; exact h
 refine Eq.trans ?_ (Law.apply_pres (f:=fun x:Pane n=> Ψ X x • F x) (Fixed.reflConfig_preserves n i) ((density_E T v β X).meas.smul h.meas)); change (∫ i, Ψ V i • F (C i) ∂prior _ _)=(∫ i, Ψ X (C i) • F (C i)∂prior _ _); exact integral_congr_ae (Eventually.of_forall fun x=>by dsimp only; rw [hp]) -- representation C
end
variable (X Y0:Set (Site c))
omit p in
lemma priceP (F:Config θK c→ℂ): flow_b S β F U= GridApprox.back S β F U:=by unfold flow_b GridApprox.back avg; simp [Complex.real_smul]
lemma twice {f' g: Config θK c→Op I}(k:Envelope f')(t:Envelope g)(d:Disjoint X Y0)(h: LocalOn X f')(u: LocalOn Y0 g):flow_b S β (fun V=> f' V*g V) U= flow_b S β f' U * flow_b S β g U:=by
 refine Wager.factor k t (density_E S p β U) ?_; intro i j l; let f:=fun x=>f' x i l; let g':=fun x=>g x l j; change flow_b S β (f*g') U= flow_b S β f U * flow_b S β g' U; rw [priceP,priceP,priceP]; exact congrFun (GridApprox.back_factors p (Wager.pane k i l) (Wager.pane t l j) (fun x y p=>congrArg (penny i l) (h x y p)) (fun x y p=> congrArg (penny l j) (u x y p)) d β) U
lemma localB {F:Config θK c→ Op I}(k:Envelope F)(h:LocalOn X F)(Y:Set (Site f))(y:∀ x∈X,GridApprox.window (S.ratio.embed x) (GridApprox.reach S.patch) ⊆ Y): LocalOn Y (flow_b S β F):=by
 intro U V e; ext i j; unfold flow_b; rw [fund (prior ..) k (density_E S p β U),fund (prior ..) k (density_E S p β V)]; let f':=fun x=>F x i j; change flow_b S β f' U=flow_b S β f' V; rw [priceP,priceP]; exact GridApprox.back_local p (Wager.pane k i j) (fun x y p=>congrArg (penny i j) (h x y p)) β Y y U V e
end RillW
end YM.CF.BProof.Bide
