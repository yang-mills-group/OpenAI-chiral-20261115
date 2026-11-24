import YM.CF.DPress.Chess.Sermon.Stem
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
-- Guide on any signed or real.P.Derivative: physical exact support claim & expression. actual fields sampled jointly both kernels.
def μC (P:Loom n)(x:Orbit n):Stage n:= (x.1,P x)
lemma earn (p:Measurable P):Measurable (μC P):= measurable_fst.prodMk p
local notation "J_"=> Ties SU.group
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][MeasurableSpace V][BorelSpace V][SecondCountableTopology V]
def pad (P:Loom n)(w:Stage m)(x:Orbit n)(F:Forest (ratio K)): Tour K:= (w,x.1,F,P x)
variable [Nonempty (Forest (ratio K))](P:Loom n)
open Fock Finset
local notation "Stx"=> St (ratio K)
def loreC (S:StepData (More n) (More m))(A:Fold K V)(x:Stage m)(β:ℝ)(z:Orbit n):= S.density β x.1 z.1 • ∫ y,A (pad P x z y)∂ St (ratio K)
namespace LoreStage
variable {A:Fold K V}(h:Envelope A)(v:Measurable P)
include h v
lemma spend (p:S.patch.Branches S.kernel SU.group)(x:Stage m)(β:ℝ) : Envelope (loreC P S A x β):=by
 let α(t:Forest (ratio K) × Orbit n):= pad P x t.2 t.1; have he: Measurable α:= measurable_const.prodMk ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk (v.comp measurable_snd))); refine Env.scale (Env.along (den_env (S.isKernel p β)) (g:=fun i:Orbit n=>(x.1,i.1)) (measurable_const.prodMk measurable_fst)) (Env.marginal (Env.along h he) (Stx))
private lemma sump (x:Stage m)(i:Pane n) : sum_T P A x i= ∫ z:Ids n,(∫ y,A (pad P x (i,z) y)∂ St (ratio K))∂depot n:=by
 unfold sum_T; let f(y:Ticket K):=unc_N A x i y; let C:= St (ratio K); let J:= Prod.map (id:(Forest (ratio K))→Forest (ratio K)) (fun z=>P (i,z)); let F j:=f (J j); have ht: MeasurePreserving J (C.prod (depot n)) (νticket (K:=K) P i):=(MeasurePreserving.id _).prod (Robe.lever v i); rw [←expect J ht _ (shelfK h x i).meas]; exact integral_prod_symm F (Env.integrableX (Env.along (shelfK h x i) ht.measurable) _) -- tune rewrite
lemma repurchased (p:S.patch.Branches S.kernel SU.group)(β:ℝ)(x:Stage m): guide S β P A x=∫ z:Orbit n,loreC P S A x β z∂city n:=by
 rw [guide,Transit.card p, integral_prod _ (μ:=prior SU.group (More n)) (Env.integrableX (spend P h v p x β) _)]; refine integral_congr_ae (Eventually.of_forall fun i=>?_); dsimp only; rw [sump P h v]; exact (integral_smul ..).symm
end LoreStage
end YM.CF.DPress.Chess.Sermon
