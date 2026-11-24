import YM.CF.DPress.Chess.Flow.Turn
import YM.CF.DPress.Chess.Planes.Boot
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Transit.Turn
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Finset AnalyticBridge.GaussianFieldAlignment
open Cube (More assembly)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough
open Bough
variable (W:Wall){n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)} (t:S.ratio= ratio K)
private lemma in_turn {n m:Side}{S:StepData n m}(D: Ratio n m)(t:S.ratio=D)(i: Site n)(s:Signed)(P T:Forest D)(x:Site m)(v: Wrap D P (affine s (D.embed i) x)= Wrap D T (affine s (D.embed i) x)) : Wrap D (t▸ Locations.forest s i (t.symm▸ P)) x=Wrap D (t▸ Locations.forest s i (t.symm▸ T)) x:=by
 subst D; apply Prod.ext; · change Step.rotate _ _=Step.rotate _ _; exact congrArg (Step.rotate · s⁻¹) (show P.up _=T.up _ from (congrArg Prod.fst v))
 change P.height _=T.height _; exact congrArg Prod.snd v
lemma worth (X:Support (More n)) : Respects (Counts (ratio K) (W.negZ X)) (Counts (ratio K) X) (ζF W t) :=by
 intro P T h; apply (Bough.holds ..).2; intro i v; change Wrap _ (moveTree ..) i=Wrap _ (moveTree ..) i; apply in_turn (ratio K) t; let A:= W.boost K.count; have he : Wrap _ P (A.site m i)= Wrap _ T (A.site m i):= (Bough.holds ..|>.1 h) _ ((twig_v ..).1 (W.twig_T K S t X ▸ Finset.mem_map_of_mem _ ((twig_v ..).2 v))) -- tune
 unfold Wall.site at he; rw [show A=W.boost K.count from rfl,←W.rod,sitA, show (assembly m).embed (reSweep K _).b=_ from (reA K (W.joy n)).symm] at he; exact he
variable {Z:Type*}[NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z]
-- note type canopy
lemma cash_mean [Nonempty (Forest K)] (F:Forest K→Z): (∫ x,F x∂Bough.St K)= (Fintype.card (Forest K):ℝ)⁻¹ • ∑ i, F i:=by
 unfold St Cash.PM; rw [integral_finsetSum_measure]; swap; · intro i _; exact Integrable.smul_measure (integrable_dirac (by finiteness)) ENNReal.ofReal_ne_top -- check argument
 rw [smul_sum]; refine sum_congr rfl ?_; intro i _; rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ((cashT K).nn i)]
 -- remove
end YM.CF.DPress.Chess.Transit.Turn
