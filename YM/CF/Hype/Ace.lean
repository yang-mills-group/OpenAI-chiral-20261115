import YM.CF.Pith.Pole
import YM.CF.Bake.Layer
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees Bake Vow
variable (U: Orbit n)
-- sum charges with localized movement.M. countable finite here.lag. Anchor orientation.Lo.Bold. incidence contamination $.Zκ.Translent.
variable {ι:Type*}[DecidableEq ι](R:Finset ι)(X':ι→ Scree.Hub n)(F':ι→InkD n)(v:ι→ℝ)(P:BudgetPoint)(t:ℝ)
-- Archive customers.Print.F.Unit.Ch.Provider.Pres.BETA. helper reorientation.
lemma numb_b(i:Scree.Hub n)(F: InkD n)(x:Orbit n): numbE P.threshold i.val.2 F x.1= Vow.march P (Bake.lagE i) (oV F) x:=by unfold Vow.march; split; exact Set.indicator_of_mem (by assumption) _; rename_i Q; exact Set.indicator_of_notMem (show x.1∉{U|pingS P.threshold i.val.2 U} from Q) _ -- tune
lemma prop_add(X:Scree.Hub n){F G:InkD n}{a b:ℝ}(p:PressB P X F h a)(v:PressB P X G h b):PressB P X (F+G) h (a+b):=by
 obtain ⟨A,g,u,x⟩:=p.worth; obtain ⟨C,k,w,l⟩:=v.worth
 exact ⟨fun i j h=>congrArg₂ (·+·) (p.term i j h) (v.term i j h),fun i=>(p.fitted i).add (v.fitted i),p.measureV.add v.measureV, fun i j=>(congrArg₂ (·+·) (p.gaugeV i j) (v.gaugeV i j)).trans (map_add ..).symm,A+C,fun j=>add_nonneg (g j) (k j),fun i q j=> Prism.tack (u i q j) (w i q j),by simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add x l⟩
lemma prop_sum(X:Scree.Hub n)(p:∀ i∈R,PressB P X (F' i) t (v i)): PressB P X (∑ i∈R,F' i) t (∑ i∈R,v i):=by induction R using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; exact Vale.rinse ..| insert i X' u ih=>rw [sum_insert u,sum_insert u]; exact prop_add P X (p i (mem_insert_self ..)) (ih fun j s=>p j (mem_insert_of_mem s))
-- basic. Labeled not trivial.
abbrev Tumb(R:Finset ι)(X:ι→ Scree.Hub n)(i:Scree.Hub n):Finset ι:=R.filter fun j=>X j=i
abbrev sunY : RegBudget n:=fun i=>∑ j∈ R with X' j=i,F' j
local notation "C'"=> (sunY R X' F')
lemma release_v(U:Orbit n): exponentL P (sunY R X' F') U.1=∑ i∈R,march P (lagE (X' i)) (oV (F' i)) U:=by
 unfold exponentL; rw [←sum_fiberwise_of_maps_to (g:=X') (s:=R) (t:=univ) (fun i _=>mem_univ _)]; apply sum_congr rfl; intro i _; rw [numb_b]; unfold Vow.march; split; swap
 · symm; rename_i z; exact sum_eq_zero (fun j u=> if_neg (by rw [(mem_filter.mp u).2]; exact z))
 rename_i z; unfold oV sunY; rw [Finset.sum_apply]; refine sum_congr rfl fun j u=>?_ ; rw [(mem_filter.mp u).2,if_pos z]
variable(γ':ℝ)(t0:∀ i∈R,PressB P (X' i) (F' i) h (v i))(g:∀ i:Seat n,(∑ j∈R with (X' j).val.1=i,P.mass (X' j).val.2 (v j)) ≤γ')
include t0 g
lemma feat_v: IncX (fun _=>False) (sunY R X' F') P h γ':=by
 refine ⟨⟨fun i=>∑ j∈R with X' j=i,v j,fun i=>prop_sum (Tumb R X' i) F' v P h i fun j q=> (mem_filter.mp q).2 ▸ t0 j (mem_filter.mp q).1,fun i=>?_⟩,fun _ v=>v.elim⟩
 refine (le_trans ?_ (g i)); let U':= R.filter (fun j=>(X' j).val.1=i); rw [←sum_fiberwise_of_maps_to (g:=X') (t:=univ) (s:= U') fun i _=> mem_univ _] -- parentheses
 apply le_of_eq; refine sum_congr rfl fun j _=>?_ ; split_ifs with v'; swap; · rw [show (U'.filter fun i=> X' i=j)=∅ from eq_empty_iff_forall_notMem.mpr fun i p=> (by have he:=(mem_filter.mp (mem_filter.mp p).1).2; rw [(mem_filter.mp p).2] at he; exact v' he.symm),sum_empty]
 unfold BudgetPoint.mass; rw [mul_sum]; apply sum_congr; · ext k; simp only [U', mem_filter]; exact ⟨fun ⟨l,t⟩=>⟨⟨l,(by rw [t]; exact v'.symm)⟩,t⟩,fun g=>⟨g.1.1,g.2⟩⟩ -- tune
 intro i p; rw [(mem_filter.mp p).2]
end YM.CF.Larch
