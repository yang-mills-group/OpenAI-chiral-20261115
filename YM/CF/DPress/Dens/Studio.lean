import YM.CF.DPress.Yarn.Rye
import YM.CF.Continuum.Expanding
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
open Graph Mint Window
namespace Studio
variable {N:Side}
abbrev Card(N:Side):= Finset (Finset (Force N))
abbrev OpT(N:Side):= FC (Single N)
abbrev ActMenu(N:Side):= OpT N × (Force N→OpT N)
abbrev roll (i: Card N)(Y:ActMenu N):OpT N:= exp Y.1 * ∑ j∈ i,(j.toList.map Y.2).prod -- not taking product in FC.D
private lemma Cexp : ContDiff ℝ 1 (exp:OpT N→OpT N):= contDiff_iff_contDiffAt.mpr fun x=> (exp_analytic x).contDiffAt
lemma ℓc(i: List (Force N)): ContDiff ℝ 1 fun y:ActMenu N=> (i.map y.2).prod:=by
 induction i with
 | nil=> exact contDiff_const
 | cons i f ih=> exact ((contDiff_apply ℝ (OpT N) i).comp contDiff_snd).mul ih -- tune comp syntax
lemma roll_diff(i:Card N):ContDiff ℝ 1 (roll i):= (Cexp.comp contDiff_fst).mul (ContDiff.sum fun j _=> ℓc j.toList) -- tune
lemma LipsH(N:Side)(u:ℝ): ∃ C:NNReal,∀ i:Card N,LipschitzOnWith C (roll i) (closedBall 0 u):=by
 letI: ProperSpace (ActMenu N):=FiniteDimensional.proper ℝ _
 choose K h using fun i:Card N=> (roll_diff i).contDiffOn.exists_lipschitzOnWith (show (1:WithTop ℕ∞) ≠ 0 from one_ne_zero) (convex_closedBall (0:ActMenu N) u) (isCompact_closedBall _ _)
 exact ⟨∑ i,K i,fun i=>(h i).weaken (single_le_sum (s:=univ) (f:=K) (fun i _=> bot_le (α:=NNReal)) (mem_univ _))⟩
variable(p:BudgetPoint) (x: Orbit N) (P Q:Yds N) (A:Op (Single N)) (h:IsStarProjection A) {a b z y:ℝ}
local notation "ΠF"=>Finset (Force N)
local notation "θp"=> p.threshold
abbrev flagP : Card N:= univ.filter (fun i: Finset (Force N) => coverF p i x.1 ∧ Set.PairwiseDisjoint (i:Set (Force N)) (fun j=> j.val.1.val.2))
abbrev Menu : ActMenu N:= ⟨tank A (exponentL p P.1 x.1),fun i=> tank A (clamp p i (P.2 i) x)⟩
def BoardV :OpT N:= tank A (exp (exponentL p P.1 x.1)*fueled p P.2 x)
lemma actuator (U:GramM N)(t:U.p=p)(u:U.slip=0):tank A (U.board x)= BoardV p x (budget_at U) A:=by rw [GramM.board,u,Vale.still_Footprint, add_zero,t]; rfl -- budget_at U from Kay
include h
lemma receipt : roll (flagP p x) (Menu p x P A)=BoardV p x P A:=by
 unfold BoardV; rw [Graph.shape A _ _ h]; unfold roll; apply congrArg; let F(j):= clamp p j (P.2 j) x; have hv: fueled p P.2 x=∑ i∈flagP p x,∏ j∈i,F j:=by rw [flagP,Finset.sum_filter]; rfl
 let b:= (nursery A h).cook; rw [hv,tank_eq A _ h,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [←prod_map_toList _ F,map_list_prod,List.map_map]; rfl
lemma menu_Lin : Menu p x (P-Q) A=Menu p x P A-Menu p x Q A:=by
 rw [show ∀ t:Orbit N, Menu p t (P-Q) A= Menu p t P A-Menu p t Q A from ?_]; intro t; apply Prod.ext
 · change tank _ (exponentL _ (P.1-Q.1) _)= tank _ _ - tank _ _; have hP:=Larch.ripe_H p t (P.1-Q.1) Q.1; rw [sub_add_cancel] at hP; rw [eq_sub_of_add_eq hP.symm,tank_eq _ _ h,map_sub]; rfl
 apply funext; intro i; change tank _ (clamp _ i _ _) =tank A (clamp _ i _ _) -tank A (clamp _ i _ _);
 unfold Scree.clamp; by_cases U:boundF i p t.1; · simp only [U, if_true]; change tank A (P.2 i t-Q.2 i t)= _; rw [tank_eq _ _ h,map_sub]; rfl
 simp only [U, if_false, tank_eq _ _ h,map_zero,sub_self]
abbrev M1 (N:Side):ℝ:=(More N).val^4
variable(t:1≤a)
include t
lemma pays(g:AccountY p a P b):‖Menu p x P A‖≤ b* M1 N:=by
 have hp:=g.nn t; have he: 0≤ b*M1 N:=by unfold M1; positivity
 change max (‖tank A (exponentL p P.1 x.1)‖) ‖fun i=>tank A (clamp p i (P.2 i) x)‖ ≤ _; refine max_le ((Graph.billP A _ h t).trans (Graph.toeE g.E (zero_le_one.trans t) x.1)) ((pi_norm_le_iff_of_nonneg he).mpr fun i=>?_ ); refine (Graph.billP A _ h t |>.trans ((Graph.pad (Rosy.kX _ t g.K i) (zero_le_one.trans t) x).trans ?_)); let q:ℝ:=(More N).val; exact le_mul_of_one_le_right hp (one_le_pow₀ (by unfold q; exact_mod_cast (More N).property : 1≤q)) -- tune. Orientation max dimensions.
omit h t
section
-- kine enough.Level.Transport.
theorem banker (p:BudgetPoint)(n:Side)(b:ℝ) : ∃ C:ℝ,0≤C∧∀ {a:ℝ}(P Q:Yds n)(u:1≤a)(η: AccountY p a P b)(y:AccountY p a Q b)(z:ℝ)(t:AccountY p a (Q-P) z)(x:Orbit n)(A:Op (Single n)),IsStarProjection A→ ‖BoardV p x Q A-BoardV p x P A‖ ≤ C*z:=by
 obtain ⟨C,h⟩:=LipsH n (b*M1 n); refine ⟨C * M1 n ,mul_nonneg C.property (by unfold M1; positivity),?_⟩; intro a P Q u v ν z t x A g; let S:=Menu p x Q A; let T:= Menu p x P A
 have he :‖S-T‖≤ z*M1 n:=by unfold S T; rw [←menu_Lin p x Q P A g]; exact pays p x (Q-P) A g u t
 rw [← receipt p x Q A g,← receipt p x P A g,←dist_eq_norm]; refine ((h (flagP p x)).dist_le_mul S (mem_closedBall.mpr ((dist_zero_right _).trans_le (pays p x Q A g u ν))) T (mem_closedBall.mpr ((dist_zero_right _).trans_le (pays p x P A g u v)))).trans ?_; rw [dist_eq_norm]; exact (mul_le_mul_of_nonneg_left he C.property).trans_eq (by change (C.val:ℝ)* (z*M1 n)=(C.val:ℝ)*M1 n*z; ring) -- dist_le_mul likely syntax
end
end Studio
end FitD
end YM.CF.Py.Kay
