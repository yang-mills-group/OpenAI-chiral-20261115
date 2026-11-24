import YM.SU5.Hiro.Crisp
import YM.SU5.Regis.Voyance
/-! cover continuity test (Temperature for arbitrary fixed support). Uses original first-pane SU gauge. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Fock Finset Cube Spire Scroll MeasureTheory Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree Gloss Branch RP Reflect Wilson Lat Rush SU Lat Lattice Precision Tree Tenant Push.SectorMeasure Peaks Tulip Buffered Afterglow Lifted Heat Advance Vale Window
open Reed (Fine)
open Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder ContDiff
attribute [local instance] opCStarAlgebra
open Ballad Metric
variable {N:Side}
abbrev Ono (S:Finset Cover)(x:Edge Cover): Prop:=x.1∈ S∧x.1+step x.2∈ S
def whisk (S:Finset Cover)(U:LinksC):LinksC:=fun x=> if (x.1∈ S∧x.1+step x.2∈ S) then U x else 1
lemma isle_whisk (S:Finset Cover)(U:LinksC): Agrees (S:Set Cover) (whisk S U) U:=fun _ p u=> if_pos ⟨p,u⟩
variable {α:Type*} [TopologicalSpace α](f:LinksC→α)(S:Finset Cover)
lemma certified_brand : Topology.IsEmbedding brand:= (spinD.isClosedEmbedding (fun u v h=> group.mat_injective (congrArg Prod.snd h))).isEmbedding
lemma brush_box {U:Set LinksC}(v:U∈𝓝 1): ∃ e>(0:ℝ),∀ (N:Side)(X:Pane N),Rightful (dBook N S) X 1 e → whisk S (onC N X)∈ U:=by
 by_contra h; push Not at h; let H(n:ℕ):ℝ:= (2:ℝ)⁻¹^n; have hh(n:ℕ):= h (H n) (by unfold H; positivity); choose y u w p using hh
 let B(i):=whisk S (onC (y i) (u i)); have he:Tendsto B atTop (𝓝 1):=by
    refine tendsto_pi_nhds.mpr fun i=>?_ ; by_cases q:Ono S i; swap; · simp_rw [B,whisk,if_neg (show ¬(i.1∈ S ∧ _) from q)]; exact tendsto_const_nhds
    apply certified_brand.tendsto_nhds_iff.mpr; rw [tendsto_iff_dist_tendsto_zero]; apply squeeze_zero (fun i=> dist_nonneg) ?_ (show Tendsto H atTop (𝓝 0) from tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)); intro n; rw [Function.comp_apply,show B n i=_ from (if_pos q : B n i=onC _ (u n) i),dist_eq_norm]; exact tilreal (w n) i.2 i.1 q.1 q.2 -- defeq one pane
 obtain ⟨i,e⟩:= (he.eventually v).exists; exact p _ e
lemma certified_roots (u:LocalOn (S:Set Cover) f)(q:ContinuousAt f 1) {V:Set α}(h:V ∈ 𝓝 (f 1)):
 ∀ᶠ ζ:ℝ in 𝓝[>] (0:ℝ),∀ (N:Side)(U:Pane N),Rightful (dBook N S) U 1 ζ→ f (onC N U)∈V:=by
 obtain ⟨ζ,a,Z⟩:= brush_box S (q.eventually h); filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds a)] with x u0 N U v
 rw [←u _ _ (isle_whisk S (onC N U))]; exact Z _ U (Velvet.loft_rightful v u0 subset_rfl)
lemma flags_one(N:Side): onC N 1=1:=rfl
variable (g:LinksC→ℂ)
def hushL:Weaver:=fun N x=> g (onC N x.1) • 1
lemma hush_coeff (K: Calibration): household K (hushL g)= scalar K (g∘Prod.fst):=rfl
lemma hushPass (u:LocalOn (S:Set Cover) g) (p:Continuous g): Passion (hushL g) S false:=by
 have he:= Coeff.fromC false S p u; let F(x:Side)(V: Fields x):=(g (onC x V.1):ℂ) • (1:FC (Single x)); obtain ⟨C,H⟩:= IsCompact.exists_bound_of_continuousOn (s:=Set.univ) isCompact_univ p.continuousOn
 refine ⟨⟨C,(norm_nonneg (g 1)).trans (H 1 (Set.mem_univ _)),fun n x=>by unfold hushL; rw [norm_smul,norm_one,mul_one]; exact H _ (Set.mem_univ _)⟩,?_, fun N=> ⟨Env.compact (((p.comp (on_cont _)).comp continuous_fst).smul continuous_const),fun a b e y=>congrArg (fun x:ℂ=> x • (1: FC _)) (u _ _ (on_agree _ e)),fun _=> Fine.one.scale _⟩,fun K=> InTest.seed he⟩
 intro e t; filter_upwards [certified_roots (V:=Metric.ball (g 1) e) g S u p.continuousAt (Metric.ball_mem_nhds _ t)] with ζ t N X v _; unfold hushL; rw [←sub_smul,norm_smul,norm_one,mul_one, ←dist_eq_norm,flags_one]; exact (Metric.mem_ball.mp (t N X.1 v)).le
end YM.CF.Hiro
#print axioms YM.CF.Hiro.certified_roots
#print axioms YM.CF.Hiro.hushPass
