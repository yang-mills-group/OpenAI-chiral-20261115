import YM.SU5.SatinWard.Resolution.Tariff
import Anomaly.Apert.Cotton
import SatinThinScroll

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

open Mew Roots Rive Oise ResolutionFrame Waxy
-- avoid inst lex (this section's layout arbitrary J)
attribute [-instance] instDecidableEqLex
variable {χ:SweepSign n}
section Themes
variable {ε:Type}[Fintype ε]
-- linear-combination THEMES for all later layouts. Needn't be injective.
noncomputable def themes (T:ε→Theme n χ)(r:ε→ℝ): Theme n χ where
 face x E F:=∃ (u:ε→RegBudget n)(v:ε→ForceBudget n), (∀ i,(T i).face x (u i) (v i)) ∧ E=∑ i:ε,r i • u i ∧ F=∑ i:ε,r i • v i
 color:=by
    rintro s p x y _ _ _ _ a ⟨E,F,H,rfl,rfl⟩ ⟨E',F',K,rfl,rfl⟩
    have V (i:ε):=((T i).color s p x y _ _ _ _ a (H i) (K i)); rw [smul_sum,smul_sum]; constructor
    · intro h u; simp_rw [Finset.sum_apply,map_sum]; apply sum_congr rfl; intro i _; rw [smul_comm (χ.sgn s) (r i)]; exact (passingR.smul _ (V i).1 (r i)) h u
    intro h u v; simp_rw [Finset.sum_apply,map_sum]; apply sum_congr rfl; intro i _; rw [smul_comm (χ.sgn s) (r i)]; exact (passingF.smul _ (V i).2 (r i)) h u v

-- keyed layout: every fibre over a root is the same menu.
structure Seating {J:Type}[LinearOrder J][Fintype J] (σ:J→Site n)(Z:J→ε): Prop where
 once(i:J): Bijective fun j:pipe_ζ (Cube.node∘σ) i=> Z (j:J)

variable {J:Type}[LinearOrder J][Fintype J]{σ:J→Site n}{Z:J→ε}(s:Seating σ Z)
noncomputable def seat (j:J): pipe_ζ (Cube.node∘σ) j ≃ ε:= Equiv.ofBijective _ (s.once j)
include s
lemma at_seat (j:J)(k:ε) : σ ((seat s j).symm k)= σ j:=
 node_inj _ (Finset.mem_filter.mp ((seat s j).symm k).property).2
lemma sums_seat {W:Type*}[AddCommMonoid W] (F:J→ W) (i:J): (∑ j∈pipe_ζ (Cube.node∘σ) i,F j)=∑ t:ε,F ((seat s i).symm t):=by rw [← sum_coe_sort]; exact (Equiv.sum_comp (seat s i).symm _).symm -- tune comp_issues
lemma under_seat {W:Type*}[AddCommMonoid W](F:ε→W)(i:J):(∑ j∈pipe_ζ (Cube.node∘σ) i,F (Z j))=∑ t:ε,F t:=by rw [← sum_coe_sort]; exact Equiv.sum_comp (seat s i) F
lemma seat_themes (T:ε→Theme n χ)(r:ε→ℝ)(i:J)
    (E:J→RegBudget n) (K:J→ForceBudget n)(t:∀ j,(T (Z j)).face (σ j) (E j) (K j)) :
 (themes T r).face (σ i) (∑ j∈pipe_ζ (Cube.node∘σ) i,r (Z j) • E j) (∑ j∈pipe_ζ (Cube.node∘σ) i,r (Z j) • K j) := by
 let Y(j): J:= ((seat s i).symm j).val; have hp (j): Z (Y j)=j:= (seat s i).apply_symm_apply _
 refine ⟨E∘Y,K∘Y,fun j=> ?_,?_,?_⟩; · have he:=t (Y j); rw [hp,show σ (Y j)=σ i from at_seat s i j] at he; exact he
 all_goals rw [sums_seat s]; refine sum_congr rfl fun j _=> ?_; rw [show Z _= j from hp j]; rfl
lemma toV_paid (A:J→J→ℂ)(q r:ℝ)(x:Key J)(p:∀ i j, ‖A i j‖≤ q)(g:∀ i,‖x i‖ ≤ r)(h:0≤q)(i:J):‖toV_C (Cube.node∘σ) A x i‖ ≤ (Fintype.card ε:ℝ)*(q*r):=by
 unfold toV_C; apply le_trans (norm_sum_le ..); rw [sums_seat s]; apply le_trans (b:=∑ i:ε,q*r)
 · exact sum_le_sum fun j _=> by rw [norm_mul]; exact mul_le_mul (p ..) (g _) (norm_nonneg _) h
 simp
end Themes

variable {P : Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}{d:ℝ}(V:Grace K l L){U:Grasp V.U B d}
variable {X:GramM (mid N B)}{Y:GramM (mid P B)}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{Xp:Op SU.Slot}{q':Chi}
local notation "cΩ"=> mid N B
local notation "fΩ"=> mid P B
variable {η:Type} [DecidableEq η] [Fintype η] (F:ResolutionFrame ι)
local notation "ΦW"=> Primary ι η
variable {z h Vp Vf T W C BQ Rt Zt b g κp A θ θ' κ D H J₁ J₂ v:ℝ}{Mcap:ℕ}
-- b/g `astro` financial floors. progress footprint includes
-- second Cut budget and min torus Hessian throughout. ℕ width M.
abbrev foyerCap (ε:Type)[Fintype ε](L:Side) :ℝ:= 1+(Fintype.card ε:ℝ)*(sprintCost L*2)
structure SpindleFinance (ι η:Type)[Fintype ι][DecidableEq ι][Fintype η] (F: ResolutionFrame ι)
    (D H:ℝ) (L:Side) (X Y:BudgetPoint) (A θ θ' v h Vf T W BQ Rt Zt κp:ℝ) (Mcap:ℕ):Prop where
 -- θ upper q=t, θ' lower; v total allowance factored by q
 buoy : 0 < θ
 climb : θ ≤ θ'
 climb' : θ' ≤ 2*θ
 live: θ' ≤ 1
 lux: 1 ≤ h
 accr:1 ≤ A
 hedge:8 ≤ X.B
 air: |T| ≤ ResolutionFrame.nullLoss L * θ
 appr:|W|≤ H -- W multiplied by duty
 lease:F.Stretch D
 eUp:1 ≤ H
 premise: RepositoryRent F D H A L
 red:|BQ|≤ H
 blue:|Rt| ≤ H
 green:|Zt|≤ H
 corset₁: (ResolutionFrame.mu L)^4/4≤ Tune.qCorset X.threshold Y.threshold (L.val:ℝ)
 corset₂: Tune.qCorset X.threshold Y.threshold (L.val:ℝ) ≤ 4*(ResolutionFrame.mu L)^4
 rack: 2*A*(Mcap:ℝ)+1 ≤ v
 ink: wish_E X.B κp ≤ θ'
 force: χCut X.B Mcap (foyerCap (Primary ι η) L) Vf ≤ θ'
 panorama: wish_E X.B Vf ≤ θ'
 remain:(foyerCap (Primary ι η) L*θ'⁻¹)*Vf ≤ 2*A
 small: Nice_B X.B Mcap (foyerCap (Primary ι η) L) (1/8)
 large: Nice_B X.B Mcap (foyerCap (Primary ι η) L*θ'⁻¹) (1/8)

variable {I:Type}[LinearOrder I][Fintype I]{F}
variable (R:SpindleFinance ι η F D H l.L X.p Y.p A θ θ' v h Vf T W BQ Rt Zt κp Mcap)
variable {σ:I→Site (mid N B)}{ιz:I→Primary ι η}{U': Primary ι η→ ArcΦ}
variable {E0:Key I→RegBudget (mid P B)}{K0:Key I→ForceBudget (mid P B)}
variable {E':Key I→RegBudget (mid N B)}{K':Key I→ForceBudget (mid N B)}
-- NOTE E'==lower income (Cause) increments relative book. K'= rust not increment.
local notation "tagPlate" => F.enterBasis (η:=η)
local notation "b₀" => (A*θ)
local notation "b₁" => (A*θ')
variable {K_: Reflow ι η} (T_:Economics F D H A l.L X.p Y.p κ θ θ' K_) (Z:Energized F h θ' U' K_)
variable (pay: Cause_P V U G S G₀ G₁ X Y E0 0 K0 Xp q' z h Vp Vf σ (fun _=> A*θ) (F.enterBasis h θ ∘ ιz) E' K' (U'∘ιz) 0 T W C BQ Rt Zt κp)
variable (t: Seating σ ιz) (Q:Force_M X.p.B (Cube.node∘σ) Mcap)(k:|κ|≤Real.exp 1)(Hκ:∀ x : Site (mid P B), nun_ω Y.F x= (κ:ℂ))

abbrev spokes (f:I→Primary ι η) (s:Reflow ι η) (L:Side) := fun i j=> (s.sales L (f i) (f j):ℂ)
local notation "Λ"=>spokes ιz K_ l.L
local notation "workE"=> FlameX σ E' Λ
local notation "workF"=> FlameK σ K' Λ
local notation "pΛ" i:max => pipe_ζ (Cube.node∘σ) i
include R T_ Z pay t k Hκ
lemma wheel_arc (i:I): Axon l.L.val (σ i) X.p (νTip workE i) h (A*θ') (tagPlate h θ' (ιz i)):=by
 let W₁:= σ i; let P₀ := X.p; let Λs(j):= K_.sales l.L (ιz j) (ιz i) -- syntax
 have hm(j:I)(p:j∈ pΛ i) : Axon l.L.val W₁ X.p (νTip E' j) h (F.rentInk A θ h T W κ l.L (ιz j)) (U' (ιz j)):=by
    have t₁:= (pay.pulse j).1; rw [Hκ,show σ j= σ i from node_inj _ (mem_filter.mp p).2] at t₁; exact t₁
 rw [part_Φ V σ E' K' E0 0 K0 Xp _ _ _ _ pay]; unfold spokes; simp_rw [Complex.coe_smul];
 let Λt(i:Primary ι η):=K_.sales l.L i
 refine turf_A _ _ _ _ _ (∑ j∈pΛ i, |Λt (ιz j) (ιz i)| * F.rentInk A θ h T W κ l.L (ιz j)) (A*θ') (?bound) (?axon)
 case axon =>
    rw [← economy_go l.L U' F K_ h θ' Z (ιz i), ← under_seat t (fun j=>Λt j (ιz i) • U' j) i]; apply wave_F; · intro j w; exact real_E (σ i) _ (hm j w) (zero_le_one.trans R.lux)
    exact zero_le_one.trans R.lux
 case bound => rw [under_seat t (fun j:Primary ι η=> |Λt j (ιz i)| * F.rentInk A θ h T W κ l.L j) i]; exact rents_formula R.premise k R.lux R.air R.lease R.accr R.eUp R.buoy R.climb T_ R.appr (ιz i)

variable {φ:Primary ι η→ Theme (mid N B) (F.colors (mid N B))}
abbrev inheritTheme (F:ResolutionFrame ι) (s:Reflow ι η)(L:Side)(φ:Primary ι η→ Theme n (F.colors n))(j:Primary ι η): Theme n (F.colors n) := themes φ (fun i=> s.sales L i j)
omit R T_ Z k Hκ
lemma heirloom (e:∀ i,(φ (ιz i)).face (σ i) (νTip E' i) (emberTip K' i))(i:I): (inheritTheme F K_ l.L φ (ιz i)).face (σ i) (νTip workE i) (emberTip workF i):=by
 rw [part_Φ V σ E' K' E0 0 K0 Xp _ _ _ _ pay,partK σ V E0 0 K0 _ _ E' K' _ _ pay]; unfold spokes; simp_rw [Complex.coe_smul]; exact seat_themes t φ (fun j=> K_.sales l.L j (ιz i)) i _ _ e

-- Income uses H * θ= v* θ exactly. propagate 2 hill for stable boot. θ upper. inputs later relax.
structure Lamps (F:ResolutionFrame ι)(L:Side)(X:GramM (mid N B))(h A v θ width:ℝ)(σ:I→Site (mid N B))(t:I→Primary ι η)(E:Key I→RegBudget (mid N B))(K:Key I→ForceBudget (mid N B))(φ:Primary ι η→Theme (mid N B) (F.colors (mid N B))) : Prop where
 notice : Notice σ E K
 axis(i:I): Axon L.val (σ i) X.p (νTip E i) h (A* θ) (F.enterBasis h θ (t i))
 cover (z:Key I) (w:∀ i,‖z i‖≤ width) : IncX primeU (E z) X.p h (v*θ)∧ Dark primeU (K z) X.p h (v*θ)
 credit(i:I): (φ (t i)).face (σ i) (νTip E i) (emberTip K i)

include R T_ Z k Hκ Q
theorem evolve (e:∀ i,(φ (ιz i)).face (σ i) (νTip E' i) (emberTip K' i)) : Lamps F l.L X h A v θ' 2 σ ιz workE workF (inheritTheme F K_ l.L φ) ∧ PanoramaBill X.p h (2*θ'⁻¹) θ' (2*A) workE workF:=by
 have hg:0≤ b₁ := mul_nonneg (zero_le_one.trans R.accr) (R.buoy.trans_le R.climb).le; let D₂ := (foyerCap ΦW l.L); have hz:= R.buoy.trans_le R.climb; let a:= l.L; let Δ:= sprintCost a; have hp:0≤ Δ:=(sprint_pos ..).le; let c:ℝ:=Fintype.card (Primary ι η); have hc:0≤c:=Nat.cast_nonneg _; have hb:1≤ D₂:=le_add_of_nonneg_right (mul_nonneg hc (mul_nonneg hp (by norm_num)))
 have ht(i j:I):‖Λ i j‖ ≤Δ:=by unfold spokes; rw [Complex.norm_real]; exact economical_bound R.premise T_ (ιz i) (ιz j)
 let S':= tagPlate h θ' ∘ ιz; let ax:= wheel_arc V R T_ Z pay t k Hκ
 refine ⟨⟨flame_notice σ V E0 0 K0 _ _ E' K' _ _ pay Λ,ax,fun z' x=>?_, heirloom V pay t e⟩,fun z' x=>?_⟩
 · obtain ⟨u,y⟩:= double_C X σ Mcap R.lux S' Q V E0 0 K0 _ _ E' K' _ _ pay Λ ax hg R.hedge hb R.small z' x (fun i=>(toV_paid t Λ Δ 2 z' ht x hp i).trans (le_add_of_nonneg_left zero_le_one))
   have hR:= R.rack
   refine ⟨Provides.liftE _ X _ _ u ?_,Provides.liftQ _ X _ _ y ?_⟩; linarith only [mul_le_mul_of_nonneg_right hR hz.le,R.ink]; -- cast
   apply R.force.trans; apply le_mul_of_one_le_left hz.le ((le_add_of_nonneg_left (show 0 ≤ 2*A*Mcap from by have hv:= R.accr; positivity)).trans hR)
 have hx:1≤θ'⁻¹ := (one_le_inv₀ hz).2 R.live
 refine elevated_C X σ Mcap R.lux S' Q V E0 0 K0 _ _ E' K' _ _ pay Λ ax hg R.hedge (one_le_mul_of_one_le_of_one_le hb hx) R.large z' x (fun i=>?_) θ' (2*A) R.ink R.panorama ?_ R.remain
 · refine (toV_paid t Λ Δ (2*θ'⁻¹) z' ht x hp i).trans ?_; change c*(Δ* (2*θ'⁻¹))≤ (1+c*(Δ*2))*θ'⁻¹; nlinarith only [inv_pos.mpr hz]
 rw [show 2 * θ'⁻¹*(A*θ')=2*A by field_simp]
end ShapeLab
end YM.CF.QuadClock
