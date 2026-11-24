import YM.CF.Taxi.Lane
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open AnalyticBridge.VerifiedReset Push.Local Next.Foundations
variable (X0: Scree.Hub n)(o:Site (More n))(F:Pane n→ℝ)
abbrev villa (X: Scree.Hub n) : Support (More n):= X.val.2 ∪ halo 6 {X.val.1}
def stateT (X:Scree.Hub n):Scree.Hub n:= ⟨ (X.val.1,villa X), mem_union_left _ X.property⟩
local notation "Xp"=> X0.val.2
local notation "Op"=> X0.val.1
abbrev fluxP (x:Scree.Hub n)(F:Pane n→ℝ)(a b:PlaqAxes):= if Nonwrapping (villa x) x.val.1 then AnalyticBridge.VerifiedReset.coeff F x.val.1 a b else 0 -- tune
abbrev fuelC (X:Scree.Hub n)(U:Pane n→ℝ)(y:Skye.Seat n):Pane n→ℝ := motto X.val.1 y • counter (fluxP X U) y (G:=SU.group)
abbrev payout (X:Scree.Hub n)(U:Pane n→ℝ):Pane n→ℝ:= ∑ i: Site (More n),fuelC X U i
lemma shipT(p:motto Op o ≠0): halo 2 {o}⊆ villa X0:=by
 intro i v; obtain ⟨j,h,t⟩:=halo_spec.mp v; rw [mem_singleton.mp h] at t; exact mem_union_right _ (halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle Op o i).trans ((add_le_add (motors _ _ p) t).trans (by norm_num))⟩) -- tune
-- local Pane REAL strict
structure BandS (P:BudgetPoint)(X:Scree.Hub n)(F:Pane n→ℝ)(C:ℝ):Prop where
 regular:(pintK P).Regular X.val.2 F
 toll(V): pingS P.threshold X.val.2 V→Signs P X.val.1 (F ∘ increment V) C
local notation "Z"=> villa X0
open StressFlux
variable {F} (hT:BandS P X0 F c)
include hT
lemma payC (a b:PlaqAxes) : P.threshold^2 * |fluxP X0 F a b|≤c:=by
 have he:= hT.toll 1 (ping_f P Xp); unfold fluxP; split
 next p=>
    let t:= P.threshold; have ht :0 ≤ t:=P.threshold_pos.le
    let w(i:PlaqAxes):=(AnalyticBridge.VerifiedReset.wedge i (spike SU.group)).field Op
    have hw(i):P.dirBound Op (t • w i):=wedge_dir _ _ _ _ (spike_norm Thera.yet_one).le
    have hp(i:Fin 2):P.dirBound Op ((![t • w a,t • w b]:Fin 2→ tangD n) i):=by fin_cases i; exact hw a; exact hw b
    have hq:= he.token 2 (le_trans (by norm_num : 2 ≤ 6) P.order_ge) _ hp; change ‖logHessian F (t • w a) (t • w b)‖ ≤ _ at hq
    change t^2 * |logHessian F (w a) (w b)| ≤ c; rwa [show logHessian F (t • w a) (t • w b)= t^2 * (logHessian F (w a) (w b)) from ?_,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)] at hq; rw [hessian_eq,hessian_eq,map_smul,map_smul,_root_.smul_apply]; simp only [smul_eq_mul]; ring -- tune
 rw [abs_zero,mul_zero]; exact he.grade
omit hT
lemma roseL(k:20+40 < (More n).val)(u:motto Op o≠0)(Q:PlaqAxes→ PlaqAxes→ℝ)(v: LinearJet E')(P:BudgetPoint): logHessian (counter Q o) (v.field Op) (v.field Op)= quad Q v.positive v.positive:=by
 let G:=v.field Op
 have hm (i j:Lattice.Step) := AnalyticBridge.VerifiedReset.Square.plate_deriv i j o Op v (by have ht:= AnalyticBridge.VerifiedReset.Square.near_face o i j; apply Nat.lt_of_le_of_lt _ k; have hh:= (separation_comm _ _).trans_le (motors _ _ u); have h:= separation_triangle (atFace o i j) o Op; omega) (by omega)
 have ht (a:PlaqAxes): HasDerivAt (fun t:ℝ=>petals (AnalyticBridge.VerifiedReset.line G t) o a) (v.positive a) 0:=by
    simp_rw [AnalyticBridge.VerifiedReset.petals,StressFlux.clover,StressFlux.stencil]; refine HasDerivAt.congr_deriv (((hm (posDir _) (posDir _)).sub (hm _ (negDir _))).sub ((hm (negDir _) _).sub (hm _ _))|>.const_smul (4:ℝ)⁻¹) ?_
    dsimp only [StressFlux.flag,posDir,negDir]; simp only [↓reduceIte,one_mul,mul_one,one_smul,neg_mul_neg,neg_one_smul,Bool.false_eq_true]; unfold LinearJet.positive; module
 have he := quad_limit (f:=fun t=> petals (AnalyticBridge.VerifiedReset.line G t) o) (fun i=> normalized_limit (by simp) (ht i)) Q; have hv := hessian_limit Thera.yet_one (counter_regular o Q P) (by simp [counter,AnalyticBridge.VerifiedReset.quad]) G
 have hy:Tendsto (fun t => counter Q o (AnalyticBridge.VerifiedReset.line G t) / t^2) (𝓝[≠] 0) (𝓝 (quad Q v.positive v.positive /2)):= (he.div_const 2).congr (fun t=>by unfold counter; ring)
 change logHessian _ G G= _; linarith only [tendsto_nhds_unique hv hy]
end YM.CF.Taxi
