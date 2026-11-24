import YM.CF.Stax.Sil
import YM.CF.Yaw.Quartz
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
-- total.Enforced majorant. Batt.Instant α.Gen anchored n0. One PS evaluate.
open PowerSeries Push.AbsoluteSums Trees
-- Calendar at 1.
variable (L s κ a μV c d t α ℓ:ℝ)(b: Palot.leaf (Seat n)→ℝ)
local notation "PX"=> (P.supportExponent)
variable (H:Timer (Cadre.chip (cribR z) r) z κ L μV b s a c d t 1 z)(vα:0<α)(vℓ: 0 ≤ ℓ)(pL:ℓ+α≤ L-μV*1) (μV':1 ≤ h)
-- output
local notation "F₀"=> lamp (P:=P) F K
abbrev Sco(X:VX)(D:Support (More n)):=hitU (N X D)
abbrev ScoL(X:VX)(D:Support (More n)):=hitU (Nd X D)
include H
lemma payG : (∀ X:VX,∀ D ⊆ X.val,Aqua (N X D)) ∧ ∀ i:SA,nook ((roofL (Sco r z) κ)*loom_v L μV b 1) i ≤ a:=by
 let s':=N; have he:= fun (i:SA)(n:ℕ)=>H.book i (1:ℝ) ⟨zero_le_one,le_rfl⟩ n; exact ⟨fun X D p=> (ray s' H.keep κ H.slope L μV b a he X D p).2,fun i=> fort s' H.keep κ H.slope L μV b a he i ⟩
include vα vℓ pL T hF μV'
local notation "δ'"=> (d*a+ s*α⁻¹*a*c)
lemma earnL:(∀ X:VX,∀ D⊆X.val,Aqua (Nd X D))∧∀ i:SA,nook (roofL (ScoL r z) κ*loom_v ℓ 0 b 1) i ≤ d*a+s*α⁻¹*a*c:=by
 have hm(X:VX)(D:Support (More n))(p:D⊆ X.val):0≤r X D:= (hF X D p).merit.wage (zero_le_one.trans μV'); have ht (i:SA)(n:ℕ):serif Nd κ ℓ 0 b i n 1 ≤ d*a+s*α⁻¹*a*c:=(H.worth vα vℓ pL _ (fun _ _ _=>tick_r _ _) (oreL0 z r) i n).trans_eq (one_mul _);
 let f:=Nd; have he(X:VX)(D:Support (More n))(p:D⊆ X.val):cent (f X D):= heatR z r hm T.dice X D; let W:= d*a+s*α⁻¹*a*c
 exact ⟨fun X D p=> (ray f he κ H.slope ℓ 0 b W ht X D p).2,fun i=> fort f he κ H.slope ℓ 0 b W ht i⟩
lemma rentK:(∀ X:VX,∀ D⊆X.val,Fray P h δ X D (F₀ X D) (Sco r z X D)∧Fray P h δ X D (rem_X (P:=P) F K X D) (ScoL r z X D))∧(∀ i:SA,nook (roofL (Sco r z) κ*loom_v L μV b 1) i ≤ a)∧(∀ i:SA,nook (roofL (ScoL r z) κ*loom_v ℓ 0 b 1) i ≤ d*a+s*α⁻¹*a*c):=by
 obtain ⟨v,g⟩:=payG (n:=n) r z L s κ a μV c d t b H; obtain ⟨x,q⟩:=earnL F r hF K z T L s κ a μV c d t α ℓ b H vα vℓ pL μV'
 exact ⟨fun X D h=> ⟨cell F r hF K z T μV' X D (x X D h) h,rem_K F r hF K z T μV' X D h (x X D h)⟩,g,q⟩
lemma blazeV(V:Orbit n)(p:FleetS P.threshold V.1)(A:Op (Single n))(y: Phys n)(W: Op (Single n))(q: IsStarProjection A)(g:Thera.TagG A W)(e: Sea A y)(v:Op SU.Slot)(vx:star v=v)(pM:∑ Y:Aura n,M V Y=Sault.dma A W (-(Tap.plankP n v)) (Dial.tickA n)):let c:=acts (exp (dg W)) y; let Z_:=nursery A q; let D:=flags P.threshold V.1
 acts (Z_.cook (hGas D (hailV D F₀ V))) c=scaleZ v (acts (Z_.cook (hGas D (hailV D F V))) c):=by
 intro C_ U_ D; have ht:= payG (n:=n) r z L s κ a μV c d t b H; have hh:=earnL F r hF K z T L s κ a μV c d t α ℓ b H vα vℓ pL μV'; rw [← print F r hF K z T V p μV' ht.1 A y W q g e v vx pM]; change acts _ _=acts (U_.cook _) C_;  congr 3; apply congrArg (hGas D); exact funext fun x=> (saveK F r hF K z T V p μV' x _ (show D∩x.val=D∩x.val from rfl) (hh.1 _ _ inter_subset_right)).symm -- tune congr
end YM.CF.Stax
