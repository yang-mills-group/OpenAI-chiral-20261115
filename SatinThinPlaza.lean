import SatinThinRunner
import YM.SU5.Selected.Chene.Vantage
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
variable (p:Runner P.J Chi.canonical P.h P.N0 Pay ξC Γϕ Tξ n u P.P)
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
local notation "xt" => hat P.R.L P.x
local notation "M"=> works_X (K:=P.K) Tξ n 6 5 HI Pay ξC Γϕ
-- iteration will use these precise Foots & can drop finitely many too-small tori
structure Panorama (Tξ:Hove.Grant P.K.j 2)(Pay ξC Γϕ:ℝ)(n u:ℕ):Prop where
 scene : ∃ Z W V1 Kf:ℝ→ℝ, BladeQ P.R Z W V1 Kf∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<Y.uv k → let x:=hat P.R.L P.x s; let D:=works_X (K:=P.K) Tξ n 6 5 HI Pay ξC Γϕ;
     Foyer P.V P.U (apt (Y.ir i) P.block P.R.L s) (Stem Y i k s) ((Y.voyage i).CapeT s) ((Y.voyage i).CapeT (s+1)) (RootBook Y i k s) (RootBook Y i k (s+1)) (((Y.voyage i).X (Y.uv k)).wave s).val Chi.canonical P.J.d P.h (V1 x) (Kf x) (W x) D.delta D.f0 D.g0 D.g1 D.g2 (3*dleaf P.R.L x+colorsPhi P.R.L Γϕ x) (colorsPhi P.R.L Γϕ x) (Z x) u
include flag p
lemma sky_Line : Panorama Y Tξ Pay ξC Γϕ n u:=by
 obtain ⟨Z,W,V1,Kf,p',h⟩:=p.pays; refine ⟨Z,W,V1,Kf,p',?_⟩
 filter_upwards [(turnover P).eventually h,(Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop 10] with s w qp
 let v:= Y.meter.a s; let a:= hat P.R.L P.x s; let L:= P.R.L
 let z:=10*(L.val*(4*v.B+2)+2*v.B); filter_upwards [Y.ir_grows.tendsto_atTop.eventually_gt_atTop (max z 4)] with i he k hi
 let m₀:= Y.ir i; let m:= mesh m₀ P.R.L s; let n₁:= mesh m₀ P.R.L (s+1); let Y' := Y.voyage i; let D:=Coord i k; let ρ:= Actual Y.meter Y'.funds Y'.CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k)
 let K:= ρ.toSpine.address s
 obtain ⟨p,b,h,g⟩:= flag i (Y.uv k)
 have hk:=h.toRealQ; let Zq:= ρ; have hh:ρ.active P.P b s=ρ.gram P.P b s:= p.success P.H hk s hi (p.paysStep P.H h s hi)
 have hv:= p.request s hi
 have hG : HavenL (mid m P.block) v P.R.L.val:= by
    let S:= cell m₀ P.block L s; have hp:4 < S.val ∧ z<S.val:=⟨lt_of_lt_of_le ((le_max_right ..).trans_lt he) (amplit ..),lt_of_lt_of_le ((le_max_left ..).trans_lt he) (amplit ..)⟩
    have hx:L.val≥3:=P.R.coarse; have hh: v.B=radiusB a:=hv.boot.B
    exact regularRooms (show 4 ≤ S.val*2 from by omega) (by change 1 < L.val; omega) (hh ▸ qp) (hp.2.trans_le (Nat.le_mul_of_pos_right (S.val) two_pos))
 dsimp only -- let beta shapes
 let E:= w m n₁ K v (Y.meter.a (s+1)) hv (b.read (s+1)).re (ρ.chargeLevel P.P b (s+1)) (ρ.offset P.P b (s+1)) (hat_step s ▸ (p.beta_ok P.H hk _ hi).2) (p.flow (p.charged P.H hk _ hi)) hG
 -- rotate from Board publication
 unfold RootBook; rw [g.gramZ,g.waveZ]; rw [← hh,ρ.gram_fine P.P b s hi]; exact E
end Preparation
end LocalLimit
end YM.CF.Py.Rate
