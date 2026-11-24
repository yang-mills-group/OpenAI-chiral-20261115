import SatinThinPlaza
import Gingham.Linen.Club
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

open Linen
variable (a: InkCover P.J Chi.canonical P.h P.N0 Pay ξC Γϕ Tξ n P.P)
local notation "xt" => hat P.R.L P.x


/-- §XXI (124), charged on the actual Course. Includes Sweep,
    every final D consultation (on PressQ as well), rates 1+10/b. -/
def Plumage : Prop :=
 ∃ C≥(1:ℝ), ∃ d: ℕ, ∀ᶠ s:ℕ in atTop, ∀ (i k:ℕ),
    s < Y.uv k →
    let x := hat P.R.L P.x s
    let R := RootBook Y i k s
    let p := R.p
    Location.Boot x p ∧
    Quills (frosting R.F) p P.h (C*(1+(p.B:ℝ))^d * (Linen.stiffness P.R.L x)) ∧
    R.slip=0

include a
lemma downy: Plumage Y:=by
 obtain ⟨C,e,j,Z⟩:= (poly_nesting (poly_shop P.h)).slope
 refine ⟨C,e,j,?_⟩
 filter_upwards [(turnover P).eventually a.mewl, (turnover P).eventually (high_price P.R.L),
    (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop
       (max 40 (guard_shop P.R.L.val))] with s w ⟨vz,vd,_⟩ qp i k hi
 let v:= Y.meter.a s
 let m₀:= Y.ir i; let m:= mesh m₀ P.R.L s; let n₁:= mesh m₀ P.R.L (s+1); let Y' := Y.voyage i; let ρ:= Actual Y.meter Y'.funds Y'.CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k)
 let K:= ρ.toSpine.address s


 obtain ⟨p,b,h,g,_⟩:= (Y.voyage i).paths (Y.uv k)
 have hk:=h.toRealQ; have hh:ρ.active P.P b s=ρ.gram P.P b s:= p.success P.H hk s hi (p.paysStep P.H h s hi)
 have hv:= p.request s hi
 let E:= w m n₁ K v (Y.meter.a (s+1)) hv (b.read (s+1)).re (ρ.chargeLevel P.P b (s+1)) (ρ.offset P.P b (s+1)) (hat_step s ▸ (p.beta_ok P.H hk _ hi).2) (p.flow (p.charged P.H hk _ hi))
 let X:= RootBook Y i k s
 have hb:v=X.p:=((Coord i k).pull.owns s hi.le).width
 have jg:Glazes X.F X.p P.h (guard_shop P.R.L.val)
             (bill_shop P.h X.p.B):=by
    rw [←hb]
    unfold X RootBook; rw [g, ←hh]
    exact E
 let e0:= hv.boot
 have r: Location.Boot ((xt) s) X.p:= hb ▸ e0
 exact ⟨r,(Glazes.branches r.order (zero_le_one.trans P.height)
           (poly_shop _) (r.B ▸ qp)
           (show Real.exp _ ≤ Linen.stiffness P.R.L ((xt) s) from r.B ▸ vz)
           ((Coord i k).pull.note s hi.le|>.buoy) vd jg).mono
           (mul_le_mul_of_nonneg_right (Z _) ((Real.exp_pos _).le.trans vz)),
        (Coord i k).pull.note s hi.le|>.tone⟩
#print axioms downy

