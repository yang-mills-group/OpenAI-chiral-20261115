import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Payment
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Home

/-! # actual city advance and local cap price. No common between-period
trajectory hypothesis. -/
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
open Window SquareScalar
namespace Preparation
open Marks Donor
variable {P: Preparation}{F : (s:Side)→ Scree.Loom s→Prop} (Y:Course P F)
namespace Course
local notation "Ξ" i:max => Y.voyage i
local notation "Gₛ" i:max k:max h:max => (Ξ i).Q k h
local notation "Xj" i:max j:max => cell (Y.ir i) P.block P.R.L j
local notation "γF" i:max j:max => Pane (Xj i j)
local notation "G₀" i:max k:max => (Ξ i).X (Y.uv k)
local notation "Xm" i:max j:max => (Ξ i).CapeT j
variable (j:ℕ)
open FullBill Push.GridApprox
-- costed threshold to apply theorem
abbrev radiusPrice (j r:ℕ) := 1+mural (SquareScalar.tile P.block P.R r) (Y.thermal j)
theorem at_home : ∀ᶠ k in atTop, j < buoy (Y.ivory k) ∧ ∀ i, ∀ _p:(Y.voyage i).kick ≤ k, ∀ r:ℕ, SquareScalar.tile P.block P.R r ≤ (Xj i j).val → ∀ (w:ℝ) (A:Pane (Xj i j)→ℂ), Cells.Interior (window 0 r) A →
    (∀ t,‖A t‖ ≤ w) → ‖Y.texture i k j (bosonic (Xj i j) A)‖ ≤ Y.radiusPrice j r*w := by
 filter_upwards [Y.gauge_bill j] with k v
 refine ⟨v.1,?_⟩; intro i p r he w B h Ω; let b:=tickBox P.R r; let rB:=2*P.block.val; let U:=traceOfWalk P.block (Xj i j); let A':= B ∘ U b
 have ht:B=A' ∘ U (-b):= by
    ext t:1; apply congrArg B; unfold U traceOfWalk; rw [smul_neg, back_home]
 rw [ht]; exact v.2 i p _ (tile_dvd ..) (tile_pos ..) he w A' (canvas P.block P.R r B h w Ω) (-b)
variable (i k:ℕ)
open Period Window Push.GridApprox
abbrev visit : Session P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ P.x (Y.ir i) (Y.uv k) :=
  let x:=(Ξ i).X (Y.uv k); ⟨Y.meter,(Ξ i).funds,x.pilot,x.gram,(Ξ i).CapeT,x.wave,x.fee,Y.history i k⟩
local notation "T" => Carousel.standard P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ (Y.visit i k)
abbrev stepData (j:ℕ) := Carousel.buoyG P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ (Carousel.standard P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ (Y.visit i k)) j
abbrev beta (j:ℕ) := ((G₀ i k).gram (j+1)).beta
abbrev lyric (j:ℕ) := Carousel.garner P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ (Carousel.standard P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ (Y.visit i k)) j
lemma pilot_steps : let g:= Y.stepData i k j; g.patch = P.R ∧ g.kernel=P.K.bind ∧ g.patch.Branches g.kernel SU.group := by intro g; have he:= Carousel.actualG P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ T j; exact ⟨he.1,rfl,he.2.2⟩
local notation "Kz" => (Y.beta i k j)
lemma singer (p:j < Y.uv k)(X:Pane (cell (Y.ir i) P.block P.R.L j)→ℂ)(u:Envelope X) : Y.texture i k j (bosonic (Xj i j) X) = Y.texture i k (j+1) (bosonic (Xj i (j+1)) (Y.lyric i k j X)) := Carousel.hhgo P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ T _ p X u
-- dummy ABI for the smoothing estimate over all pilots below. Uses effective penalty only.
def dummy (P:Preparation) : StepData 1 P.R.L:=⟨P.R,P.K.bind,(by simp)⟩
abbrev ceiling (P:Preparation)(j:ℕ) := 2*hat P.R.L P.x (j+1)
lemma seated(p : j< Y.uv k) : Y.beta i k j ∈ Set.Icc (-(ceiling P j)) (ceiling P j) := by
 have hp:= (T).sift (j+1) p; obtain ⟨q,u⟩:=hp; change hat P.R.L P.x (j+1)/2 ≤ Y.beta i k j at q
 change Y.beta i k j ≤ 2*hat P.R.L P.x (j+1) at u; exact ⟨by unfold ceiling; linarith,u⟩
def ready (P: Preparation)(r:ℕ) := P.R.L.val*r+Push.GridApprox.reach P.R
lemma closer (r:ℕ)(X:Pane (Xj i j)→ℂ)(h:Cells.Interior (window 0 r) X) : Cells.Interior (window 0 (ready P r)) (Y.lyric i k j X) := by
 let S:= Y.stepData i k j; have he:= Y.pilot_steps j i k; have hv:= he.2.2
 have hu: S.ratio.embed 0=0:= map_zero S.ratio.root
 rw [show ready P r=S.ratio.count.val*r+Push.GridApprox.reach S.patch from (congrArg (fun x: Patch=> x.L.val*r+Push.GridApprox.reach x) he.1.symm)]; change Cells.Interior (window 0 (S.ratio.count.val*r+Push.GridApprox.reach S.patch)) (back S Kz X)
 rw [← hu]; exact back_cylinder hv h Kz (fun U V t=> S.covary hv t Kz U V)
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
