import YM.SU5.Assay.Coin
import YM.SU5.Assay.TickPay
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
open Ballad Glaze
local notation "C"=>Lead.Clan
local notation "ϱ"=>P.respool j x
local notation "β"=>P.rawBase j x
local notation "ν"=>P.rawSlot j x
variable (A:ℕ→P.Glaze)(M:P.Menagerie)(I:Set P.Court)(Z:C)
local notation "€"=>P.electro M
local notation "o" s:max =>pinDiagonal (P.ferry A M I s)
/-! Buy the same chiral-wire normalization by putting the nonzero appraised
 factor back. This enters the `F` formula only to CANCEL the appraisal,
 though charges on placement and on the limiting thermal operators and bounds
 will in general notice this factor. -/
def inlay (s:ℕ): P.Glaze := (P.badge A M I Z s).coat (€ Z)
def inlayBook (l:ℕ→P.Folio)(s:ℕ):P.Folio:=beltBook (P.ferry A M I s) (l s) (P.stockFolio (P.flash (M Z).n) Z)
local notation "Q"=>P.inlay A M I
lemma inlay_literal (s:ℕ):
 (Q Z s).F=(A s).F*P.chartAll (o s) (P.frontMat Z (M Z).n):=by
 change € Z•((A s).F*P.chartAll (o s) ((M Z).bright.F))=_
 rw [←mul_smul_comm,←map_smul,P.electro_front]
lemma inlay_first {l:ℕ→P.Folio}(h:∀s,P.Wove none (A s).S (A s).F (l s))(s:ℕ):
 P.FirstDress (serial (Q Z) s) Z.2 (P.inlayBook A M I Z l s):=by
 let B':=(M Z).bright.coat (€ Z)
 have e:B'.F=P.frontMat Z (M Z).n:=P.electro_front M Z
 let k:=P.stockFolio (P.flash (M Z).n) Z
 have p:P.FirstDress (B'.apron s) Z.2 k:=by
   change B'.F∈P.Beam s _ _ ∧ P.Wove _ _ B'.F _
   rw [e]
   exact P.front_film _ _ (M Z).gap s
 let v:=P.ferry A M I s
 have w:B'.w≤v:=P.ferry_guest A M I s Z
 have u:=belt_first (l s) k (P.ferry_own A M I s) w (h s) p
 let d:=(Q Z s).S
 let b:= P.inlayBook A M I Z l s
 change (A s).F*P.chartAll (o s) B'.F ∈P.Beam s d _ ∧ P.Wove _ _ ((A s).F*P.chartAll (o s) B'.F) b at u
 change (Q Z s).F∈P.Beam s d _ ∧ P.Wove _ _ (Q Z s).F b
 rw [P.inlay_literal,←e];exact u
variable {P j x A I}
lemma Clutch.inlay_tiny (h:P.Clutch I A):Tiny (Q Z):=h.badge_tiny M Z
lemma Clutch.inlay_pole (h:P.Clutch I A)(v:(⟨j,x⟩:P.Court)∈I)
 {g:ℕ→P.VMark}{p:Vantage}{T:P.RawLag j x}(u:P.RawNormal j x (serial A) g p T):
 P.RawNormal j x (serial (Q Z)) g p (€ Z •T) :=
 (h.raiseRaw M Z v u).scale (h.inlay_tiny M Z).fades (fun _=>rfl) (fun _=>rfl)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
