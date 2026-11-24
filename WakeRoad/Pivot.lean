import WakeRoad.Sciad
import Gingham.Ruff.AtSea
import WakeRoad.Tallow
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
open CF.Onyx
open CF.Gingham.Ruff Spine.Gingham.VoyageB
open UVNext.FreeStress
variable (P:Spine)(r:ℕ→ℕ)
local notation "iₛ" i:max=>P.period (P.projection.rows (r i))
local notation "kₛ" i:max=>P.cutoff (P.projection.columns (r i))
local notation "nDoc" s:max i:max=>side P.run (iₛ i) s
local notation "Mₛ" s:max i:max=>P.par.V.L.H ((P.run).uv (kₛ i)-s)
local notation "R*" s:max=> ((↑(2*ArborJet.moment P s:ℕ):ℂ))
local notation "ff"=> (4* Maxwell.normal)
variable {m:ℕ}
variable (s n:ℕ)
local notation "K"=>RootBook P.run (iₛ n) (kₛ n) s
local notation "ι"=>Postcard ((K).p.B/10)
variable {a c μ:ℝ}{l:ℕ}{δ C:ℝ}(B:Scene P a c μ l s (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))))(X:Rialto 6 P.par.d δ C)
local notation "A*" b:max=> grove P s (iₛ n) (kₛ n) b
local notation "w*"=> cocoa P s (iₛ n) (kₛ n) B X
local notation "G*" b:max=>combo P s (iₛ n) (kₛ n) B X b
open Spine.Gingham
open Gingham.Ruff
variable {r' f:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ l r' F)
    (E:ℝ)(κ:ℕ→ℝ)
-- supply ledger lower at joint poses θ and x, signed determinant etc. here reporting before landing passage inside r
set_option maxHeartbeats 600000
include β
lemma profitPlane (w:StrictMono f)(pA:Anthem P a c μ l δ C X)(hd:0<δ)(HM:Pooling P.run (P.period∘P.projection.rows) (P.cutoff∘P.projection.columns) (r'∘f) κ){Reg:P.Register}{m₀:ℕ}(H:P.PreparedInvestment Reg E m₀):
 ∃ q'> (0:ℝ),∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,
   let i:=Diary.irr P ((r'∘f) n); let k:=Diary.uvv P ((r'∘f) n);
   Nonempty (Scene P a c μ l s i k) ∧ ∀ B:Scene P a c μ l s i k, let R:=κFix κ s; let _r:=(r'∘f); let f':=ArborJet.filmT P s i k B δ R; let A:=f' true; let G:=f' false;
     q' ≤ (((↑(2*ArborJet.moment P s:ℕ):ℂ)^8)*(Journey.compass P.run i k s (A * G)-Journey.compass P.run i k s A * Journey.compass P.run i k s G)).re := by
 let r:=r'∘f
 obtain ⟨q,hq,t⟩:=mortgage P X β w pA hd HM
 obtain ⟨D,d,u,W⟩:=chargeMirror P a c μ l X hd β.aP pA (ν:=r) HM.up.tendsto_atTop
 have v:=collecta P X m₀ Reg E H β (Classical.choice (PhysicalNext.JointLoad.Heir.webExists SU.group)) hd pA w.tendsto_atTop
 refine ⟨q/2,half_pos hq,?_⟩
 filter_upwards [t,W,(master P D).eventually (gt_mem_nhds (half_pos hq)),v] with s t W g v
 let ξ:=κFix κ s
 let R :ℝ:=↑(2*ArborJet.moment P s)
 let x:=hat P.par.R.L P.par.x s
 have hp:= paidFix P.run HM P.large s
 filter_upwards [t,W,v,(Gathering P.run HM s).abs.eventually (gt_mem_nhds (by norm_num: |(1:ℝ)|<2))] with n t W v g₀
 refine ⟨t.1,fun B=>?_⟩
 let i:=Diary.irr P (r n); let k:=Diary.uvv P (r n)
 obtain ⟨o,y,z⟩:=W B
 let S:= atlas P r s n B X ξ
 let T' := ArborJet.filmT P s i k B δ ξ
 let G:= visage P r s n B X ξ
 let M(U):= Journey.compass P.run i k s U
 let u:= (v.2 B _ hp)
 have e(b:Bool): ‖S b‖ ≤ sage P D x:=by
    have he:=ceiling P r s n B X ξ b g₀.le -- pos
    let d:= (RootBook P.run i k s).p
    have hz':d.B=radiusB x:= B.gears.boot.B
    change _ ≤ _ * Regis.Wake.assay 2 (leaseR _) (Fintype.card (Postcard (d.B/10))) at he
    refine he.trans ?_
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (o.trans (le_abs_self _)) (by norm_num)) (Regis.Wake.assay_non _ _ _ (by positivity))); unfold sage; rw [hz']
 have t': q ≤ ((↑(R^8):ℂ)*(G-S true*S false)).re:=by
    unfold R; rw [Complex.ofReal_pow,Complex.ofReal_natCast]; exact t.2 B
 let e':= fuel_split (M (T' true)) (M (T' false)) (M (T' true*T' false)) (S true) (S false) G (R^8) _ (fuzzy x) (pow_nonneg (Nat.cast_nonneg (α:=ℝ) _) _) ((norm_nonneg _).trans (e true)) (chip_pos ..|>.le) (e true) (e false) (u.single true) (u.single false) u.joint _ t'
 have tQ:q/2 ≤ ((↑(R^8):ℂ)*(M (T' true*T' false)- M (T' true)* M (T' false))).re := e'.trans' (by change q/2≤q-R^8*waste P D x; linarith only [g])
 unfold R at tQ; rw [Complex.ofReal_pow,Complex.ofReal_natCast] at tQ; exact tQ
#print axioms profitPlane
