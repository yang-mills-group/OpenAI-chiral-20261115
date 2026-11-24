import SatinFixedContrastNovember4
import YM.SU5.Thin.Topped
import YM.SU5.Thin.Pedestal

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open Sifter DoseBill
namespace VoucherOp
/-- One small but true clearance test. Both seam costs must be **strictly** on
this side of the window, including intrinsic widths and all points in the closed
supports of the smears. Sequential neighbor windows TOUCH, not inserting another
hidden heat at purchase of the correlations. -/
def RoomThin (P:Spine)(A:P.Apron)(F:SampleDose)(lo hi:ℝ):Prop:=∀ p∈ tsupport F.val,
    lo<p 3-A.realWidth P 3 ∧ p 3+A.realWidth P 3< hi
def ReadyThin (F:SampleDose)(lo hi:ℝ):Prop:=∃ ε >(0:ℝ),∀ p∈ tsupport F.val,
    lo < p 3-ε∧ p 3+ε < hi
variable {P:Spine}{x:P.Spectrum0 3}{J:P.Ellis 3 x}{Z:Lead.Clan}{n:ℕ}{b:ℕ→ℕ} (D:P.VoucherOp x Z n b) (a:Bool)(s t:ℕ)(F:SampleDose)(lo hi:ℝ)
local notation "ξ"=> P.advocate 3 x 3
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ω"=> P.wealth 3 ξ
local notation "κ"=> P.enter 3 ξ
local notation "ν"=> P.physicalEnergy 3 ξ
local notation "σ"=> P.seasons 3 ξ
local notation "Ψ" k:max=> P.cardSchedule Z n (b k) a
local notation "μ" k:max=> D.cost k
include D
lemma readyCosts (q:ReadyThin F lo hi): ∀ᶠ s:ℕ in atTop, ∀ j:ℕ,RoomThin P (Ψ (s+j)) F lo hi:= by
  obtain ⟨ε,v,t⟩:=q
  have hf:Tendsto (fun i:ℕ=>(Ψ i).realWidth P 3) atTop (𝓝 0):= ((P.probeWidth_static n 3).comp D.safe.tendsto_atTop).congr fun i=>(P.schedule_width ..).symm
  obtain ⟨N,u⟩:= eventually_atTop.mp (hf.eventually (gt_mem_nhds v)) -- lt_mem? expect gt_mem
  filter_upwards [eventually_ge_atTop N] with i hi j p q
  have hl:(Ψ (i+j)).realWidth P 3 < ε:= u (i+j) (by omega)
  exact ⟨(t p q).1.trans (by linarith only [hl]), lt_trans (by linarith only [hl]) (t p q).2⟩
omit D in
lemma ReadyThin.openInterval {F lo hi} (q:ReadyThin F lo hi)(p:Vantage)(e:p∈ tsupport F.val): lo<p 3∧p 3<hi:=by obtain ⟨v,h,r⟩:=q; have hz:=r p e; constructor<;> linarith only [hz.1,hz.2,h]

-- four operators: constituent literal priced on stamp slab lo-hi at the
-- eligible t, mix(t), real smear reached at fixed widths in Hc, thin-field.
def mixedGrid : (P.ColorHil 3 ξ).Op:= (D.cost s).recipe fun k=>P.gridPage x t F (Ψ (s+k)) lo hi
def workingOp :(P.ManyF 3 ξ).Op:= DoseBill.issue H F D.bound (fun p=>D.mixPillar a s p lo hi) (fun x=> D.contPillar a s lo hi x) (fun p=> D.capPillar a s p lo hi)
def thinOp :(P.ManyF 3 ξ).Op:= DoseBill.issue H F ‖D.operator a‖ (fun p=> D.reachedPillar a p lo hi) (fun x=> D.contFinal a lo hi x) (fun p=> D.finalPay a p lo hi)
lemma working_pillar : D.workingOp a s F lo hi= (D.cost s).recipe (fun k=>P.fullPage x F (Ψ (s+k)) lo hi):=
  DoseBill.sumIssue H F D.bound _ (fun _=> D.contPillar ..) (fun _=> D.capPillar ..) _
    (fun k=>P.pillar 3 ξ (Ψ (s+k)) lo hi) (fun k=> ‖(Ψ (s+k)).engine P 3 ξ‖)
    (fun k v=> P.pillar_cont x lo hi _ _ _ continuous_id continuous_const) (fun k p=> P.pillarPay x p lo hi (Ψ (s+k))) fun p=>rfl
lemma mixedCap : ‖D.mixedGrid a s t F lo hi‖≤ P.doseTotal F t * D.bound :=
 (D.cost s).cap fun i _=> (P.rawPageBill x t F (Ψ (s+i)) lo hi).trans (mul_le_mul_of_nonneg_left (D.pays a _) (sum_nonneg (f:=fun i=>‖P.activation t F i‖) fun i _=>norm_nonneg _))
lemma workingBound : ‖D.workingOp a s F lo hi‖ ≤ along F * D.bound := DoseBill.rangeCost ..
lemma orbitalQuote : ‖D.thinOp a F lo hi‖ ≤ along F * ‖D.operator a‖ := DoseBill.rangeCost ..
-- qualification only needed for width price; for grid convergence
-- keep true cost order later with `prepped`.
omit D in
private lemma moveTogether (X Y:Hilbert)(D:Scoop)(T:X→L[ℂ]Y)(S:ℕ→ℕ→ Y.Op)(F:ℕ→X.Op)(x:X)
    (g:∀ i∈D.take,Tendsto (fun t=> S i t (T x)) atTop (𝓝 (T (F i x)))) : Tendsto (fun t=> D.recipe (fun i=> S i t) (T x)) atTop (𝓝 (T (D.recipe F x))):=by
  simp_rw [Scoop.evaluates Y, Scoop.evaluates X,Scoop.recipe,map_sum,map_smul]; exact tendsto_finsetSum _ fun i hi=> (g i hi).const_smul _
variable (J)
include J
lemma working_grid (y:P.ManyF 3 ξ) : Tendsto (fun t=> D.mixedGrid a s t F lo hi (κ y)) atTop (𝓝 (κ (D.workingOp a s F lo hi y))) :=
 let C (k t:ℕ):=P.gridPage x t F (Ψ (s+k)) lo hi; let B(k):=P.fullPage x F (Ψ (s+k)) lo hi
 Eq.mp (congrArg (fun z:(H).Op=> Tendsto (fun t=> D.mixedGrid a s t F lo hi (κ y)) atTop (𝓝 (κ (z y)))) (D.working_pillar a s F lo hi).symm)
   (moveTogether H H' (μ s) ((κ).toContinuousLinearMap) C B y fun i _=> P.page_grid x J F _ lo hi y)
omit J
lemma field_pass (q:ReadyThin F lo hi) (y:H) : Tendsto (fun i=> D.workingOp a i F lo hi y) atTop (𝓝 (D.thinOp a F lo hi y)):=
 DoseBill.tendContinuum H F _ (fun p=>D.reachedPillar a p lo hi) (fun _=> D.contFinal ..) (fun _=> D.finalPay ..) (fun i p=>D.mixPillar a i p lo hi) (fun _=> D.bound) (fun i z=>D.contPillar a i lo hi z) (fun i p=>D.capPillar a i p lo hi) D.bound (fun i p=>D.capPillar a i p lo hi) (fun x p y=> D.page_pass a p lo hi (ReadyThin.openInterval q p y).1 (ReadyThin.openInterval q p y).2 x) y
end VoucherOp
#print axioms VoucherOp.working_grid
#print axioms VoucherOp.field_pass
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
