import Preen.Troon
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 100000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel
variable (P:Spine)(s w:ℕ)(o:Bool→ Cover)(n₀:Bool)(z:ℝ)(A:ℕ)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Δ" i:max=> flightY P w (i:ℕ)
local notation "η" i:max b:max=> cabinY P (o b) w (i:I).val
local notation "S₀"=>spots P s w o A
local notation "T₀"=>trialY P s w o n₀ z A
noncomputable abbrev anchors (P:Spine)(s w:ℕ)(o:Bool→ Cover)(A:ℕ)(n:Side)(i:Fin (cardD P A s))(b:Bool):Skye.Seat n:= wrap (More n) (nodeC (cabinY P (o b) w i.val))
noncomputable abbrev pedestal (o:Bool→ Cover)(n:Side)(b:Bool):Skye.Seat n:=wrap (More n) (nodeC (o b))
abbrev onSq(n:Side):Mark n:=CalendarQ' (sampleZ (V) (Real.sqrt (Yx)) (σ) z n₀ (anchors P s w o A n) (fun _ _=> 1)) -- Health wind chord
variable (i:ℕ)
local notation "N"=>Papal.count P.run s i
-- test eval. 
lemma body_cost (m:Side)(q:0<P.payday s)(x:Fields ((K).c m)) : (bodyT P s o n₀).val m x=((raiseX SU.group (V) (Real.sqrt (Yx)) n₀ x.1 (fun _:Bool=>1) (pedestal o ((K).c m)):ℝ):ℂ) • (1:FC _):=by
 unfold bodyT testZ raiseX loader; split
 · change (fellerT P s (o false)).val m x * (fellerT P s (o true)).val m x = (↑(_*_ :ℝ):ℂ) • _
   rw [show (fellerT P s (o false)).val m x=_ from feller_mark P s _ _ q x,show (fellerT P s (o true)).val m x=_ from feller_mark P s _ _ q x,Complex.ofReal_mul]
   rw [Algebra.smul_mul_assoc,one_mul,smul_smul]
 exact feller_mark P s _ m q x
lemma trial_cost(m:Side)(q:0<P.payday s): (T₀).val m=onSq P s w o n₀ z A ((K).c m):=by
 let y:=Real.sqrt (Yx); let k(i:ℕ):= yacht P s w o n₀ i
 let Y(x:I):P.Test:= (σ:ℂ) • (k x.val-(z:ℂ) • 1)
 have hv : (∑ i:I,Y i).val=∑ i:I,(Y i).val:=by -- use Finset.sum_hom? general induction with add
    generalize (Finset.univ:Finset I)=S; induction S using Finset.induction_on with | empty=> simp | @insert j S h H=>rw [sum_insert h,sum_insert h]; change (Y j).val+ _ =_; rw [H]
 funext x
 change (∑ i:I,Y i).val m x=_; rw [hv,Finset.sum_apply,Finset.sum_apply]; unfold onSq sampleZ CalendarQ'
 dsimp only; rw [Complex.ofReal_sum, Finset.sum_smul] -- sum_smul?
 apply Finset.sum_congr rfl; intro i _
 change (σ:ℂ) • ((k i.val).val m x-(z:ℂ) • 1)= _; have he:=body_cost P s (fun j=> cabinY P (o j) w i.val) n₀ m q x
 rw [show (k i.val).val m x=_ from he,Complex.ofReal_mul,Complex.ofReal_sub,←sub_smul,smul_smul]
variable (n:Side)
lemma arrive_r : Route (anchors P s w o A n) (fun _ _=>1) (pedestal o n) (fun _=>1):=by
 intro i; refine ⟨1,(Pi.single (3:Axis) (((pollN P:ℤ)*(flightY P w i.val:ℤ):ℤ):Per (More n)):Site (More n)),?_,by simp⟩
 funext b k; unfold anchors pedestal; rw [affine,show Signed.act 1 _ = wrap _ (nodeC (o b)) from Signed.act_one ..]; change (((nodeC (η i b) k:ℤ):Per (More n)))=_; rw [ticking P w o k k]; split
 next v=> subst k; rw [Int.cast_add]; rw [Pi.add_apply]; rw [Pi.single_eq_same]; rfl
 next v=> rw [add_zero]; rw [Pi.add_apply]; rw [Pi.single_eq_of_ne v,add_zero]; rfl
private lemma bands_now (n:ℕ)(o:Cover):nodeC o∈ Calico.bands o n:= Calico.inBands o (fun i=>by rw [sub_self]; exact ⟨by exact Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _), Int.natCast_nonneg _⟩)
set_option diagnostics true in
lemma townT (b:Bool)(t:I) :nodeC (η t b) ∈ S₀:=by
 unfold spots
 let v(i:I)(b:Bool):= Calico.bands (η i b) 22
 have h0:=bands_now 22 (η t b)
 exact join_mem v t b h0
where join_mem {α γ:Type}[Fintype γ][DecidableEq α](f:γ→Bool→ Finset α)(i:γ)(b:Bool){x:α}(p:x∈f i b): x∈ (Finset.univ:Finset γ).biUnion (fun i=>Finset.univ.biUnion fun b:Bool=>f i b):= Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,p⟩⟩
lemma tray_tag (b:Bool)(t:I):anchors P s w o A n t b∈Satin.region (S₀) n:=Finset.mem_image_of_mem _ (townT P s w o A b t)
private lemma transport_eq{c d:Side}(h:c=d): ship h (onSq P s w o n₀ z A c)=(onSq P s w o n₀ z A d):=by subst c; rfl
lemma lit_port (q:0<P.payday s) : distribute P.run P.large s i (T₀).val=onSq P s w o n₀ z A (N) := by unfold distribute; rw [trial_cost P s w o n₀ z A _ q,transport_eq] -- count=side
#print axioms lit_port
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
