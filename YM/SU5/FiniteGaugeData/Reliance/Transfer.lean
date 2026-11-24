import YM.SU5.FiniteGaugeData.Reliance.Lobby
import YM.SU5.FiniteGaugeData.LocalLimit.Physical
import YM.CF.Continuum.Caravan
/-!
# Actual uniform high-level budgets, at one Cashbox pivot Λ

Bootstrap by comparing to the level-zero loan IN this family (not smaller tori, not Printed).
Retain actual pole and all records; supply the sharpened capCost so our carousel representation
buys all levels of the **same CapP parcel**. No comparisons at heat or varying pivot here. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
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

open FullBill Window Marks
open Pyx
open Girt

namespace Preparation
local notation "q₀" => Chi.canonical
variable {P : Preparation} {F : (s:Side)→ Scree.Loom s → Prop} (Y:Course P F)

namespace Course
variable (i k j : ℕ)
local notation "Ξ" => Y.voyage i
local notation "U₀" => P.U
local notation "N₀" => (Ξ).funds
local notation "m₀" => Y.ir i
local notation "CS" => P.Ctor (Y.ir i)
local notation "kt" => Y.uv k
local notation "Xv" => (Ξ).X (Y.uv k)
local notation "Χ" j => (Xv).gram j
local notation "Qv" => (Ξ).CapeT
local notation "T" => Y.meter
local notation "Yr" => Vale.mesh m₀ P.R.L

open Window Graph Period Jade.Earn

/-- Can call the Carousel budgets as sharpened through TOP this time. -/
def sturdy : Carousel P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.x (Y.ir i) (Y.uv k):=by
 let M:= Y.history i k; let p:=(Xv).pull
 exact ⟨T,N₀,kt,le_rfl,(Xv).pilot,(Xv).gram,Qv,(Xv).wave,(Xv).fee,p.wear,p.owns,p.sift,M.mark,M.pole,M.roof,(Xv).due,fun j h=> by
    have t:= p.note j h; refine ward_m (show (Χ j).path.Bounds (Χ j).funds P.K.top.width P.K.top.paths P.V.W.bar from ?_) (t.lot_p le_rfl le_rfl)
    rw [← (p.owns j h).path, ← (p.owns j h).fund]; exact P.V.L.mood _, (Xv).balance,p.color.trans ((Xv).due.unit),p.tip,p.price,p.note,p.shift⟩

abbrev faceW (P: Preparation)(j:ℕ):= hat P.R.L P.x j -- notation T
local notation "xs" j:max=> hat P.R.L P.x j
local notation "φ"=> Y.sturdy i k
local notation "Va" j:max=>sites (cell (Y.ir i) P.block P.R.L j)

-- check def, clamp profile; L≥3, exact match.
lemma seatRule (a:Side) : sites a= roomSite (More a):= by simp only [sites,roomSite,site_card,Nat.cast_pow]
lemma howBig (P:Preparation)(m:Side)(j:ℕ)(a:ℝ):
    pathFees (More (P.Ctor m j)) (More (P.Ctor m (j+1))) (Scales.y SU.group P.R.L (hat P.R.L P.x j)) a = -(capCost P.R (hat P.R.L P.x j) a) * sites (P.Ctor m j):=by
 let h:= hat P.R.L P.x j; let v:ℝ:=P.R.L.val; let u:= sites (P.Ctor m j); let x:= sites (P.Ctor m (j+1))
 have he:x=v^4*u:=by
    unfold x u v sites; rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow]
    have ht:(More (P.Ctor m (j+1))).val=(More (P.Ctor m j)).val* P.R.L.val:= kint m P.block P.R.L j
    rw [ht]; push_cast; ring
 unfold pathFees capCost; unfold x at he; rw [←seatRule,←seatRule,he]; unfold v u; ring

lemma paid_progress {a:ℝ}(h:∀ z≥P.x,P.C z≤ capCost P.R z a): Carousel.Promoted P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ (Y.ir i) a (Y.sturdy i k):=by
 intro j q; have he:= (Xv).perSite j q
 let V:= Va j; have hv:0 ≤ V:= zero_le_one.trans (sites_pos _)
 let w:= (Χ j).v.re; let u:= (Χ (j+1)).v.re; let Z:=curve_F P.R.L (More (CS j)) (More (CS (j+1))) (xs j) a
 have hy: - (P.C (xs j) * V) ≤ w-u:= (abs_le.mp he).1
 have hx: Z≤ w-u:= by
   unfold Z curve_F; rw [howBig P (Y.ir i) j a,neg_mul]; exact (neg_le_neg (mul_le_mul_of_nonneg_right (h (xs j) (Vale.crown ..)) hv)).trans hy
 rw [Complex.norm_exp,Complex.norm_exp,←Real.exp_add]; apply Real.exp_monotone; change u+Z ≤ w; linarith
local notation "Φr" j:max => rateBet (Χ j) (Qv j) P.U
local notation "φt" j:max => TV (Χ j) (Qv j) P.U

lemma tenure {a:ℝ} (h:(Ξ).kick ≤ k) (p:Y.τ ≤ a) : Real.exp (budgetCharge (Χ 0) (soaked P.x) (-a)) ≤ rateBet (Χ 0) (Qv 0) P.U:=by
 let b := soaked P.x; have hz:1 ≤ P.x:= Y.oneP; have hp:0< P.x:=zero_lt_one.trans_le hz; have ht: b≤1:= inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hz)
 have he : strengthLog b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (Real.log_nonpos (show 0≤b from (inv_pos.mpr (Real.sqrt_pos.mpr hp)).le) ht)
 have hi:= (Ξ).lower k h; apply le_trans (b:=Real.exp (-Y.τ*sites _)) _ hi
 apply Real.exp_monotone; have hk:massMeter (cell (Y.ir i) P.block P.R.L 0)=Va 0:=by unfold massMeter sizes sites; rw [Nat.cast_pow]
 change massMeter _*(3*strengthLog b+-a) ≤ _; rw [hk,mul_comm (-Y.τ)]; apply mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans (sites_pos _))

/-- uniform lower AFTER strip, not relative to `serviceCost` bound for each level. -/
theorem solvent (W:Cashbox P) :
    ∃ A:ℝ,0 < A ∧ ∀ i k, (Y.voyage i).kick ≤ k→ ∀ j ≤ Y.uv k,
     let X:= ((Y.voyage i).X (Y.uv k)).gram j
     let S:= (Y.voyage i).CapeT j
     Tableau (Vale.mesh (Y.ir i) P.R.L j) X S P.U (soaked (hat P.R.L P.x j)) A := by
 obtain ⟨r,h,p⟩:= W
 let O:=Classical.choice (YM.Next.Rank.exists_budget SU.group)
 let C:= Carousel.costPlan P.V (cashU P.W.C) O; let A:= max (max Y.τ C) (2*r)
 have hr:2*r≤A:=le_max_right ..; have ht: max Y.τ C≤A:= le_max_left ..
 refine ⟨A,lt_of_lt_of_le (by positivity) hr,fun i k t j v=>?_⟩; intro X S; let P':= Y.sturdy i k; let W:= hat P.R.L P.x j; let hV:= p W (Vale.crown ..)
 have g : Real.exp (budgetCharge (P'.E j) (soaked W) (-A)) ≤ rateBet (P'.E j) (P'.Y j) P.U:= Carousel.fullPaid P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ (zero_lt_one.trans_le Y.oneP) h.le hr P' (paid_progress Y i k (fun i u=>(p i u).1)) (tenure Y i k t ((le_max_left Y.τ C).trans ht)) j v
 refine ⟨Carousel.sailed P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P' j v,g,?_⟩
 refine (Carousel.toils_κ P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.height P' O j v hV.2.1 hV.2.2).trans (Real.exp_monotone (budgetLe (P'.E j) C A (soaked W) ((le_max_right ..).trans ht)))
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Course.solvent
