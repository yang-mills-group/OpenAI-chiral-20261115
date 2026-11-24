import YM.SU5.Assay.Badge
import YM.SU5.Assay.ReelPrice
import YM.SU5.Assay.Medal
import YM.SU5.Assay.TollBelt
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
variable {P}
local notation "𝔏"=>Lead.Clan
local notation "τ"=>P.tock
local notation "δ"=>P.macroStep
variable (A:ℕ→P.Glaze)(M:P.Menagerie)(I:Set P.Court)
local notation "m"=>P.scrap A M I
local notation "β"=>P.rawBase j x
local notation "D"=>P.badge A M I
local notation "ι"=>P.walk j
local notation "σ"=>P.rawSlot j x
local notation "γ"=>P.actOne j x
local notation "Δ"=>P.actTwo j x
/-! Explicit embedding budget. At widths keeping the bigger stencil charged the owner's
 norms are ≤c (can blow up with s), and errors ≤e = prismGap(scrap)/exp(c). Even pre-posed
 raw readings bought at either orientation. -/
variable (s:ℕ)
structure Lock (P:Spine)(j:Axis)(x:P.Spectrum0 j)(A:ℕ→P.Glaze)(M:P.Menagerie)(I:Set P.Court)(s:ℕ)(c e:ℝ):Prop where
 low:0≤c
 high:0≤e
 pays:e*Real.exp c ≤ prismGap (P.scrap A M I s)
 capital:∀Z:Lead.Clan,∀ {l r},P.tock s (P.badge A M I Z s).w≤l→P.tock s (P.badge A M I Z s).w≤r→
   ‖P.rawBase j x (serial A s) l r‖≤c ∧
    ‖P.rawBase j x (serial (P.badge A M I Z) s) l r-P.rawBase j x (serial A s) l r‖≤e

lemma badge_width (Z:𝔏):(A s).w ≤ (D Z s).w:= (P.ferry_own A M I s).trans (Nat.le_add_left ..)
variable {A I s}
private lemma one_lock (h:P.Punch I M A s (m s))(v:(⟨j,x⟩:P.Court)∈I):∃ c e,P.Lock j x A M I s c e:=by
 let c:=‖β (serial A s) (m s) (m s)‖
 let q:=Real.exp c
 have t:0 < q:=Real.exp_pos c
 have k:=P.scrap_pos A M I s
 let b:= prismGap_pos k
 refine ⟨c,prismGap (m s)/q,norm_nonneg _,(div_pos b t).le,le_of_eq (div_mul_cancel₀ _ t.ne'),fun Z {l r} p u=>?_⟩
 obtain ⟨r',w⟩:=h.2 Z
 let f:=P.ferry_guest A M I s Z;let g:=P.ferry_own A M I s
 have y: m s≤τ s (D Z s).w:= (P.ferry_room A M I s).trans ((P.tock_le ..).mpr (Int.ofNat_le.mpr (Nat.le_add_left ..)))
 constructor
 · rw [P.rawBase_step j x (serial A s) h.1 h.1 (y.trans p) (y.trans u)]
   exact sand_pay ..
 · apply (belt_cost x g f p u h.1 r' (P.ferry_room A M I s)).trans
   rw [le_div_iff₀ t,mul_comm (_*_) q,←mul_assoc]; exact w ⟨j,x⟩ v
lemma Clutch.lock (h:P.Clutch I A)(v:(⟨j,x⟩:P.Court)∈I):∀ᶠ s in atTop,∃ c e,P.Lock j x A M I s c e:=
 (Clutch.punches M h).mono fun i y=> one_lock j x M y v -- syntax
lemma scrap_small (P:Spine)(A:ℕ→P.Glaze)(M:P.Menagerie)(I:Set P.Court)(s:ℕ):P.scrap A M I s≤1:=
 inv_le_one_of_one_le₀ ((le_add_iff_nonneg_left ..).mpr (by positivity))
variable {M j x}{c e a b:ℝ}{Z:𝔏}
namespace Lock
variable (h:P.Lock j x A M I s c e)
include h
lemma overs:e*(c+1)≤ prismGap (m s):= (mul_le_mul_of_nonneg_left (Real.add_one_le_exp c) h.high).trans h.pays
lemma edge:e ≤ prismGap (m s):=(le_mul_of_one_le_right h.high ((le_add_iff_nonneg_left ..).mpr h.low)).trans h.overs
lemma pin:e≤1:=(h.edge.trans (prismGap_le (scrap_pos ..))).trans (scrap_small ..)
lemma usePoint (n:Bool)(p:τ s (D Z s).w≤a)(q:τ s (D Z s).w≤b):
 ‖β (ι n (serial A s)) a b‖≤c ∧ ‖β (ι n (serial (D Z) s)) a b-β (ι n (serial A s)) a b‖≤e:=by
 cases n;· exact h.capital Z p q
 simp only [walk,↓reduceIte,P.rawBase_kiss,rawOther,←star_sub,norm_star]
 exact h.capital Z q p
lemma slot_lock {F:SampleDose}(n:Bool)(t:ℕ)(w:Walled j F a b (τ s (D Z s).w)):
 ‖σ t (ι n (serial A s)) a b F‖≤P.gridMass F t*c ∧
 ‖σ t (ι n (serial (D Z) s)) a b F-σ t (ι n (serial A s)) a b F‖≤P.gridMass F t*e:=by
 constructor
 · apply P.sampler_cost
   intro y u;exact (h.usePoint n (w y u).1.le (w y u).2.le).1
 · apply P.sampler_diff
   intro y u;exact (h.usePoint n (w y u).1.le (w y u).2.le).2
end Lock
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
