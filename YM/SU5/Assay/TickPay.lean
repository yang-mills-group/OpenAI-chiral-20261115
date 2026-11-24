import YM.SU5.Assay.Narrow
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
/-! Claims using the punched embedding. -/
lemma mass_nonneg (P:Spine)(F:SampleDose)(t:ℕ):0≤P.gridMass F t:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
variable {j x A M I}{a b d k c e:ℝ}{Z Z':𝔏}{F G:SampleDose}{s t u:ℕ}
namespace Lock
variable (h:P.Lock j x A M I s c e)
include h
lemma raw_once (n:Bool)(w:Walled j F a b (τ s (D Z s).w)):
 ‖σ t (ι n (serial (D Z) s)) a b F-σ t (ι n (serial A s)) a b F‖≤P.gridMass F t*prismGap (m s):=
   (h.slot_lock n t w).2.trans (mul_le_mul_of_nonneg_left h.edge (mass_nonneg ..))
lemma raw_joint (n p:Bool)(w:Walled j F a b (τ s (D Z s).w))(v:Walled j G d k (τ s (D Z' s).w)):
 ‖σ t (ι n (serial (D Z) s)) a b F*σ u (ι p (serial (D Z') s)) d k G-
    σ t (ι n (serial A s)) a b F*σ u (ι p (serial A s)) d k G‖≤P.gridMass F t*P.gridMass G u*(2*prismGap (m s)):=by
 obtain ⟨g,l⟩:=h.slot_lock n t w
 obtain ⟨q,r⟩:=h.slot_lock p u v
 let f₀:=σ t (ι n (serial A s)) a b F
 let g₀:=σ u (ι p (serial A s)) d k G
 let f₁:=σ t (ι n (serial (D Z) s)) a b F
 let g₁:=σ u (ι p (serial (D Z') s)) d k G
 let i:=P.gridMass F t; let y:=P.gridMass G u; have i':0≤ i:=mass_nonneg ..;have y':0≤y:=mass_nonneg ..
 change ‖f₁*g₁-f₀*g₀‖≤ i*y*(2*prismGap (m s))
 have v':‖g₁‖≤y*(c+1):=calc
   _=‖g₁-g₀+g₀‖:=by rw [sub_add_cancel]
   _≤y*e+y*c:=(norm_add_le ..).trans (add_le_add r q)
   _≤_:=by rw [←mul_add];exact mul_le_mul_of_nonneg_left (by linarith only[h.pin]) y'
 rw [show f₁*g₁-f₀*g₀=(f₁-f₀)*g₁+f₀*(g₁-g₀) by rw [_root_.sub_mul,mul_sub];abel]
 refine (norm_add_le ..).trans ?_
 have t:‖(f₁-f₀)*g₁‖≤ i*e*(y*(c+1)):=
   (norm_mul_le ..).trans (mul_le_mul l v' (norm_nonneg _) ((norm_nonneg _).trans l))
 have z:‖f₀*(g₁-g₀)‖≤ i*c*(y*e):=
   (norm_mul_le ..).trans (mul_le_mul g r (norm_nonneg _) ((norm_nonneg _).trans g))
 apply (add_le_add t z).trans
 rw [show i*e*(y*(c+1))+i*c*(y*e)=i*y*(e*(c+1)+e*c) by ring]
 exact mul_le_mul_of_nonneg_left (by linarith only [h.overs,h.high]) (by positivity)

lemma once (n:Bool)(w:Walled j F a b (τ s (D Z s).w))(y:s≤t):
 ‖γ (D Z s) n F s t-γ (A s) n F s t‖≤P.gridMass F t*prismGap (m s):=by
 have q:=Walled.grow (badge_width A M I s Z) w
 rw [actOne_price n _ w y,actOne_price n _ q y]
 exact (P.vacant_diff ..).trans (h.raw_once n w)
lemma joint (n p:Bool)(w:Walled j F a b (τ s (D Z s).w))(v:Walled j G b d (τ s (D Z' s).w))(y:s≤t):
 ‖Δ (D Z s) n F (D Z' s) p G s t-Δ (A s) n F (A s) p G s t‖≤P.gridMass F t*P.gridMass G t*(2*prismGap (m s)):=by
 have q:=Walled.grow (badge_width A M I s Z) w
 have r:=Walled.grow (badge_width A M I s Z') v
 rw [actTwo_price n p _ _ w v y,actTwo_price n p _ _ q r y]
 exact (P.vacant_diff ..).trans (h.raw_joint n p w v)
end Lock

-- Obtain the limiter on upper closure price; not sufficient for full
-- interaction as need a nontrivial owner to begin with. Transfer even
-- RawNormal whenever owner has it in catering chamber.
variable (M) (Z:𝔏)
lemma Clutch.exchange (h:P.Clutch I A)(v:(⟨j,x⟩:P.Court)∈I):
 ∀a>0,∀b>0,∀ᶠ s in atTop,‖β (serial (D Z) s) a b-β (serial A s) a b‖≤ m s:=by
 let y:=h.badge_tiny M Z
 intro a p b q
 filter_upwards [y.early p,y.early q,h.lock j x M v] with s u y ⟨_,_,r⟩
 exact (r.capital Z u y).2.trans (r.edge.trans (prismGap_le (scrap_pos ..)))
lemma Clutch.raiseRaw (h:P.Clutch I A)(v:(⟨j,x⟩:P.Court)∈I){g:ℕ→P.VMark}{p:Vantage}{T:P.RawLag j x}(w:P.RawNormal j x (serial A) g p T):P.RawNormal j x (serial (D Z)) g p T:=
 w.viaDiff (h.badge_tiny M Z).fades (h.scraps M) (h.exchange M Z v)
lemma Clutch.raiseNormal (h:P.Clutch I A)(v:(⟨j,x⟩:P.Court)∈I){T:P.LagOp j x}(w:P.Normal j x (serial A) T): P.Normal j x (serial (D Z)) T:=by
 refine w.viaDiff (h.badge_tiny M Z).fades (h.scraps M) (fun a u b y=>?_)
 filter_upwards [h.exchange M Z v a u b y] with i p
 rw [←P.reprise_rawBase,←P.reprise_rawBase,←P.reprise_sub];exact (P.reprise_pay ..).trans p
lemma Clutch.raiseKiln (h:P.Clutch I A)(v:(⟨j,x⟩:P.Court)∈I){T:P.LagOp j x}(w:P.Kiln j x (serial A) T):P.Kiln j x (serial (D Z)) T:=by
 refine ⟨w.gridded,h.raiseNormal M Z v w.normal,?_⟩
 intro F a b p
 obtain ⟨u,_,r⟩:=P.grid_budget F -- typo
 have ht:Tendsto (Prod.fst:ℕ×ℕ→ℕ) atTop atTop:=by rw [←prod_atTop_atTop_eq]; exact tendsto_fst
 have y:Tendsto (fun i=>u*m i) atTop (𝓝 0):=by simpa using (h.scraps M).const_mul u
 refine (w.pressed F a b p).squeeze' (y.comp ht) ?_
 filter_upwards [ht.eventually ((h.badge_tiny M Z).fades.room p),ht.eventually (h.lock j x M v)] with i w ⟨_,_,g⟩
 exact (g.raw_once false (t:=i.2) w).trans (mul_le_mul (r i.2) (prismGap_le (scrap_pos ..)) (prismGap_pos (scrap_pos ..)).le ((mass_nonneg ..).trans (r i.2)))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
