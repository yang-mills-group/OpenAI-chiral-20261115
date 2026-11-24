import YM.SU5.SatinWard.Resolution.Disclosure
import YM.SU5.SatinWard.Resolution.Ynez
import YM.SU5.SatinWard.Resolution.Tableyard
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open MezzoBill
namespace Dovetail

/-! Same regulator convergence including external-lag powers before claiming WP. want uniform-li bound in v for both.T.Ages.Future. This module first finances reflection at stages used. -/
variable {v m:ℕ}(q:Cover)(p:ResidualPermit q)(M:P.par.R.L.val%16=1)(z:Soul)(i:Axis)(x:P.Spectrum0 i)(mu:Axis)
local notation "σ" v:max=> P.macroStep v
local notation "ℛ"=> P.locate i x
local notation "π"=> P.reprise i x
local notation "ℜ"=> P.charter i x
local notation "fee" i:max => home P q i
variable {s f0:ℕ}{Z:ℕ→ℕ}{C H A d c dσ:ℝ}{η:Type}[Fintype η](ρ:Piano P f0 C H A η Z) (q₂:payable P v 2)
local notation "q'"=> flipline i q
local notation "p'" => makesColor q p i
local notation "JV" u:max=> JpriceApp P q M p u mu v
local notation "Ju" u:max=> JpriceApp P (flipline i q) M (makesColor q p i) u mu v
local notation "K$"=> soloV P v q₂ q p pseV
local notation "K'"=> soloV P v q₂ (flipline i q) (makesColor q p i) pseV
local notation "φ♠"=> (↑(colorPay i mu):ℂ)
local notation "Uw"=> (kinWidth P:ℝ)*P.macroStep v
local notation "Uf"=> (choirWidth P:ℝ)*P.macroStep v
local notation "δ₀" v:max=> moonClock P v
variable (p₁:f0 ≤ v)(pHw:Tendsto Z atTop atTop)(W:HeartClock P f0 H A d c dσ P.jump128 M Z η)(e:Melodic P η A f0 Z)(K:P.NightCop)[Nonempty η]{l r:ℝ}
local notation "hℓ"=> home P q v
local notation "PS"=> pricedPSE P M i x p ρ
local notation "Px"=> pricedPSE P M i x (makesColor q p i) ρ
local notation "Tμ" v:max => psScale P ρ v
local notation "Cℓ" F:max => annoFace P i x v (home P q v) F
local notation "Ζℓ" F:max => annoFace P i x v (home P (flipline i q) v) F
local notation "v★" s:max=> trueKey P pHw e K s
namespace Freeport
open Polaris
local notation "root"=> rayPost
local notation "A☆" x:max=> priceX P pHw e mu rayPost M K rayP i x z
local notation "B☆" x:max=> pricedPSE P M i x rayP ρ
local notation "A◇" x:max v:max=> realFreshF P pHw e mu rayPost M K rayP i x z v
local notation "B◇" x:max v:max=> heyC P rayPost rayP i x ρ v
variable (x₁:P.Spectrum0 3)(J:P.Ellis 3 x₁)(y: Bool→ Cover)(T: ℝ)
local notation "U"=> P.advocate 3 x₁ i
local notation "PSΓ"=>P.singleState 3 v x₁
local notation "δ" v:max=> moonClock P v
local notation "Θt" v:max=> home P rayPost v
local notation "ΖQ" v:max=> (↑(psScale P ρ v):ℂ)
local notation "ν" s:max=> P.macroStep s
local notation "Jour" v:max p:max=> cornea P M pHw e K v mu z p
local notation "Pse" v:max p:max=> brass P ρ v p
open Polaris.Rampart _root_.GarnetAct.Cut
variable (F G:Curtain)
local notation "aE" p:max r:max=> Metric.closedBall p r
-- rectangular authorization.Evaluate even with unshrunk local boxes. Mask Momentum tested on same Body.Survives under refinement as needed. These attest containment at each measured support price. Doesn't assert unaffected old promoted supports are still single-level budgets.
open RibbonDoc
local notation "Φ"=> P.Aperture
local notation "τ" i:max=> P.pinFoot i
local notation "Gx" x:max v:max => P.meshPose v x
local notation "dη" h:max=> psScale P ρ h
local notation "Hℓ" v:max=> home P rayPost v
local notation "Θζ"=> P.calibration
-- accused.APP.T.Preparation position issues enquiry.V.Genuine.
local notation "Κ★" i:max v:max => brass P ρ v i
local notation "Z★" i:max v:max => cornea P M pHw e K v mu z i
lemma paysAt (N:P.Apron)(p:Vantage)(u:∀ i:Axis,N.realWidth P i+ |home P rayPost v i|≤ moonClock P v) (q:Cover) : Φ N (Gx q v)⊆ closedBall (station P v q) (moonClock P v):=by
 intro x h; apply (dist_pi_le_iff (clockP P v).le).2; intro i; let z:=home P rayPost v; let y:= Gx q v; have he:= h i; change |x i-y i|≤ _ at he; change |x i-(z i+y i)| ≤ _; rw [show x i-(z i+y i)= (x i-y i)-z i from by ring]; exact (abs_sub ..).trans ((add_le_add_left he _).trans (u _))
variable (w:ℝ) (pW:0<w) -- shadow p existing; CARE define.
abbrev Rich (v:ℕ)(x: Set Vantage)(i:P.Test)(g:Bool):Prop:= P.asked_at v i x∧i∈enclave P.calibration ∧ if g then RibbonDoc.SpiritGlow P i else Six.PureMatter P.calibration i
include pW ρ
lemma both (pv:skit)(f:Rampart.Supported F G pv (w/2)):
 ∀ᶠ v:ℕ in atTop, (∀ x∈ Seats P v F, Rich P v (closedBall (pv false) w) (cornea P M pHw e K v mu z x) false)∧ ∀ x∈Seats P v G, Rich P v (closedBall (pv true) w) (brass P ρ v x) true:=by
 have h:Tendsto (fun n=>2*ν n+moonClock P n+w/2) atTop (𝓝 (w/2)):=by simpa using ((P.macroStep_zero.const_mul (2:ℝ)).add (small_clock P ρ)).add_const (w/2)
 filter_upwards [h.eventually (ge_mem_nhds (half_lt_self pW)),eventually_ge_atTop f0] with v h hv; let t:=(ρ.date.stock _ hv).2; let q:= (v★ v) z; let Y':= (JpriceApp P rayPost M rayP q mu v); let B':= soloV P v t rayPost rayP pseV; let t':=tollηw P (fun _=>1) v; let W:=moonClock P v
 constructor
 · intro x hx; let N:= cornea P M pHw e K v mu z x; change Rich P v _ N _; let S:= aE (pv false) w; have g:P.Aperture Y' (P.meshPose v x) ⊆ S:=by
      refine (paysAt P (v:=v) Y' 0 (fun i=>?_) _).trans (fun i h'=> Rampart.along_up P F v _ _ _ _ f.basis₀ h x hx i h'); unfold Y'; rw [Hmu_width]; exact le_trans (add_le_add_right (home_room P rayP ..) _) (windMoney P ρ hv)
   have ht := RibbonDoc.inside P x Y' S rfl g; exact ⟨ht.1,ht.2, (if_neg Bool.false_ne_true).symm ▸ spinBill P x M q mu⟩ -- if rewrite precedence
 intro x hx; let S:=aE (pv true) w; have g:P.Aperture B' (P.meshPose v x) ⊆ S:=by
    refine (paysAt P (v:=v) B' 0 (fun i=>?_) _).trans (fun i h'=>Rampart.along_up P G v _ _ _ _ f.basis₁ h x hx i h'); unfold B'; rw [solo_width]; exact (add_le_add_right (home_room P rayP ..) _).trans (windowLaw P ρ hv)
 let N:=RunK P x t; rw [brass,dif_pos hv]; let y:= (↑(psScale P ρ v):ℂ); have ht:= RibbonDoc.inside P x B' S rfl g; refine ⟨asking_scale P S N y ht.1, Subalgebra.smul_mem _ ht.2 y,?_⟩; rw [if_pos rfl]; exact physH P N (lensColor P x t) y
omit pW ρ
variable (S:Set Vantage)(u:ℕ)
local notation "Church" x:max g:max=> Rich P u S x g
lemma rich_zero (b:Bool):Church 0 b:=by refine ⟨asking_zero P S,Subalgebra.zero_mem _,?_⟩; cases b; exact Six.LinkIndependent.zero'; exact colour_zero P
lemma rich_add {uT V:P.Test}{b:Bool}(p:Church uT b)(q:Church V b):Church (uT+V) b:=by
 obtain ⟨h,u,g⟩:=p; obtain ⟨e,w,k⟩:=q; refine ⟨asking_sum P uT V h e,Subalgebra.add_mem _ u w,?_⟩; -- placeholder explicit h,e
 cases b; · rw [if_neg Bool.false_ne_true] at g k ⊢; exact Six.LinkIndependent.plus' g k
 rw [if_pos rfl] at g k ⊢; exact psyche P _ _ g k
lemma rich_scale {uT:P.Test}{b:Bool}(p:Church uT b)(y:ℂ):Church (y • uT) b:=by
 obtain ⟨h,u,g⟩:=p; refine ⟨asking_scale P S uT y h,Subalgebra.smul_mem _ u y,?_⟩
 cases b; · rw [if_neg Bool.false_ne_true] at g ⊢; exact Six.LinkIndependent.scale' g y
 rw [if_pos rfl] at g ⊢; exact physH P _ g y
lemma rich_sell {I:Type*}(M:Finset I)(V:I→ P.Test)(b:Bool)(t:∀ i∈M, Church (V i) b) : Church (∑ i∈M, V i) b:= by
 induction M using Finset.induction_on with
 | empty=> rw [sum_empty]; exact rich_zero ..
 | insert j M h ih=> rw [sum_insert h]; exact rich_add P S u (t _ (mem_insert_self _ _)) (ih fun i h=>t _ (mem_insert_of_mem h))
#print axioms both
end Freeport
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
