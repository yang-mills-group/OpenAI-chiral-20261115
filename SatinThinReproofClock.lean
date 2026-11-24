import SatinFixedContrastNovember4
import SatinThinReproof
import SatinThinFieldInteraction
/-! # Spacetime coordinate and displacement budget for testing the actual continuation in the problem.

Use the purchased E4 and Vantage conventions. Test with the very same spatial vector
as in the fixed centers. E.g., give even cube radius 1/4, about each Mink
center (not altering the REAL Euclidean calculation); no assertion about arbitrary
wider budgets. Even its entire width would be permitted in each late stencil iteration if
making such a continuation. But in fact this construction TESTS negatively for
actual labels and against the attempts below. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 330000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open YM.SatinMacro YM.SatinEdge
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "S"=> P.seasons 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "E!"=> (S).E
local notation "U!"=> (S).U
local notation "κ"=> (S).unit
local notation "ℒ"=> Lead.Clan

-- with time axis #3 last. Keep the whole spatial displacement of the Thin lab
abbrev sameRest (p:Vantage): OS.Cross timeAxis:= transverse 3 (fun i=>p i.val)
def sameTravel(p:Vantage)(t:ℝ):E4:= joinST (sameRest p) t
def rollCall(p:Vantage)(t:ℝ):Vantage:= Function.update p (3:Axis) t
local notation "travel"=> Spine.sameTravel
lemma roll_price_time (p:Vantage)(t:ℝ) : rollCall p t 3=t:= Function.update_self ..
lemma roll_away (p:Vantage)(t:ℝ)(i:Axis)(v:i≠3): rollCall p t i=p i := Function.update_of_ne v ..
lemma roll_uses (p:Vantage)(t:ℝ): P.cartage 3 ξ (rollCall p t)= (S).U (sameRest p):=
 (Spine.of_slideP x 3 (rollCall p t) p (roll_away p t)).trans (P.uses_cart 3 ξ p)
-- arbitrary Mink displacement time. *** NOT Euclidean price time ***
lemma roll_real (p:Vantage)(t:ℝ)(i:Axis): travel p t i=rollCall p t i:= by
 by_cases h:i=3; · subst i; exact (joinST_clock ..).trans (roll_price_time p t).symm
 rw [roll_away p t i h]; change ((sameRest p).val+t • YM.basis timeAxis:E4) i=_; rw [PiLp.add_apply,PiLp.smul_apply]; simp only [basis_eq,(show i ≠ timeAxis from h),if_false]; rw [smul_zero,add_zero]; exact transverse_eyes 3 _ ⟨i,h⟩
lemma roll_static (v:E4) : (κ).translation v Ω=Ω:= static (S) Ω (((S).fixed _).2 (P.heaven_hot 3 ξ)) (fun a=>by
 let u:Vantage:=fun i=> a.val i; have he: U! a = P.cartage 3 ξ u:=(congrArg U! (eyes_toFace 3 a)).trans (P.uses_cart 3 ξ u).symm
 rw [he]; exact P.cart_empty 3 ξ u) v

/-- Any claimed pair-supports within these true bounding regions.
Can use *this* test without claims on arbitrarily large footprints. -/
def compassBudget : Set E4:= {x|∀ i:Axis, |x i| ≤ 1/4}
lemma compass_origin : (0:E4) ∈ compassBudget:= by intro i; change |(0:ℝ)|≤_; norm_num
variable (p:Vantage) (e: 2 < p 0) {t:ℝ}(u:|t|≤1)
include e u
-- Space #0 Euclidean-price displacement already >2. Use this in Mink metric and pay at MOST 1/4 shift on each side, both axes#0 and #3; hence true for the entire appearances. Centered at zero first for the test. Can shift for p and q once this is paid.
lemma compass_apart : Apart compassBudget (there (travel p t) compassBudget):= by
 rintro x a v ⟨y,b,rfl⟩; let v:= y+travel p t-x
 have he: ‖spatial v‖≥ |y 0+p 0-x 0|:= by
    have hz: spatial v (0:Fin 3)= y 0+p 0-x 0:=by change y 0+travel p t 0-x 0=_; rw [roll_real,roll_away _ _ _ (by decide)]
    nth_rewrite 1 [← hz]; exact PiLp.norm_apply_le (spatial v) _
 have h:YM.time v=y 3+t-x 3:= by rw [show v=y+travel p t-x from rfl,sameTravel, drift_clock]; rfl
 apply (Mink.lateral v).mpr; rw [h]; obtain ⟨p₁,p₂⟩:= abs_le.mp u; refine abs_lt.mpr ⟨?_,?_⟩ <;> linarith [(abs_le.mp (a 0)).1,(abs_le.mp (a 0)).2,(abs_le.mp (b 0)).1,(abs_le.mp (b 0)).2,(abs_le.mp (a 3)).1,(abs_le.mp (a 3)).2,(abs_le.mp (b 3)).1,(abs_le.mp (b 3)).2,le_abs_self (y 0+p 0-x 0)]
lemma compass_detect : travel p t ∈ Mink.spacelike:= by
 let a:=travel p t; simpa using compass_apart p e u _ compass_origin (0+travel p t) (mem_image_of_mem _ compass_origin)
omit e u
-- same cost includes even Mink-time radii as given by ACTUAL Apron label(s)
abbrev apronBudget (A:P.Apron):Set E4 := {x:E4| WithLp.ofLp x ∈ P.Aperture A 0}
lemma compass_width (A:ℕ→P.Apron)(ht:P.thicknessZero A): ∀ᶠ i in atTop, P.apronBudget (A i) ⊆ compassBudget := by
 filter_upwards [eventually_all.mpr (fun i:Axis=>(ht i).eventually (gt_mem_nhds (show 0<(1:ℝ)/4 by norm_num)))] with i h y z j
 simpa only [Pi.zero_apply, sub_zero] using le_trans (z j) (LT.lt.le (show (A i).realWidth P j < (1:ℝ)/4 from h j))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.compass_apart
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.compass_width
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.roll_static
