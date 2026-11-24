import YM.SU5.May.Corridors
import YM.SU5.May.RegistrationClock
import YM.SU5.Reconstruction.Seams.Court
import YM.SU5.Reconstruction.PilotLight.Clock
import YM.SU5.Reconstruction.Vermont.Windward
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine

open Aria Germ Alliance SelectionAnalysis Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "C" => P.room
local notation "Y" => P.run
local notation "L" => P.large
local notation "P₁" => P.par
local notation "V" => P.law
local notation "G" => P.projection
local notation "H" => P.history
local notation "H₁" => P.projection.clipped
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J
/-!
The Euclidean operator program, CP1. Full storage of the chosen compact
windows and their clocks & offsets, and of course same χ. Even buy the
paired equality on the compass (where CP27 wants to register these on the
very Mink fields over *that* space), no continuity/cone hypothesis.
-/
open Selected (doorstep indoor fort ride peninsula vocation displacement compass_origin placement atEstate vocate)
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget
local notation "ℳ" => marks (timeMesh P.par)
local notation "Q" => Follows Y L V G j (C j) χ
local notation "K" => P.calibration
local notation "D'" => Domain Y L G
local notation "X'" => Sky K
local notation "Hr" => ride Y L V H H₁ j false (C j) χ
local notation "R" => peninsula Y L V H H₁ j false (C j) χ
local notation "Pₓ" => P.maySaunters x j
local notation "P₀" => (Pₓ).orthogonalProjectionOnto
local notation "M" => P.mayFort x j
local notation "Ω'" => vocation Y L V H H₁ j false (C j) χ
local notation "ι" => OSvector Y L V G j (C j) χ
local notation "Ψ" => osValue Y L V G j (C j) χ
local notation "α" => P.glasshouseCharacter 3 x
abbrev mayCarries := opCarries Y L V G j (C j) χ
local notation "Z" => P.mayCarries x j
local notation "mv" => FirstWindows.move K
local notation "ej" => Chambers.eject j
local notation "tk" t:max => FirstWindows.ticket Y L G t

variable {q : Bool} {F U: SampleDose} {D₀ : Doorway} (D : P.MayBooth F D₀)
variable {f : Sky (tent P.run P.large)}
abbrev panelShift (t:ℳ) (X : Set Vantage) := FirstWindows.slides (coordinates P.par (eject j t)) X
local notation "Dᵤ" => D.box.sealing
local notation "S" t:max A:max => P.panelShift j t A
lemma boothStamps (u : f∈ D' q Dᵤ) : mv (ej (-D.low j)) f∈ D' q (S (-D.low j) Dᵤ) :=
  FirstWindows.moving Y L V G _ f u
lemma boothPanel_compact : IsCompact (S (-D.low j) Dᵤ) :=
  D.box.door_compact.image (continuous_id'.add continuous_const)
lemma boothPanel_ready : S (-D.low j) Dᵤ ⊆ Chambers.strip j 0 (D.width j) := by
  have h:= D.prints j; unfold panelShift; rw [LightBudget.eject_neg, map_neg, Chambers.coordinates_eject]
  apply Set.Subset.trans (Set.image_mono h); rw [show (fun a:Vantage=>a + - (eject j (D.low j:ℝ))) '' Chambers.strip j (D.low j) ((D.low j:ℝ)+(D.width j:ℝ))=_ from Chambers.strip_zero ..]; rw [add_sub_cancel_left]
lemma boothPanel_face : Crease.panelFace j Dᵤ = Crease.panelFace j (S (-D.low j) Dᵤ):=
    (Crease.slide_pin Y L V G j Dᵤ (D.low j) 1 (domain_one ..) (D.width j) (D.prints j)).2.1

def mayOperator (u : f ∈ D' q Dᵤ) : (I₀).Op := stripOp Y L V G j (C j) χ (D.width j) (D.allowance j)
  (mv (ej (-D.low j)) f) (
    (by cases q
        · exact domain_mono Y L G (P.boothPanel_ready j D) (P.boothStamps j D u)
        exact domain_loose Y L G _ (domain_mono Y L G (P.boothPanel_ready j D) (P.boothStamps j D u))))

lemma mayGraph (u : f∈ D' q Dᵤ) : Follows Y L V G j (C j) χ (mv (ej (-D.low j)) f)
    (D.width j) (P.mayOperator x j D u) := stripOp_follows ..
-- Follows permits direct reading on χ, even **before** bringing any backing.
lemma mayGraphReads {A : (P.mayHil x j).Op} {r t: marks (timeMesh P.par)}
    (e : Q (mv (ej t) f) r A) (k:f∈ D' false Set.univ) :
    Ψ ⟨f,k⟩ = inner ℂ Ω (A Ω):= by
  let z := mv (ej t) f; let f₀ : z ∈ D' false (flank j 0):= domain_mono Y L G (Chambers.strip_in j _) e.pose
  let p: z ∈ D' false univ:= domain_le_lawDomain Y L G _ f₀
  let Ht:= ChargeFrame.answer_oper Y L V G j (C j) χ e (v:=⟨z,f₀⟩) rfl
  rw [←Ht, FirstWindows.expectation]; exact (moving_value Y L V G j (C j) χ (eject j t) k p).symm
lemma mayProjectionVac (A:(I₀).Op) : Z A Ω' = P₀ (A Ω) := by
  change P₀ (A (Ω').val)=_; rw [Selected.vocate]
lemma mayRemembers (A:(I₀).Op) : inner ℂ Ω (A Ω) = inner ℂ Ω' (Z A Ω') := by
  refine (congrArg (fun x:I₀=> inner ℂ x (A Ω)) (Selected.vocate ..).symm).trans ?_
  refine (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=Pₓ) Ω' _).symm.trans
    (congrArg (inner ℂ (show M from Ω')) (P.mayProjectionVac x j A).symm)
lemma mayTicketReads (t:ℕ)(g:P.Test)(h: (tk t) g ∈Domain Y L G false Set.univ):
    osValue Y L V G j (C j) χ ⟨(tk t) g,h⟩=P.singleState 3 t x g:=by
  rw [os_ticket_val]; exact P.mayResponse x j t g

section pairs
open Schedule
variable (F U) (D : P.MayBooth F reviewEarlierBox)
  (E : P.MayBooth U reviewLaterBox)
local notation "D₁" => D.box.sealing
local notation "Eᵤ" => E.box.sealing
local notation "W" => P.boothPair F U D E
local notation "Wv" => (W).registerQ
local notation "Δ" => E.low j-D.high j
lemma pureRoute (d : ℳ) : Schedule.route (R) (eject j (d:ℝ)) = (R).E (Real.toNNReal (d:ℝ)) := by
  rw [← Chambers.coordinates_eject j d]; exact bridge_time Y L V G j (C j) χ _
/-- Exact gap to use between these shutters. -/
abbrev mayGap : ℳ := E.low j - D.high j
local notation "ΔP" => P.mayGap j F U D E
local notation "dℝ" => Real.toNNReal ((ΔP):ℝ)
local notation "aℝ" => Real.toNNReal (D.width j:ℝ)
-- two `route`s in CP27 actual continuation
lemma first_leg : Fixture.start Wv j 0 false - Fixture.paste ((W).back j) = ej (D.width j:ℝ) := by
  ext i; by_cases p:i=j <;> simp [Fixture.start, boothPair,Fixture.paste,p,eject]
lemma second_leg : Fixture.start Wv j 0 true - Fixture.stop Wv j 0 false = ej (ΔP:ℝ):=by
  ext i; by_cases p:i=j <;> simp [Fixture.start,Fixture.stop,boothPair,p,eject,mayGap,MayBooth.width]
  <;> try ring
variable {g : Sky (tent P.run P.large)}
lemma mayPair {x' : (P.mayHil x j).Op} {y : (P.mayHil x j).Op}
    (u : f∈ Domain Y L G false D₁) (v : g∈Domain Y L G false Eᵤ)
    (p: Q (mv (ej (- D.low j)) f) (D.width j) x') (m: Q (mv (ej (- E.low j)) g) (E.width j) y)
    (h : f*g∈Domain Y L G false Set.univ) :
    osValue Y L V G 3 (C 3) α ⟨f*g,h⟩ = inner ℂ Ω' (Z x' ((R).E dℝ (Z y Ω'))) := by
  let U':= Chambers.given Y L G W u v
  let B (i:Bool):= signal Y L V G Wv (duet f g) j (C j) χ (U'.shielded j) i
  have t:= (pair_center Y L V G 3 C α W u v ⟨_,h⟩ rfl j).symm
  have r : x'= B false:= by
    apply Chambers.unique_op Y L V G j (C j) χ  (D.width j) p
    rw [LightBudget.eject_neg]
    exact journey_cost Y L V G Wv (duet f g) j (C j) χ (U'.shielded j) false
  have s : y=B true:= by
    apply Chambers.unique_op Y L V G j (C j) χ  (E.width j) m
    rw [LightBudget.eject_neg]
    exact journey_cost Y L V G Wv (duet f g) j (C j) χ (U'.shielded j) true
  rw [r,s]; refine t.trans ?_
  change inner ℂ Ω' (Schedule.route (R) (Fixture.start Wv j 0 false-Fixture.paste ((W).back j))
    (Z (B false) (Schedule.route (R) (Fixture.start Wv j 0 true-Fixture.stop Wv j 0 false) (Z (B true) Ω'))))= _
  rw [P.first_leg j F U D E,P.second_leg j F U D E, P.pureRoute,P.pureRoute, ← (R).swing]
  rw [Crease.seat_cools]
end pairs
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
