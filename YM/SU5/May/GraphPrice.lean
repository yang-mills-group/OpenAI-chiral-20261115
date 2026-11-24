import YM.SU5.May.CorridorsEu
import YM.SU5.May.RegistrationFort
import YM.SU5.Reconstruction.Moat.Verso
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
open Selected (doorstep indoor fort ride peninsula vocation displacement compass_origin placement atEstate vocate)
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget
local notation "ℳ" => marks (timeMesh P.par)
local notation "Q" => Follows Y L V G j (C j) χ
local notation "K" => P.calibration
local notation "D'" => Domain Y L G
local notation "X'" => Sky K
local notation "Hr" => Selected.ride Y L V H H₁ j false (C j) χ
local notation "R" => peninsula Y L V H H₁ j false (C j) χ
local notation "Pₓ" => P.maySaunters x j
local notation "P₀" => (Pₓ).orthogonalProjectionOnto
local notation "M" => P.mayFort x j
local notation "Ω'" => vocation Y L V H H₁ j false (C j) χ
local notation "ι" => OSvector Y L V G j (C j) χ
local notation "Ψ" => osValue Y L V G j (C j) χ
local notation "α" => P.glasshouseCharacter 3 x
local notation "Z" => P.mayCarries x j
local notation "mv" => FirstWindows.move K
local notation "ej" => Chambers.eject j
local notation "tk" t:max => FirstWindows.ticket Y L G t
/-! CP1 buy the actual two-operator Follows product, its EU price with or without compass projection,
and the kets (at zero seam) identified. -/
local notation "mov" t:max f:max => FirstWindows.move K (Chambers.eject j t) f
lemma mayShiftSum (t s:ℳ)(f:X') : mov t (mov s f) = mov (t+s) f := by rw [move_sum,selectRay]

variable {t: marks (timeMesh P.par)} {f₀ g₀ : Sky (tent P.run P.large)} {X B : (P.mayHil x j).Op}
lemma mayForwardOrigin (h: Q f₀ t X) (u:ℳ)(p:0 ≤ u) (z:D' false (flank j 0))(e:z.val= mov u f₀):
    ι z = (Hr).E (Real.toNNReal (u:ℝ)) (X Ω):= by
  let w: f₀∈ D' false (flank j 0):= domain_mono Y L G (Chambers.strip_in j _) h.pose
  rw [show z=⟨_,e ▸ z.property⟩ from Subtype.ext e]
  rw [transported_ket Y L V G j (C j) χ f₀ w (ej u) (by rw [eject_at]; exact p)]
  rw [ChargeFrame.heatbill Y L V G j (C j) χ u]; exact congrArg _ (ChargeFrame.answer_oper Y L V G j (C j) χ h rfl)

variable (F U:SampleDose)(D : P.MayBooth F reviewEarlierBox) (E : P.MayBooth U reviewLaterBox)
local notation "Δ" => P.mayGap j F U D E
local notation "dℝ" => Real.toNNReal (Δ:ℝ)
lemma mayTotal_positive : 2 < ((Δ):ℝ) := by
  have w:= P.booths_gap j F U D E; change 2<(E.low j:ℝ)-(D.high j:ℝ); linarith
lemma mayEarly_negative : 0 ≤ -(D.high j) := by
  have h:= D.insideMax j; change (D.high j:ℝ) < -1 at h; change (0:ℝ) ≤ - (D.high j:ℝ); linarith
lemma mayLate_positive : 0 ≤ E.low j := by
  have h:= E.insideMin j; change 1 < (E.low j:ℝ) at h; change (0:ℝ) ≤ (E.low j:ℝ); linarith
lemma mayReversed (f : X') : Reflector.reversion K P.par j (D.width j) (mov (- D.low j) f)= mov (D.high j) (flipMark j K f) := by
  unfold Reflector.reversion; rw [flipped_moves, reverse_eject,neg_neg,P.mayShiftSum]; simp only [MayBooth.width,sub_add_cancel]
variable (h : Chambers.Follows P.run P.large P.law P.projection j (P.room j) (P.mayChar x j) (FirstWindows.move (tent P.run P.large) (eject j (-D.low j)) f₀) (D.width j) X)
  (g : Chambers.Follows P.run P.large P.law P.projection j (P.room j) (P.mayChar x j) (FirstWindows.move (tent P.run P.large) (eject j (-E.low j)) g₀) (E.width j) B)
include g in
lemma mayLateKet (z : D' false (flank j 0))(p:z.val=g₀):
    ι z=(Hr).E (Real.toNNReal (E.low j:ℝ)) (B Ω):= by
  refine P.mayForwardOrigin x j g _ (P.mayLate_positive j U E) z (p.trans ?_); rw [P.mayShiftSum,add_neg_cancel,eject_zero,move_by_zero]
include h in
lemma mayEarlyKet (z : D' false (flank j 0))(p:z.val=flipMark j K f₀):
    ι z=(Hr).E (Real.toNNReal (-(D.high j:ℝ))) ((star X) Ω):= by
  have g:=Reflector.fromBack Y L V G C 3 α j (mov (-D.low j) f₀) (D.width j) h (D.allowance j)
  refine P.mayForwardOrigin x j g (-D.high j) (P.mayEarly_negative j F D) z (p.trans ?_)
  rw [P.mayReversed j F D, P.mayShiftSum,neg_add_cancel,eject_zero,move_by_zero]
lemma eject_subtract (u v : ℳ) : ej u - ej v = ej (u-v):=by rw [sub_eq_add_neg,←LightBudget.eject_neg,selectRay,sub_eq_add_neg]
include h g in
lemma mayOrderedOp : Follows Y L V G j (C j) χ
    (FirstWindows.move K (ej (-D.low j)) (f₀*g₀)) (E.high j-D.low j)
    (X * (Hr).E dℝ * B) := by
  let F':= mov (-D.low j) f₀; let U':= mov (-E.low j) g₀; let v:= E.low j-D.low j; let d:= E.high j-D.low j
  have hp: (D.width j:ℝ)< ((eject j v j):ℳ):= by
    rw [eject_at]; change (D.high j:ℝ)-(D.low j:ℝ)<(E.low j:ℝ)-(D.low j:ℝ); linarith [P.booths_gap j F U D E]
  have hv : v+E.width j=d:=by unfold MayBooth.width v d; abel
  have hz : ((ej v j+E.width j:ℳ):ℝ) ≤ (d:ℝ):=by rw [eject_at,hv]
  have ht:= ChargeFrame.boxAfter Y L V G j (C j) χ (x:=F') (y:=U') (ej v) d (D.allowance j).le
    (E.allowance j).le hp hz h g
  have he: FirstWindows.move K (ej (-D.low j)) (f₀*g₀) = F'*mov v U' := by
    unfold F' U'; rw [P.mayShiftSum, show v+ -E.low j = -(D.low j) from (by unfold v; abel),move_prod]
  rw [show eject j v-eject j (D.width j) = eject j Δ from (P.eject_subtract j _ _).trans (congrArg (ej) (by unfold v mayGap MayBooth.width; abel)),
    ChargeFrame.heatbill,selectRay,hv,sub_self,
    show (0: Selected.placement P.par)=eject j (0:ℳ) from (eject_zero ..).symm,
    ChargeFrame.heatbill, show Real.toNNReal ((0:ℳ):ℝ) =0 from (by simp only [AddSubgroup.coe_zero,Real.toNNReal_zero]),(Hr).eZero] at ht
  rw [he]; exact ((mul_one (X * (Hr).E dℝ * B)) ▸ ht) -- tuning id
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
