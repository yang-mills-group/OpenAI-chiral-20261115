import YM.SU5.Registration.SpinePad

/-!
# M4 domain and operator estimates towards registration

On this data, no extra hypothesis for the convergence in the domain
of the vacuum column/padded width operations on vacuum. Then towards
higher words: reconstruct directly on this same character, charging operator
estimates (`CapReady`) at each given symmetric t>0 of the ACTUAL positive-width
padded **point** operators. Those are new inputs, not inferred from the
unpadded tempered two-point measures. Not addressing all determining-family
properties yet, don't assume this gives local Poincaré or interaction.

Preserve exactly the instrument readings; can recover the F/U Euclidean
continued readings from the *same field prescription*, NOT a result about
the corresponding numeric value on Minkowski supports. MatchTest enforces
the Wightman two-point identification in the tested order. The port keeps
the fixed measurement geometry & formula so the remaining problems can
use that map.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "Ω" => P.heaven 3 ξ
local notation "G" => bands (P.seasons 3 ξ)
local notation "T" => (P.seasons 3 ξ).E

lemma inside_domain : Ω ∈ D := by
  have ht:= heat_domain (S) (Ω) (s:=1) zero_lt_one
  rw [P.heaven_hot 3 ξ] at ht; exact ht
abbrev vacuumEntry : D:= ⟨Ω,P.inside_domain x⟩

variable (W : P.Apron)
lemma valise_vacuum (B : (H).Op) (f : Test4) : Seld.valise (S) B f Ω= collect (S) f (B Ω) := by
  rw [Seld.vmap,collect_eq]; apply integral_congr_ae; filter_upwards with i
  change f i • ((S).unit.translation i (B ((S).unit.translation (-i) Ω)))=_; rw [P.roll_static]
lemma vacuum_bill (B : (H).Op) (f : Test4) : warm (S) B f (P.vacuumEntry x)= gathers (S) f (B Ω):=
  Subtype.ext ((warm_actual (S) B f _).trans (P.valise_vacuum x B f))
lemma manage_vacuum (y : P.birthF 3 W.s W.F) {t : ℝ≥0} (p : P.priceWidth W ≤ t) :
    P.manage x W t Ω = P.cradleG x W y t:= by
  let d:=P.priceWidth W
  change T (t-d) (P.realTable x W (T (t-d) Ω))=_
  rw [P.heaven_hot 3 ξ,P.roll_label_pay x W y]; unfold cradleG; rw [Real.toNNReal_coe]
  exact DFunLike.congr_fun (((S).time (t-d) d).symm.trans (congrArg (T) (tsub_add_cancel_of_le p))) _

-- first registration family. Either side; keep the probe mark list label
-- for consuming CapReady (not all determining families implemented).
abbrev Instrument := Lead.Clan × Bool
abbrev positiveLabel (a:Lead.Clan) : Instrument := (a,true)
abbrev negativeLabel (a:Lead.Clan) : Instrument := (a,false)
abbrev reverseProbe (a : Instrument) : Instrument := (a.1,!a.2)

variable (A : ℕ→P.Apron) (c r n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
    (X : P.HandleWith x c r A n)
    (F U : SampleDose) (Y : Lead.Clan → Test4→L[ℂ] (P.ManyF 3 (P.advocate 3 x 3))) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4)
local notation "Λ" => P.profilesZ x V w
local notation "W" => P.soldTrumpet A c r n w
local notation "b[" a "," i "]" => P.sold_birth x A c r n w a i X

/-- The partner uses kiss on `Apron` in THIS calendar. -/
def registeredStamp (j : Instrument) (i : ℕ): P.Apron:= if j.2 then W j.1 i else (W j.1 i).kiss P 3
abbrev pointBill (j : Instrument) (s : ℝ≥0) (i : ℕ) := P.manage x (P.registeredStamp A c r n w j i) s
local notation "Y₀" => P.AtZeroHeat x A c r n w V X F U Y Z
set_option maxHeartbeats 100000
variable {K : P.Register} {f₀ r₀ g h : ℕ}
variable (R : P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox f₀ r₀ K)
local notation "ρ" => 𝓝[>] (0:ℝ≥0)
-- no CapPrice estimates consumed yet
lemma stars_live (e : Y₀) (a : Lead.Clan) (f : Test4) : Y a f ∈ radial (S):=by
  obtain ⟨q,u,p⟩:=e.forecasts
  rw [u]; exact wake_radial (S) _ (q _) f
include R
lemma radial_stars (e : Y₀) (a : Lead.Clan) (f : Test4) :
    (bands (S)).Approaches ρ (fun t=> gathers (S) f (Λ a (t:ℝ))) ⟨Y a f, P.stars_live x A c r n w V X F U Y Z e a f⟩ := by
  obtain ⟨p,u,-⟩:= e.forecasts
  have he:=radial_limit (S) _ (p a) (R.armada.energy a).2.1 f
  rw [show radialWake (S) _ (p a) f= _ from (?_ : radialWake (S) _ (p a) f= ⟨Y a f, P.stars_live x A c r n w V X F U Y Z e a f⟩)] at he; exact he
  apply Subtype.ext; exact DFunLike.congr_fun (u a).symm f
lemma first_stamp_limit (a : Lead.Clan) (f : Test4) (t : ℝ≥0) (p : 0<t) :
    (bands (S)).Approaches atTop (fun i=> warm (S) (P.pointBill x A c r n w (positiveLabel a) t i) f (P.vacuumEntry x)) (gathers (S) f (Λ a t)):= by
  have h:= (R.armada.heated_points a (t:ℝ) (show 0<(t:ℝ) from p)).2
  intro k; refine (gather_approaches (S) f h k).congr' ?_
  filter_upwards [(R.armada.slender a 3).eventually (ge_mem_nhds (show 0<(t:ℝ) from p))] with i u
  have u':P.priceWidth (W a i)≤t:=by change ((P.priceWidth (W a i)):ℝ)≤ (t:ℝ); rw [P.price_exact]; exact u
  rw [P.vacuum_bill, show P.pointBill x A c r n w (positiveLabel a) t i=P.manage x (W a i) t from rfl, P.manage_vacuum x _ b[a,i] u']
omit R
-- The operator estimates the vacuum-convergence test hasn't paid
abbrev CapBacked := ∀ a : Lead.Clan, P.CapReady x (W a)
variable (p : P.CapBacked x A c r n w)
include p
lemma all_backed (j : Instrument) : P.CapReady x (P.registeredStamp A c r n w j) := by
  rcases j with ⟨a,i⟩; cases i
  · exact P.cap_partner x (W a) (p a)
  exact p a
lemma delivery_sold (j : Instrument) : Delivery (S) (P.pointBill x A c r n w j) := P.delivery_cap x _ (P.all_backed x A c r n w p j)
abbrev registeredField (j : Instrument) := P.pointField x _ (P.all_backed x A c r n w p j)
local notation "χ" => P.registeredField x A c r n w p
local notation "B" => P.managed
lemma inverse_stove_field (a : Lead.Clan) : χ (negativeLabel a)= SatinRegistration.adj (S) (P.managed x _ (p a)) ((P.delivery_cap x _ (p a)).isSound) ((P.delivery_cap x _ (p a)).paid) := P.field_partner x (W a) (p a)
lemma distributes (j : Instrument) (x' : D) : Continuous (fun f:Test4=>(χ j f x').1):=field_distribution (S) ..
lemma register_inner (j : Instrument) (f : Test4) (x' y : D) :
    inner ℂ (χ j f x').1 y.1=inner ℂ x'.1 (χ (reverseProbe j) (bar f) y).1 := by
  suffices he : ∀ a:Lead.Clan, ∀ (f:Test4) (x' y:D), inner ℂ (χ (positiveLabel a) f x').1 y.1=inner ℂ x'.1 (χ (negativeLabel a) (bar f) y).1 by
    rcases j with ⟨a,i⟩; cases i
    · have hp:= he a (bar f) y x'; rw [bar_twice] at hp; exact (by rw [← inner_conj_symm, ← hp, inner_conj_symm]; rfl)
    exact he a f x' y
  intro a f x' y
  rw [P.inverse_stove_field]; exact field_adjoint (S) (P.managed x _ (p a)) ((P.delivery_cap x _ (p a)).isSound) ..
lemma register_closable (j : Instrument) (f : Test4) : ((G).asPartial (χ j f)).IsClosable:=field_closable (S) ..
lemma register_shift (j : Instrument) (f : Test4) (m : E4) (x' : D) : SatinRegistration.shift (S) m (χ j f x')= χ j (ahead m f) (SatinRegistration.shift (S) m x') := field_translate (S) ..

include R
lemma limit_profile_paid (a : Lead.Clan) (s : ℝ≥0) (u : 0<s) : (P.delivery_sold x A c r n w p (positiveLabel a)).accepts s Ω = Λ a s := by
  let K : ℕ→(H).Op := fun i=> P.manage x (W a i) s
  refine tendsto_nhds_unique (l:=atTop) (f:=fun i=> K i Ω) ((P.delivery_sold x A c r n w p (positiveLabel a)).accepted s u Ω) ?_
  refine (R.armada.heated_points a (s:ℝ) (show 0<(s:ℝ) from u)).2.congr' ?_
  filter_upwards [P.eventuallyCovered x _ (p a) s u] with i h; exact (P.manage_vacuum x _ b[a,i] h.le).symm
lemma registered_vacuum (e : Y₀) (a : Lead.Clan) (f : Test4) :
    (χ (positiveLabel a) f (P.vacuumEntry x)).1 = Y a f := by
  let k:=P.delivery_sold x A c r n w p (positiveLabel a)
  have ht:= passes_lim (S) _ k.isSound k.paid (l:=ρ) f id id (tendsto_id : Tendsto id ρ ρ) tendsto_id (x:=P.vacuumEntry x) (X:=fun _=> P.vacuumEntry x) (by intro n; simp_rw [sub_self,Grading.budget,Grading.due,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds)
  refine tendsto_nhds_unique (Grading.Approaches.hilbert _ ht) ?_
  refine (Grading.Approaches.hilbert _ (P.radial_stars x A c r n w V X F U Y Z R e a f)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with i t; change _=(warm (S) (bothPads (S) k.accepts i i) f (P.vacuumEntry x)).1
  rw [show bothPads (S) k.accepts i i=k.accepts i from (by unfold bothPads; rw [min_self,tsub_self,(S).eZero]; exact ((congrArg (· * (1:(H).Op)) (one_mul (k.accepts i))).trans (mul_one _))), P.vacuum_bill, show k.accepts i Ω=_ from P.limit_profile_paid x A c r n w V X F U R p a i t]
lemma registered_tie (e : Y₀) (a b : Lead.Clan) (f g' : Test4) : Z a b (tieAt f g') =
    inner ℂ Ω ((χ (negativeLabel a) (bar f)) ((χ (positiveLabel b) g') (P.vacuumEntry x))).1 := by
  rw [e.matchTest, ← P.registered_vacuum x A c r n w V X F U Y Z R p e, ← P.registered_vacuum x A c r n w V X F U Y Z R p e]
  exact P.register_inner x A c r n w p (positiveLabel a) f (P.vacuumEntry x) _

-- Attach the F/U protocol to the same padded field prescription,
-- via their given Euclidean interpretation. This cross kernel is amiss
-- without projection qualifiers if trying to multiply grid mark operators.
-- Exact widths and field correspondence before any Lorentzian claim.
local notation "β" => P.delivery_sold x A c r n w p
local notation "𝕂" a => (P.delivery_sold x A c r n w p (positiveLabel a)).accepts
/-- left operand a Euclidean `kiss`, so adjoint of positive-label engine.
Interpret this kernel only at strictly positive time gaps. -/
def onFields (a b : Lead.Clan) (y : Vantage) := let t:=Real.toNNReal (y 3/2)
                                             inner ℂ ((𝕂 a) t Ω) (P.cartage 3 ξ y ((𝕂 b) t Ω))
lemma carried_price (a b : Lead.Clan) (y : Vantage) (u : 0<y 3) : P.onFields x A c r n w p a b y= P.pointPrism x V w y a b := by
  have h:= Real.toNNReal_pos.mpr (half_pos u); unfold onFields; dsimp only
  rw [P.limit_profile_paid x A c r n w V X F U R p a _ h, P.limit_profile_paid x A c r n w V X F U R p b _ h, Real.coe_toNNReal _ (half_pos u|>.le)]; rfl
-- annotate height order
lemma registration_reading (a b:Lead.Clan) : P.readPrism x V w 1 F U a b=
    ∫ y:Vantage,∫ z:Vantage,(F.val y:ℂ)*(U.val z:ℂ)*P.onFields x A c r n w p a b (z-y):= by
  rw [R.then_read.integral]
  apply integral_congr_ae (Eventually.of_forall fun y=>?_)
  apply integral_congr_ae (Eventually.of_forall fun z=>?_)
  by_cases hy:F.val y=0; · simp [hy]
  by_cases hz:U.val z=0; · simp [hz];
  rw [P.carried_price x A c r n w V X F U R p a b _ ((by change 0<z 3-y 3; linarith only [thin_separation y z (R.supports.1 (subset_closure hy)) (R.supports.2 (subset_closure hz)) 3]) )]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
