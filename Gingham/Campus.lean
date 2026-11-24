import Gingham.Ecru
import Gingham.OneField
import YM.SU5.Registration.Affine.Constellation
/-! # Field registration uses M8 cap, not Wadding strength H
All arms have true widths, not subsequent refinement width used as if
making stamps at it! Everything at axis 3 of advocate of this fixed election;
same domain, weights and appointment for all. The stronger M8 purchase
(not `wadding_satin`) is intended.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ

structure Hook where
  arms : P.Swatch
  earns : arms.WPermit x 3

def Hook.west (a:Hook P x) : Hook P x :=
  ⟨a.arms.turn 3, a.earns.reflector x 3 _⟩

abbrev toll (a:Hook P x) : Quote P x :=
   a.earns.atHeat

lemma toll_adj (a:Hook P x) (d:ℝ≥0) :
    star (toll P x a d) = toll P x (a.west P x) d := by
  have he: (fun t=> (a.earns.atHeat t).adjoint) = (a.west P x).earns.atHeat :=
     (a.earns.delivery.reverse (a.west P x).earns.delivery
       (fun s i=> (a.arms.Wstage_turn x 3 i s s).symm)).symm
  exact congrFun he d

lemma paid_on_G (a: Hook P x) : (𝓢).Cashable (toll P x a) :=
   credited _ _ a.earns.delivery.isSound a.earns.delivery.paid

/-- Real field map; same positive order purchase. -/
def pelisse (a: Hook P x) : (𝓢).Detector := (𝓢).seated (paid_on_G P x a)

lemma collects (a:Hook P x) : (𝓢).Instates (toll P x a) (pelisse P x a) :=
   (𝓢).seated_in _

/-- Deployment to Organza's bounded-in-graph apparatus, determination,
adjoints, pruned/word results simultaneously. -/
theorem solstice : (𝓢).Fray (toll P x) (pelisse P x) :=
   ⟨collects P x, fun a=>⟨a.west P x,Eventually.of_forall (toll_adj P x a)⟩⟩

/-- M8 field also acts here and gives identical vectors wherever both
prescriptions ask (therefore `OverM4` at that vacuum and all word
field uses there; not asking identification of definitions of the two domains). -/
abbrev face8 (a:Hook P x) :=
   SatinRegistration.field _ (toll P x a) a.earns.delivery.isSound a.earns.delivery.paid

lemma pelisse_on_both (a : Hook P x)
    (f:Test4) (u:D) (w:radial 𝓢) (t:u.val=w.val) :
    (pelisse P x a f u).val = (face8 P x a f w).val :=
   concord (collects P x a) a.earns.delivery.isSound a.earns.delivery.paid f u w t


/- ## Determined: compact-test actions on the cyclic polynomial subspace. -/
local notation "𝓟"=> pelisse P x
local notation "𝓟eu"=> toll P x
abbrev here : Submodule ℂ D := (𝓢).sprout 𝓟 Ω

def EqualOnBooks (a b:Hook P x) : Prop :=
  ∀ f, LocalTest f → ∀ u∈here P x,∀ v∈here P x,
      inner ℂ v.val (𝓟 a f u).val = inner ℂ v.val (𝓟 b f u).val

lemma equal_prices {a b:Hook P x} (e:EqualOnBooks P x a b)
    {d : ℝ≥0} (g:0<d) :
    EqOn ⇑(𝓟eu a d) ⇑(𝓟eu b d) ((𝓢).nursery 𝓟 Ω: Set (G).space) :=
    (solstice P x).determines (v:=Ω) (home_basis P x).2 a b e g

lemma equal_pledges {a b:Hook P x} (e:EqualOnBooks P x a b)
    {d : ℝ≥0} (g:0<d) :
    𝓟eu a d ω₁ = 𝓟eu b d ω₁ ∧
    star (𝓟eu a d) ω₁ = star (𝓟eu b d) ω₁ := by
  let N := (𝓢).nursery 𝓟 Ω
  have ow : ω₁ ∈ N := OS.Semigroup.reflected _ (at_bud _ 𝓟 Ω)
  have eg := equal_prices P x e g
  have m (i:Hook P x) : star (𝓟eu i d) ω₁ ∈ N := by
    rw [toll_adj]
    exact ((solstice P x).pruned_keep (v:=Ω) (home_basis P x).2 _).2 d g ow

  refine ⟨eg ow,sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp ?_)⟩
    -- evaluate at one w
  let w:= star (𝓟eu a d) ω₁ - star (𝓟eu b d) ω₁
  change inner ℂ (_-_) w=0
  rw [inner_sub_left, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
     ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h : w ∈ N := N.sub_mem (m _) (m _)
  rw [eg h,sub_self]

lemma euValues {a b:Hook P x} (e:EqualOnBooks P x a b)
    {d : ℝ≥0} (g:0<d)
    (l r:ℝ) (F:SampleDose) :
    let E := fun z:Hook P x=>P.flounce 3 ξ d l r (𝓟eu z d) F
    E a ω₁ = E b ω₁ ∧ star (E a) ω₁ = star (E b) ω₁ := by
  have h := equal_pledges P x e g
  dsimp only
  constructor
  · rw [flounce_act,flounce_act]
    simp_rw [cloaked,pad_val,mul_apply_eq_comp,P.cart_empty,P.heaven_hot,h.1]
  · rw [star_flounce,star_flounce]
    simp_rw [pad_val,mul_apply_eq_comp,P.cart_empty,P.heaven_hot,h.2]


/-- Changing representatives (holding even just the local algebra readings) does
NOT change *either* answer for this joint Eu test or real test. Note what the
inputs are: local field channels each with their placement/test, not in the Eu
case bare values of their single smear regarded as real operators. In the
real case even that last information suffices, directly by definition, on full D. -/
theorem descend_eu {g g' m m' : Hook P x}
    (e:EqualOnBooks P x g g') (h:EqualOnBooks P x m m')
    (a:Weave) :
    let L := fun z:Hook P x=> EuLeft P x a (𝓟eu z)
    let R := fun z:Hook P x=> EuRight P x a (𝓟eu z)
    coupled ω₁ (L g) (R m) = coupled ω₁ (L g') (R m') ∧
    OS.Semigroup.Gingham.forecast ω₁ (L g) (R m) = OS.Semigroup.Gingham.forecast ω₁ (L g') (R m') := by
  have q := euValues P x e a.topay a.l 0 a.blot
  have t := euValues P x h a.topay 0 a.r a.well
  intro L R
  have t' : R m ω₁=R m' ω₁ := t.1
  constructor
  · have h(z y:(G).Op) : coupled ω₁ z y = inner ℂ (star z ω₁) (y ω₁) :=
      (ContinuousLinearMap.adjoint_inner_left z (y ω₁) ω₁).symm
    simp_rw [h,show star (L g) ω₁=star (L g') ω₁ from q.2,t']
  simp only [OS.Semigroup.Gingham.forecast, OS.Semigroup.Gingham.cup,t', show L g ω₁=L g' ω₁ from q.1]


/-- Compare even just the two actual (possibly polynomial)
real **algebra elements** on (compact-test polynomial)-cyclic;
for bounded-region localizations product vectors stay on that sprout. -/
theorem descend_real
    {L R L' R' : Module.End ℂ D}
    (h : EqOn ⇑L ⇑L' (here P x))
    (v : EqOn ⇑R ⇑R' (here P x))
    (m : R Ω ∈ here P x) :
    rcoupled 𝓢 Ω L R = rcoupled 𝓢 Ω L' R' ∧
    rforecast 𝓢 Ω L R = rforecast 𝓢 Ω L' R' := by
  have hg : Ω ∈ here P x := at_bud ..
  constructor
  · have e : L (R Ω)= L' (R' Ω):= (h m).trans (congrArg L' (v hg))
    unfold rcoupled rcup
    exact congrArg (inner ℂ ω₁ ∘ Subtype.val) e
  simp only [rforecast, rcup,h hg,v hg]

lemma identified {a b:Hook P x} (h:EqualOnBooks P x a b)
    {f:Test4} (t:LocalTest f) :
    EqOn ⇑(𝓟 a f) ⇑(𝓟 b f) (here P x) := by
  intro y p
  let w:= 𝓟 a f y - 𝓟 b f y
  have e : w ∈ here P x :=
     (here P x).sub_mem (pruned a t _ p) (pruned b t _ p)
  refine sub_eq_zero.mp (show w=0 from Subtype.ext ((inner_self_eq_zero (𝕜:=ℂ)).mp ?_))
  change inner ℂ w.val ((𝓟 a f y).val - (𝓟 b f y).val)=0
  rw [inner_sub_right,h f t y p _ e,sub_self]

/-! ## Marginal prices match even at normalized real inputs -/
lemma real_dose_actual (a:Hook P x)
    {d:ℝ≥0} (p:0<d)
    (F:SampleDose)(y:F.Normalized) :
    rcup 𝓢 Ω (𝓟 a (sachet_LocalFieldBounds F)) = cup ω₁ (𝓟eu a d) := by
  let Q := 𝓟eu a d
  let f := sachet_LocalFieldBounds F
  have h : (T d) (𝓟 a f Ω).val =
     ∫ t:E4, f t • (𝓢).dangle t Q ω₁ := by
    have e := DFunLike.congr_fun ((collects P x a).guard f d p) Ω
    change _ = (𝓢).heatL d (𝓟 a f ((𝓢).heatL d Ω)) at e
    rw [show (𝓢).heatL d Ω=Ω from Subtype.ext (P.heaven_hot 3 ξ d)] at e
    exact congrArg Subtype.val e.symm
  change inner ℂ ω₁ _ = _
  nth_rw 1 [← P.heaven_hot 3 ξ d]
  rw [← ContinuousLinearMap.adjoint_inner_right,(𝓢).sym,h]
  rw [← integral_inner ((𝓢).unsoiled Q f _)]

  suffices hh : (∫ t:E4, f t * cup ω₁ Q) = cup ω₁ Q by
    refine (integral_congr_ae (ae_of_all _ (fun t => ?_))).trans hh
    rw [inner_smul_right,dangle,mul_apply_eq_comp,(home_basis P x).2,
        mul_apply_eq_comp,←ContinuousLinearMap.adjoint_inner_left,
        ←ContinuousLinearMap.star_eq_adjoint,(𝓢).unit_star,(home_basis P x).2]
    rfl
  rw [integral_mul_const,show (∫ t:E4, f t)=1 from sachet_one _ y,one_mul]

lemma Eu_dose_actual (l r d:ℝ) (A:(G).Op)
    (F:SampleDose)(y:F.Normalized) :
    cup ω₁ (P.flounce 3 ξ d l r A F) = cup ω₁ A := by
  have e := P.flounce_act 3 ξ d l r A F ω₁
  unfold OS.Semigroup.Gingham.cup
  rw [e,← integral_inner (velvet_integrable F (P.cloaked_cont 3 ξ d l r A ω₁))]
  have h (z : Vantage) : inner ℂ ω₁ (P.cloaked 3 ξ d l r A z ω₁) =
      inner ℂ ω₁ (A ω₁) := by
    simp only [cloaked,pad_val,mul_apply_eq_comp,P.cart_empty,P.heaven_hot]
    rw [← ContinuousLinearMap.adjoint_inner_left,P.cart_reverses,P.cart_empty,
        ←ContinuousLinearMap.adjoint_inner_left,(𝓢).sym,P.heaven_hot]
  simp_rw [inner_smul_right,h]
  rw [integral_mul_const,integral_complex_ofReal,y.2,Complex.ofReal_one,one_mul]


abbrev simultaneous_at (a:Weave) (g m:Hook P x) : Prop :=
  Scrive a ∧ Caught P x a (𝓟eu g) (𝓟eu m) (𝓟 g) (𝓟 m)

/-- Once the books close (`mistrial` is a finite-target criterion),
a placement with positive discrepancies is bought in both sets of coordinates,
with actual marginals. Weaves' corners and axes strict clearances and
weights are fixed before width limits, common to Eu and real test. -/
theorem assigns {I:Type}
    (g:Hook P x)(m:I→Hook P x)
    (proxy : mistrial 𝓢 ω₁ (𝓟eu g) (𝓟eu ∘ m)) :
    ∃ i a, simultaneous_at P x a (g.west P x) (m i) := by
  obtain ⟨h⟩ := hear_nonzero _ _ _ _ proxy
  exact ⟨h.member, simultaneous P x (A:=𝓟eu g) (B:=𝓟eu (m h.member))
    (paid_on_G _ _ g).1 (paid_on_G _ _ _).1 h.pays h.repays h.geo h.engaged
    (collects _ _ _) (collects _ _ _) (fun d _=> toll_adj P x _ d) (collects _ _ _)⟩

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
