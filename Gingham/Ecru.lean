import Gingham.Dart
import Velour.Wadding.Glints
/-!
# The simultaneous intrinsic test

Real-time detector and ordered Eu consumption. Eu discrepancy **and**
real discrepancy for exactly the same weights. Fixed normed spacelike and
all-projection separated inputs, same positive margin (existential, no
numerical lower bound). Use possible distinct regulation errors on widths;
pricing of election/width measurements handled separately.
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
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ

abbrev Quote := ℝ≥0→(G).Op

def leftBill (r:ℝ≥0) (A:(G).Op) (f:SampleDose) : (G).Op :=
   P.flounce 3 ξ (r/2) (-(2*(r:ℝ))) 0 (star A) f
def rightBill (r:ℝ≥0) (A:(G).Op) (f:SampleDose) : (G).Op :=
   P.flounce 3 ξ (r/2) 0 (2*(r:ℝ)) A f

/-- (Wall-wall; left). -/
lemma redEye (r:ℝ≥0) (A:(G).Op) (f:SampleDose) :
    star (leftBill P x r A f) ω₁ =
    DoseTravel.beam G f (fun p=>V p (T (0-p 3 - r/2).toNNReal (A ω₁))) := by
  rw [leftBill,P.star_flounce,star_star]
  simp_rw [pad_val,P.cart_empty,mul_apply_eq_comp,P.heaven_hot]; rfl

/-- Right. -/
lemma greenEye (r:ℝ≥0) (A:(G).Op) (f:SampleDose) :
    rightBill P x r A f ω₁ =
    DoseTravel.beam G f (fun p=>V p (T (p 3-0 - r/2).toNNReal (A ω₁))) := by
  rw [rightBill,P.flounce_act]
  simp_rw [cloaked,pad_val,mul_apply_eq_comp,P.cart_empty,P.heaven_hot]; rfl

lemma EuBeam {f:ℕ→SampleDose} {p:Vantage} (e:Condenses p f)
    (w : Vantage→ℝ) (h:Continuous w) (A:(G).Op) :
    Tendsto (fun i=> DoseTravel.beam G (f i)
       (fun y=>V y (T (w y).toNNReal (A ω₁)))) atTop (𝓝 (V p (T (w p).toNNReal (A ω₁)))) :=
   Condenses.reply e (P.caravan _ _ _ _ continuous_id (vet_heat 𝓢 h continuous_const))

lemma backcost (s t:ℝ≥0)(h:0<s)(l:s≤t)(A:Quote P x)(g:(𝓢).Covetails A) :
    T ((t:ℝ)-s).toNNReal (A s ω₁) = A t ω₁ := by
  have eq : A t = T (t-s) * A s * T (t-s) :=
    (congrArg A (add_tsub_cancel_of_le l).symm).trans (g s h (t-s))
  rw [eq,mul_apply_eq_comp,P.heaven_hot,mul_apply_eq_comp,← NNReal.coe_sub l,
        Real.toNNReal_coe]

lemma Eu_imag {r:ℝ≥0}(h:0<r) {p q:Vantage} (z:p 3 = -(r:ℝ))(b:q 3=r)
    (A B:Quote P x)(c:(𝓢).Covetails A)(d:(𝓢).Covetails B)
    {f u:ℕ→SampleDose}(e:Condenses p f)(a:Condenses q u) :
    Tendsto (fun i=> fault ω₁ (leftBill P x r (A (r/2)) (f i))
               (rightBill P x r (B (r/2)) (u i)))
       atTop (𝓝 (inner ℂ (stood P x (A r) p) (stood P x (B r) q))) := by
  have u1 := ((shred_cont ω₁).tendsto _).comp (EuBeam P x e
    (fun y=>0-y 3-r/2) (by fun_prop) (A (r/2)))
  have u2 := ((shred_cont ω₁).tendsto _).comp (EuBeam P x a
    (fun y=>y 3-0-r/2) (by fun_prop) (B (r/2)))
  simp_rw [Function.comp_def,← redEye,z,zero_sub,neg_neg,← (show ((r/2:ℝ≥0):ℝ)=r/2 by simp),
    backcost P x _ _ (half_pos h) (half_le_self h.le) A c] at u1
  simp_rw [Function.comp_def,← greenEye,b,sub_zero,← (show ((r/2:ℝ≥0):ℝ)=r/2 by simp),
    backcost P x _ _ (half_pos h) (half_le_self h.le) B d] at u2
  simp_rw [shines _ (home_norm P x)]
  exact u1.inner u2

lemma realBill (p:E4) (X:(G).Op) :
    (𝓢).dangle p X ω₁ = (𝓢).edge (p 3) (V (foldSpace p) (X ω₁)) := by
  rw [dangle,mul_apply_eq_comp,(home_basis P x).2,mul_apply_eq_comp,
      moon] -- tune
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

lemma realBeam {f:ℕ→SampleDose} {p:Vantage} (e:Condenses p f)
    (X:(G).Op) :
    Tendsto (fun i=>
       age 𝓢 (-(p 3)) (jut ω₁ ((𝓢).rasp X (sachet_LocalFieldBounds (f i)))))
       atTop (𝓝 (stood P x X p)) := by
  have he (F:SampleDose) : (𝓢).rasp X (sachet_LocalFieldBounds F) ω₁ =
      DoseTravel.beam G F (fun y=> (𝓢).dangle (foldSpace.symm y) X ω₁) := by
    show (∫ y:E4,(sachet_LocalFieldBounds F) y • ((𝓢).dangle y X ω₁))=_
    rw [integral_sachet]
    rfl
  have h := e.reply (((𝓢).dangle_cont X ω₁).comp foldSpace.symm.continuous)
  simp only [Function.comp_apply,Function.comp_def] at h
  simp_rw [YM.OS.Semigroup.Gingham.age,jut,he]

  have he1 := ((((𝓢).edge (-(p 3))).continuous.comp (shred_cont ω₁)).tendsto _).comp h
  rw [realBill] at he1
  have q (t:ℝ) (v:G) : (𝓢).edge t (shred ω₁ v)=shred ω₁ ((𝓢).edge t v) := by
    have ht : (𝓢).unit.translation (t • basis 3)=(𝓢).edge t := by
      have ht : SEP 3 (t • basis 3)=0 := Subtype.ext (show (t:ℝ) • basis 3 - _=_ by simp)
      simp [YM.OS.Semigroup.unit,ht,(𝓢).uZero]
    rw [← ht]
    exact U_shred 𝓢 _ (home_basis P x).2 _ _
  dsimp only [Function.comp_apply] at he1
  rw [q _ ((𝓢).edge _ _),foldSpace.apply_symm_apply,
      ←ContinuousLinearMap.comp_apply,(𝓢).send,
      show (foldSpace.symm p) 3=p 3 from rfl, neg_add_cancel,(𝓢).birth,
      ContinuousLinearMap.id_apply] at he1
  exact he1


/-- Read a single `Weave` in four ways. 
* coupled Eu at padded Eu prices (supports ordered)
* forecast Eu at same prices
* coupled real via pocket operators
* forecast real
Not changing smear under continuation, no implication of equality by Wick
rotation *at the same test* between Eu and Mink results. There's a Weyl
price relation (coming out of same operators), e.g. in traces_real.
Inputs L already formed in earlier region, including necessary turnover
of that ingredient, L=(star A). -/
def EuLeft (a:Weave) (L:Quote P x) : (G).Op :=
   P.flounce 3 ξ a.wound a.l 0 (L a.wound) a.blot
def EuRight (a:Weave) (M:Quote P x) : (G).Op :=
   P.flounce 3 ξ a.wound 0 a.r (M a.wound) a.well
def RealLeft (a:Weave) (L:(𝓢).Detector) :=
   L (sachet_LocalFieldBounds a.blot)
def RealRight (a:Weave) (M:(𝓢).Detector) :=
   M (sachet_LocalFieldBounds a.well)
def Caught (a:Weave) (L M:Quote P x)
    (g m : (𝓢).Detector) : Prop :=
    fault ω₁ (EuLeft P x a L) (EuRight P x a M) ≠ 0 ∧
    rfault 𝓢 Ω (RealLeft P x a g) (RealRight P x a m) ≠ 0

/-- Explicit prescription constraint. -/
def Scrive (a:Weave) : Prop :=
    ∃ (i:ℕ) (p q:Vantage) (s:ℝ), |s| < (1/2:ℝ)^i ∧
        a.blot=nib p i ∧ a.well=trim (nib q i) (foldSpace (s • basis 3))


lemma convergeJog (s:ℕ→ℝ)
    (hs: ∀ᶠ i:ℕ in atTop, |s i| < (1/2:ℝ)^i) :
    Tendsto (fun i=>foldSpace (s i • basis 3)) atTop (𝓝 0) := by
  have t:= tendsto_pow_atTop_nhds_zero_of_lt_one
    (r:=(1/2:ℝ)) (by norm_num) (by norm_num)
  have he : Tendsto s atTop (𝓝 0):= tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simp only [sub_zero,Real.norm_eq_abs]
    exact squeeze_zero' (Eventually.of_forall fun _=>abs_nonneg _)
       (hs.mono fun i h=>h.le) t)
  have en := tendsto_const_nhds (f:=(atTop:Filter ℕ)) (x:=basis (3:Axis)) -- tune
  simpa only [Function.comp_def,zero_smul,map_zero] using (foldSpace.continuous.tendsto _).comp (he.smul en)

/-- Simultaneous test. Generic speakers on `seasons`; the width acquisitions
to enforce for those speakers are additional and not presumed here. -/
theorem simultaneous {A B L:Quote P x}
    (w : (𝓢).Covetails A) (c : (𝓢).Covetails B)
    {s t : ℝ≥0} (a:0<s) (b:0<t)
    (y:OS.Cross 3)
    (u: inner ℂ (jut ω₁ (A s)) ((𝓢).U y (jut ω₁ (B t))) ≠ 0)
    {f ℓ g:(𝓢).Detector}
    (F : (𝓢).Instates A f) (J : (𝓢).Instates L ℓ)
    (hs:∀ d:ℝ≥0, 0<d → star (A d)=L d)
    (M : (𝓢).Instates B g) :
    ∃ i:Weave, Scrive i ∧ Caught P x i L B ℓ g := by
  obtain ⟨h,p,q,z,pp,qq,span,spac,e⟩ := dart P x w c a b y u
  let X := nib p
  let Y := nib q
  let px := nib_to p
  let qy := nib_to q
  have rx (u:Vantage) (v) (m:ℕ→SampleDose)(k:Condenses u m) :
    Tendsto (fun i=>age 𝓢 (-(u 3))
         (jut ω₁ ((𝓢).rasp v (sachet_LocalFieldBounds (m i)))))
       atTop (𝓝 (stood P x v u)) := realBeam P x k v

  have active := ((rx p (A h) X px).inner (rx q (B h) Y qy)).eventually_ne e
  let Yu (i:ℕ) (t:ℝ) := trim (Y i) (foldSpace (t • basis 3))
  let fires (i:ℕ) (t:ℝ) :=
    |t| < (1/2:ℝ)^i ∧
    rfault 𝓢 Ω (ℓ (sachet_LocalFieldBounds (X i))) (g (sachet_LocalFieldBounds (Yu i t))) ≠ 0
  have moves : ∀ᶠ i in atTop, ∃ t, fires i t := by
    filter_upwards [active] with i ep
    have mt := F.mirror J ((eventually_mem_nhdsWithin).mono fun d ht=>hs d ht)
       (sachet_LocalFieldBounds (X i))
    rw [sachet_bar] at mt
    simpa only [fires,Yu,trim_ahead] using
       traces_real 𝓢 Ω (home_basis P x) (home_norm P x)
         F M (sachet_LocalFieldBounds (X i)) (sachet_LocalFieldBounds (Y i)) mt z z
         (-(p 3)) (-(q 3)) ep ((1/2:ℝ)^i) (pow_pos (by norm_num) _)
  let jog (i:ℕ) : ℝ := if k:∃ t, fires i t then k.choose else 0
  have hp : ∀ᶠ i in atTop, fires i (jog i) := moves.mono fun i k=>by
    unfold jog; rw[dif_pos k]; exact k.choose_spec

  let U (i:ℕ) := Yu i (jog i)
  have k : Condenses q U :=
    condenses_after qy (convergeJog jog (hp.mono fun i h=>h.1))
  have eu := (Eu_imag P x z pp qq A B w c px k).eventually_ne e
  have pv : ∀ᶠ _a:ℕ in atTop, ∃ i:Weave, Scrive i ∧ Caught P x i L B ℓ g := by
    filter_upwards [weaves_late h p q z px k pp qq span spac,eu,hp] with n he f y
    obtain ⟨i,bl,wl,wo,l,r⟩ := he
    refine ⟨i,⟨n,p,q,_,y.1,bl,wl⟩,?_,?_⟩
    · unfold EuLeft EuRight
      rw [bl, wl,wo,l,r, ← hs _ (half_pos z)]
      push_cast -- coe part
      exact f
    · rw [RealLeft,RealRight,bl,wl]
      exact y.2
  obtain ⟨i,z⟩ := pv.exists; exact z
end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
