import YM.SU5.MacroSix.Lane
import YM.SU5.MacroSix.Zoom
/-!
# Purchasing a full seed in every sign lane

Use the *matrix heat-character estimate* from the proof of `l:zoommat`, not a
subsequence rank hypothesis at reflection and not a scalar nonzero-price theorem.
True Euclidean heat time and translations and on the same Spine. As in `t:trans6`,
we also (inside both projected vectors) have the `1-E t'` factor. Here we can even
compute the nonzero limiting values after that factor directly from the explicit
analytic form `ovoid` in the matrix estimate.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2400
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial Twah Designs Prototype Lamour.Bridge.Celeste
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria Set
open _root_.YM.MacroSix (Success)

namespace Spine
section value

private lemma straight_zero (t : ℝ) (h : 0 < t) :
    plume t 0= (((1:ℝ) / (Real.pi^2*t^3)):ℂ) := by
  unfold Cordial.plume pearly
  rw [show ((0:Bank).val (2:Axis):ℝ)=0 from rfl, Complex.ofReal_zero,zero_mul,add_zero,
    Complex.real_smul,norm_zero]
  -- identity in ℂ, denominator nonzero in this evaluation
  have he : t≠0:=h.ne'
  push_cast; field_simp [Real.pi_pos.ne']
  <;> ring

private def strength (Z : Lead.Clan) : ℂ := ovoid Z 10 0 - ovoid Z (10+1/2) 0 -
    (ovoid Z (10+1/2) 0 - ovoid Z (10+1/2+1/2) 0)

private lemma strength_nonzero (Z : Lead.Clan) : strength Z ≠ 0 := by
  -- simplify all P20 terms first, then factor pi out
  have he : numberX Z ≠ 0 := by
    have h : 0<dimf Z := by unfold Window.dimf; split <;> decide
    unfold numberX; exact_mod_cast (show dimf Z ≠ 0 from h.ne')
  intro h
  simp (disch := norm_num) only [strength,ovoid, straight_zero] at h
  push_cast at h
  field_simp [Real.pi_pos.ne'] at h
  ring_nf at h
  simp_all

end value
section heat
variable {G : Hilbert} (S : OS.Semigroup G (3:Axis)) (y : Bank) (t a : ℝ≥0)

private lemma warm_commute (x : G) : S.E t (S.U y x)= S.U y (S.E t x) :=
  DFunLike.congr_fun (S.independent ..) _
private lemma damp_pair (x z : G) :
    let K (t : ℝ≥0) := inner ℂ x (S.U y (S.E t z))
    inner ℂ (x-S.E a x) (S.U y (S.E t (z-S.E a z))) = K t-K (t+a) - (K (t+a)-K (t+a+a)) := by
  intro K
  have he (b : ℝ≥0) : inner ℂ (S.E a x) (S.U y (S.E b z)) = K (b+a) := by
    rw [S.swing,warm_commute,← ContinuousLinearMap.comp_apply (S.E a),← S.time,add_comm a b]
  rw [map_sub, map_sub, ← ContinuousLinearMap.comp_apply (S.E t), ← S.time]
  simp only [inner_sub_left, inner_sub_right,he]; rfl

private lemma fourPrices (Y : ℕ → Bank) (T A : ℕ → ℝ≥0) (X W : ℕ → G) (p q r : ℂ)
    (h : Tendsto (fun i ↦ inner ℂ (X i) (S.U (Y i) (S.E (T i) (W i)))) atTop (𝓝 p))
    (e : Tendsto (fun i ↦ inner ℂ (X i) (S.U (Y i) (S.E (T i+A i) (W i)))) atTop (𝓝 q))
    (u : Tendsto (fun i ↦ inner ℂ (X i) (S.U (Y i) (S.E (T i+A i+A i) (W i)))) atTop (𝓝 r)) :
    Tendsto (fun i ↦ inner ℂ (X i-S.E (A i) (X i))
      (S.U (Y i) (S.E (T i) (W i-S.E (A i) (W i))))) atTop (𝓝 (p-q-(q-r))) := by
  exact ((h.sub e).sub (e.sub u)).congr fun i ↦ (damp_pair S _ _ _ _ _).symm
end heat

variable (P : Spine) (signs : Axis → Bool) (s n : ℕ) (x : P.Spectrum0 3)
    (j k : Window.Family)
local notation "widthLead" s:max n:max j:max => ((P.sixWidth s n j):ℝ)
local notation "β" => P.otherSpectrum 3 3 x
local notation "H" => P.ManyF 3 β
local notation "ν" => P.seasons 3 β
local notation "u" t:max => Real.toNNReal t

def smallLead : Vantage := fun i ↦ if i = 3 then 10 * P.dew s n
  else (if signs i then (1:ℝ) else -1) * (3*widthLead s n i)

lemma smallLead_ready (t : signs 3=true) (h : 2*widthLead s n 3<10*P.dew s n) :
    P.smallLead signs s n∈P.inLane s n signs := by
  let v := P.smallLead signs s n; intro i
  change _ ∈ P.laneSign s n i (signs i)

  by_cases p:i=3
  · subst i; rw [smallLead,if_pos rfl,t]; exact h
  have hp : 0 < widthLead s n i := P.sixWidth_pos s n i
  unfold smallLead; rw [if_neg p]; cases he : signs i
  · change -1*(3*_ ) < -(2*(widthLead s n i)); linarith
  change 2*widthLead s n i < 1*(3*_); linarith

variable {P x} {C r : ℕ → ℕ} (A : Launch P C r)
local notation "Δ" i:max => P.smallLead signs (C i) (r i)
local notation "w'" i:max j:max => widthLead (C i) (r i) j
local notation "ρ" i:max => P.dew (C i) (r i)
local notation "B" i:max => P.travelTime (C i) (r i)
local notation "K" i:max => P.fieldKernel (C i) (r i) x

def touched (P : Spine) (y : Vantage) : Bank := transverse 3 (fun j ↦ y j.val)

include A
lemma smallLead_late (h : signs 3=true) : ∀ᶠ i in atTop, Δ i∈ P.inLane (C i) (r i) signs := by
  filter_upwards [(timeWidthRatio A).eventually (gt_mem_nhds (show (5/2:ℝ)< 10/2 by norm_num))]
    with i t
  have he := (div_lt_iff₀ (P.dew_pos (C i) (A.unitSize i))).mp t
  exact P.smallLead_ready signs _ _ h (by linarith)

lemma smallLead_zooms : Tendsto (fun i ↦ (ρ i)⁻¹ • P.touched (Δ i)) atTop (𝓝 0) := by
  -- common transverse widths: a scalar multiple of a single transverse vector
  let F (k : Street) := (if signs k.val then (1:ℝ) else -1)*3
  let f := transverse 3 F
  let w (i : ℕ) := w' i 0
  have he (i) (k : Street) : (Δ i) k.val= w i * F k := by
    unfold smallLead; rw [if_neg k.property]; unfold w F sixWidth sixBudget
    rw [if_neg k.property,if_neg (show (0:Axis)≠3 from by decide)]
    ring
  have hz (i : ℕ) : P.touched (Δ i)=w i • f := by
    refine (eyes_toFace (3:Axis) _).trans ?_
    apply Eq.trans _ (eyes_toFace (3:Axis) (w i • f)).symm
    apply congrArg (transverse (3:Axis)); funext k
    change (P.touched _).val k.val=w i*f.val k.val; rw [touched,transverse_eyes,he i k,show f.val k.val=F k from transverse_eyes ..]
  have hp := (spaceWidthRatio A (0:Axis) (by decide)).smul_const f
  rw [zero_smul ℝ] at hp
  refine hp.congr fun i ↦ ?_
  rw [hz, smul_smul,mul_comm (_⁻¹ : ℝ),div_eq_mul_inv]

lemma twiceDimensions (T U : ℕ → ℝ≥0) {p q : ℝ} (h : P.dimensionS C r T p)
    (e : P.dimensionS C r U q) : P.dimensionS C r (fun i ↦ T i+U i) (p+q) :=
  (h.add e).congr fun i ↦ (show ((T i+U i:ℝ≥0):ℝ)/ρ i= _ from by push_cast; rw [add_div]).symm

local notation "E" i:max => P.birthCloud x j (C i) (r i)
local notation "E'" i:max => P.birthCloud x k (C i) (r i)
local notation "b" i:max => P.darkField (C i) (r i) j x
local notation "b'" i:max => P.darkField (C i) (r i) k x

variable {d : ℕ → ℝ} (Y : Prototype.readyUV P C r x d) (p : Tendsto d atTop (𝓝 0))
  (q : P.lodestarHere 3 (P.otherSpectrum 3 3 x))
include Y p q
private lemma seed_beam : Tendsto (fun i ↦ inner ℂ (b i)
    ((ν).U (P.touched (Δ i)) ((ν).E (u ((Δ i) 3)) (b' i)))) atTop
      (𝓝 ((Matrix.diagonal strength) j k)) := by
  let T (i : ℕ) := u ((Δ i) 3)
  let y (i : ℕ) := P.touched (Δ i)
  let g (t : ℝ) : ℂ := if j=k then ovoid j t 0-(purePrice j:ℂ)^2 else 0
  have ht : P.dimensionS C r T 10 := tendsto_const_nhds.congr fun i ↦ by
    unfold T smallLead; rw [if_pos rfl,Real.coe_toNNReal _ (mul_nonneg (by norm_num) (P.dew_pos _ (A.unitSize i)).le)]; exact (mul_div_cancel_right₀ (10:ℝ) (P.dew_pos _ (A.unitSize i)).ne').symm
  let W' (i : ℕ) := B i
  let V (t : ℕ → ℝ≥0) (v : ℝ) (e : 0 ≤ v) (h : P.dimensionS C r t v) :=
    centeredMatrixZoom j k A Y p q 0 v e t h y (smallLead_zooms signs A)
  let q₁ := scale_travel A
  let q₂ := twiceDimensions A T _ ht q₁
  have he (i : ℕ) : darkField P (C i) (r i) j x= E i - (ν).E (W' i) (E i) := rfl
  let f (i : ℕ) := inner ℂ (b i) ((ν).U (y i) ((ν).E (T i) (b' i)))
  have hb : Tendsto f atTop (𝓝 (g 10-g (10+1/2)-(g (10+1/2) - g (10+1/2+1/2)))) :=
    fourPrices ν y T W' _ _ _ _ _ (V T 10 (by norm_num) ht) (V _ _ (by norm_num) q₂)
      (V _ _ (by norm_num) (twiceDimensions A _ _ q₂ q₁))
  have hp : g 10-g (10+1/2)-(g (10+1/2) - g (10+1/2+1/2)) = (Matrix.diagonal strength) j k := by
    by_cases e : j=k
    · unfold g; rw [if_pos e,if_pos e,if_pos e]; simp only [← e, Matrix.diagonal_apply_eq]; unfold strength; ring
    simp [g,e]
  exact Eq.mp (congrArg (fun x ↦ Tendsto f atTop (𝓝 x)) hp) hb

variable (J : P.Ellis 3 x)
include J
private lemma seed_real (h : signs 3=true) :
    Tendsto (fun i ↦ (K i) 0 (Δ i) j k) atTop (𝓝 ((Matrix.diagonal strength) j k)) := by
  refine (seed_beam signs j k A Y p q).congr' ((smallLead_late signs A h).mono fun i t ↦ ?_)
  let y := Δ i; let f (z : Vantage) := P.cartage 3 β z
  have he : P.fieldOrder (C i) (r i) 3 0 y := P.sign_before (C i) (r i) 3 signs 0 y
    (show y-0∈P.inLane (C i) (r i) signs from (by rwa [sub_zero])) h
  let a := u (y 3); let c := u (y 3-(0:Vantage) 3)
  have hca : c=a := by simp [c,a]
  let v := b i; let z := b' i
  have hc : (ν).E c (f y z)=(ν).U (P.touched y) ((ν).E a z) :=
    (congrArg (fun t : ℝ≥0 ↦ (ν).E t (f y z)) hca).trans ((P.warm_drive 3 β y a z).trans
      (DFunLike.congr_fun (P.uses_cart 3 β y) _))
  exact ((P.fieldKernel_eq _ _ j k x J 0 y he).trans (congrArg₂ (inner ℂ) (show f 0 v=v from
    DFunLike.congr_fun (P.cart_zero 3 β) _) hc)).symm

lemma laneSeed (h : signs 3=true) :
    ∀ᶠ i in atTop, (Δ i ∈ P.inLane (C i) (r i) signs ∧ Success ((K i) 0 (Δ i))) := by
  have ht : Success (Matrix.diagonal strength) := ⟨(by
    simp only [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ strength_nonzero i)),fun i ↦ by simpa using strength_nonzero i⟩
  exact (smallLead_late signs A h).and (MacroSix.eventually_success atTop (fun i ↦ (K i) 0 (Δ i))
    _ (fun j k ↦ seed_real signs j k A Y p q J h) ht)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.laneSeed
