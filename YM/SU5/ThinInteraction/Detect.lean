import YM.SU5.ThinInteraction.Margin
/-!
# A lower bound on the diagonal discrepancy of the reflected thin field tests with this budget

TeX also gives distribution limit, rank etc.; this file only ports key pieces of the positive
construction, reaching this UNIFORM discrepancy (refine t first and use it all along the
sequence of width choices -- doesn't yet implement the ν-limit System). Explicit exponent cost.
Also keeps freedom for the common, subsequently frozen width-index tuning allowing all the further
Tendsto in the claim of TeX. Don't infer that `width_floor` proves that latter Tendsto.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 220000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open YM.SatinThin
namespace Thinning
open Set Aria Six Casting
open scoped BigOperators
variable (P:Spine) (x:P.Spectrum0 3) (s n t:ℕ) (Z:Lead.Clan)
local notation "S" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "W" => ShopP P s n
local notation "T" => timeMesh P.par
local notation "d" r:max => offset false r
local notation "τ" => P.probeWidth s n 3
local notation "M" => P.singleState 3 t x
local notation "A" => P.FTest Z s n
local notation "Y" => P.RTest Z s n

namespace Portfolio
open MeasureTheory Spectral Six Set
local notation "H" => P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "E" => (S).E
local notation "v₀" => alk s n x Z false
local notation "U" => P.cartage 3 ξ
variable {P x s n Z}{a:ℝ}(p:Portfolio x s n a Z)
lemma bill_exp (i:Vantage) (v:i 3 ≤ 2) : ‖pp p i‖≤ Real.exp ((p.m:ℝ) * 2):= by
  unfold pp; rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp only [Complex.sub_re,Complex.mul_re, Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,Complex.I_im,zero_mul,sub_self,sub_zero]; exact mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _)
private lemma norm_at {X:Hilbert}(S₀:OS.Semigroup X (3:Axis))(t:ℝ≥0)(v:X): ‖S₀.E t v‖≤‖v‖:= ((S₀.E t).le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) (S₀.shrinks _))
private lemma norm_bill (i:Vantage) (v:i 3 ≤ 2) (x':H): ‖aspect p i x'‖≤ Real.exp ((p.m:ℝ)*2)*‖x'‖ := by
  let w:= E (transit P s n i) x'; let z := pp p i
  exact le_trans (le_of_eq ((norm_smul z (U i w)).trans (congrArg (‖z‖ * ·) (P.cart_norm 3 ξ i w)))) (mul_le_mul (p.bill_exp i v) (norm_at (S) (transit P s n i) x') (norm_nonneg _) (Real.exp_pos _).le)

private lemma by_norm (X:Hilbert)(F:SampleDose)(u:F.Normalized)(f g:Vantage→X)(p:Continuous f)(w:Continuous g) {δ:ℝ}
    (e:∀ i∈tsupport F.val, ‖f i-g i‖≤δ) : ‖(∫ i,(F.val i:ℂ) • f i)-(∫ i,(F.val i:ℂ) • g i)‖≤δ:= by
  let k (i:Vantage) := (F.val i:ℂ) • f i - (F.val i:ℂ) • g i
  have hi : Integrable k := (weightedMoney F X f p).sub (weightedMoney F X g w)
  have ht:∀ i,‖k i‖≤ F.val i * δ:= by
    intro i; by_cases v:i∈ tsupport F.val
    · unfold k; rw [← smul_sub,norm_smul,Complex.norm_of_nonneg (u.1 i)] -- tune
      exact mul_le_mul_of_nonneg_left (e i v) (u.1 i)
    unfold k; rw [image_eq_zero_of_notMem_tsupport v]; simp
  rw [←integral_sub (weightedMoney F X f p) (weightedMoney F X g w)]
  exact (norm_integral_le_integral_norm k).trans ((integral_mono hi.norm ((F.smooth.continuous.integrable_of_hasCompactSupport F.budget).mul_const _) ht).trans_eq (by rw [integral_mul_const, u.2,one_mul]))
lemma close_column (F:SampleDose) (h:LittleLayout F) (u:F.Normalized) (y z:H): ‖column p F y-column p F z‖≤Real.exp ((p.m:ℝ)*2)*‖y-z‖:= by
  refine by_norm H F u (fun i=> aspect p i y) (fun i=> aspect p i z) (aspect_cont p y) (aspect_cont p z) (fun i v =>?_)
  have he : aspect p i y-aspect p i z= aspect p i (y-z):= by
    let X:(H).Op:= pp p i • ((U i) * E (transit P s n i)); exact (map_sub X _ _).symm
  exact (congrArg (fun x:H=>‖x‖) he).trans_le (p.norm_bill i (h v).1 _)

abbrev tol (p:Portfolio x s n a Z) := ((Real.exp (-4))/4)/Real.exp ((p.m:ℝ)*2)
lemma tol_pos : 0< p.tol:= by positivity -- unfold
private lemma invest_core (X: Hilbert)(w:ℝ)(B:ℝ)(hw:0<w)(b:0<B)(x y:X)
    {δ: ℝ} (e:‖x-y‖≤w*δ) (t:δ≤(B/4)/w)(u:B/2 ≤ ‖x‖): (B/4)^2 ≤ (inner ℂ y y).re:=by
  rw [← show RCLike.re (K:=ℂ) (inner ℂ y y)= (inner ℂ y y).re from rfl, inner_self_eq_norm_sq]
  have he: δ*w ≤ B/4:= (le_div_iff₀ hw).mp t; have ht:= norm_add_le (x-y) y; rw [sub_add_cancel] at ht; apply pow_le_pow_left₀ (by positivity); nlinarith

lemma width_floor (F:SampleDose)(c:ShopP P s n→₀ℝ)(e:roofed P s n F)(h:LittleLayout F)(z:F.Normalized)
    (v: ‖p.intended-focusing S false c v₀‖ ≤ p.tol): (Real.exp (-4)/4)^2 ≤ (inner ℂ
       (column p F (focusing S false c v₀)) (column p F (focusing S false c v₀))).re:=
  invest_core H (Real.exp ((p.m:ℝ)*2)) (Real.exp (-4)) (Real.exp_pos _) (Real.exp_pos _) _
    (column p F (focusing S false c v₀)) (p.close_column F h z p.intended (focusing S false c v₀)) v (p.ideal_floor F e h z)
lemma deployed (F:SampleDose)(c:ShopP P s n→₀ℝ)(e:roofed P s n F)(h:LittleLayout F)(z:F.Normalized)
    (v: ‖p.intended-focusing S false c v₀‖ ≤ p.tol) (J:P.Ellis 3 x) :
    ∀ᶠ t:ℕ in atTop, covered t c ∧ ((Real.exp (-4)/4)^2)/2 ≤
      (P.singleState 3 t x (P.reflectTest 3 (deploy t F p c)*deploy t F p c)).re:= by
  have ht:0<(Real.exp (-4)/4)^2:= by positivity
  have hb:= p.width_floor F c e h z v
  exact (coverable c).and ((Complex.continuous_re.continuousAt.tendsto.comp (pair_column p F c J e p F c e)).eventually (le_mem_nhds ((half_lt_self ht).trans_le hb))) -- tune
end Portfolio
open Portfolio
section
variable {P x}
-- Co-finance the reflected tests in each such measurement. Keep also conjugate-price tolerance.
structure Ported {a:ℝ} (p:Portfolio x s n a Z) (f:SampleDose) (c:ShopP P s n →₀ ℝ) (δ:ℝ) : Prop where
  tolerance : ‖p.intended-focusing S false c (alk s n x Z false)‖<δ ∧
                ‖focusing S true c (alk s n x Z true)‖<δ
  physical :
    ∀ᶠ t:ℕ in atTop, covered t c ∧ ((Real.exp (-4)/4)^2)/2 ≤
      (P.singleState 3 t x (P.reflectTest 3 (deploy t f p c)*deploy t f p c)).re
  against (t:ℕ) (p':covered t c) (X : P.Test→ₗ[ℂ]ℂ) (h:Factors P.calibration X)
    (m: MatterWard P.calibration X ∨ GaugeWard P.calibration X):
      X (P.reflectTest 3 (deploy t f p c)*deploy t f p c)=0

#check @Ported
lemma ports {a : ℝ} (p:Portfolio x s n a Z) (e:P.calibration.ℓ<n) (δ:ℝ)(h:0<δ)(u:δ≤p.tol)
    (J:P.Ellis 3 x) : ∃ c:ShopP P s n→₀ℝ,
    ∀ f:SampleDose, f.Normalized→LittleLayout f → roofed P s n f→ Ported s n Z p f c δ:= by
  let R:=p.appointment δ h; let c:=R.choose
  exact ⟨c,fun f p' q t=> ⟨⟨R.choose_spec.1,R.choose_spec.2⟩,p.deployed f c t q p' (R.choose_spec.1.le.trans u) J,
    fun i b x H' m=> split_deploy i f p c t e b f p c t b x H' m⟩⟩

-- One way to interface with TeX, using the **same** macroscopicSatin witnesses.
-- NOT default lake target. Build instructions in the construction notes.
lemma cofinance (K:P.Register) (r l:ℕ→ℕ) (J:P.Ellis 3 x) (B:Experiment P K r l x J)
    (U:P.Transmission x r l) (a:Lead.Clan→ℝ)(p:∀ x, 0<a x) : ∀ᶠ i:ℕ in atTop,
    ∀ Z, ∃ t:Portfolio x (r i) (l i) (a Z) Z,
      ∀ δ > 0, δ ≤ t.tol → ∃ c: ShopP P (r i) (l i)→₀ℝ,
        ∀ (f:SampleDose), f.Normalized→LittleLayout f → roofed P (r i) (l i) f→ Ported (r i) (l i) Z t f c δ := by
  apply eventually_all.mpr; intro z
  -- use uniform
  filter_upwards [Thinning.availability (x:=x) (a z) B.launch U (p z), B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i q h
  let t:= Classical.choice (q z); exact ⟨t,fun δ e v=> ports (r i) (l i) z t h δ e v J⟩

-- qualifications using external *fixed* tests with time argument > 1 as in TeX
lemma uses_fixed (r l:ℕ→ℕ) (U:P.Transmission x r l): ∀ᶠ i:ℕ in atTop, ∀ f:SampleDose,
    (∀ x'∈ tsupport f.val,(1:ℝ)< x' (3:Axis)) → roofed P (r i) (l i) f := by
  filter_upwards [(U.widths 3).eventually (gt_mem_nhds (show 0 < (1/2:ℝ) by norm_num))] with i x
  intro f v y hy
  exact lt_trans (by linarith only [x]) (v y hy)
end
#print axioms uses_fixed
#print axioms Portfolio.deployed
#print axioms cofinance
end Thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
