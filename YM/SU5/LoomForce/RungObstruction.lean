import YM.SU5.LoomForce.Placement
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
open Vale (hat)

/-!
Geometry in native Tapestry.Keeps conventions. (Fixed ratio 2 to the physical
meters of EB.1 -- a unit L0 *matter* step in EB.1.) `shield` includes the
whole reserve, not just bounds on plaquette extents. Two price results:

* All Staff purchases using `duo` under this one fixed I bill, with land
  granted even just **frequently** on the inner chosen path and eventually on
  rung, necessarily bring their node separation in *physical units* to zero.
* In their zoom appointments, however, get strict Plenum-footprint separation
  in rescaled boxes (with even a one-spatial-axis dominated time-gap option,
  see CP1), even on the coherent horizon.

Further estimates resolving to fixed-smear limits for a *continuum field*
shouldn't ask for this tenancy on such a pair at *all new* t with clock spacing
shrinking like this, even to attempt a Wake on that reading. They'll need e.g.
comparison of operators at different scales -- use these bills instead first
at a *fixed* late rung of probe calibration, as in the Pure Force plan.
-/
open CF.Pannier.Chancel Pressure Worth Worth.Pays BProof
open Heat

variable {I A : ℝ} {W V : ℕ → Staff}
local notation "Φpr" => precisionAt P.par

def rungSpace (P : Spine) (I : ℝ) (s : ℕ) := sPow P.par s I / precisionAt P.par s

lemma rungSpace_pos (I : ℝ) (s : ℕ) : 0 < rungSpace P I s := div_pos (coin_pos ..) (positiveScale ..)
lemma rungSpace_resolution (I : ℝ) : Tendsto (rungSpace P I) atTop (𝓝 0) := by
  -- use linear hat price, hence sPow affordable under any level-exponential
  let L := Λ; let X := hat L.R.L L.x; let ℓ : ℝ := L.R.L.val
  have ht: 1 < ℓ := by unfold ℓ; exact_mod_cast (show 1 < L.R.L.val by have he:= L.V.tallX; omega)
  have hx : Tendsto (fun i : ℕ => ((X i) / ℓ^i)) atTop (𝓝 0) := by
    have h0:Tendsto (fun i:ℕ=> L.x/ ℓ^i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt ht)
    have h₀:= h0.add ((tendsto_pow_const_div_const_pow_of_one_lt 1 ht).mul_const (Vale.billX L.R.L))
    simp only [pow_one,zero_mul,add_zero] at h₀; exact h₀.congr (fun i=> by unfold X hat; ring)
  refine squeeze_zero' (Eventually.of_forall (fun i => (rungSpace_pos P I i).le)) ?_ hx
  filter_upwards [(turnover Λ).eventually (Pays.leap (w:=1) (p:=0) (q:=0) (whole 0 I 0)
    (Or.inl zero_lt_one)),(turnover Λ).eventually_gt_atTop 0] with s h p
  unfold rungSpace; change sPow L s I/Φpr s ≤ X s / Φpr s
  exact div_le_div_of_nonneg_right (h.trans_eq (coinY p)) (positiveScale L s).le

omit P in
lemma tenant_foot (X : Staff) (N : Side) (b d e w : ℕ) (o : Seat N) (p : X.Pays b w)
    (q : X.tenancy N b d e o) : separation o (wrap (More N) X.xo) ≤ e := by
  apply blocks_test.mp (q ?_)
  unfold Staff.gateS; rw [←wrap_pav]; exact mem_image_of_mem _ (pav_mono (show b≤b+d+8 by omega) (p.node X))

def nearbyPair (P : Spine) (s n : ℕ) (W V : Staff) (I : ℝ) : Prop :=
    ∃ (e b w : ℕ) (o : Seat (matterSide P s n)),
      (e : ℝ) ≤ sPow P.par s I ∧
        W.Pays b w ∧ V.Pays b w ∧
        W.tenancy (matterSide P s n) b Staff.clearance e o ∧ V.tenancy (matterSide P s n) b Staff.clearance e o

lemma cannot_reach (p : ∀ᶠ s in atTop, ∃ᶠ n in atTop, nearbyPair P s n (W s) (V s) I) :
    Tendsto (fun s => dist (addressG P.par s (W s).xo) (addressG P.par s (V s).xo)) atTop (𝓝 0) := by
  have hx := (rungSpace_resolution P I).const_mul 2
  rw [mul_zero] at hx
  refine squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_ hx
  filter_upwards [p] with s v
  let a := (W s).xo; let b := (V s).xo; let S':Finset Cover := {a,b}
  obtain ⟨n,⟨e,t,w,o,l,X,Y,F,D⟩,q⟩ := (v.and_eventually (FixedProbe.geometry_money Γ P.large P.law s P.projection S')).exists
  let N := matterSide P s n; let U := wrap (More N) a; let Z := wrap (More N) b
  have h := q a (by simp [S']) b (by simp [S']); rw [← show _ = dist (addressG P.par s (W s).xo) (addressG P.par s (V s).xo) from h]
  have hF : separation o U ≤ e := tenant_foot (W s) N t _ e w o X F
  have hG : separation o Z ≤ e := tenant_foot (V s) N t _ e w o Y D
  have he : ((separation U Z:ℕ):ℝ) ≤ (↑e:ℝ)+↑e := by exact_mod_cast ((separation_triangle U o Z).trans (add_le_add ((separation_comm ..).le.trans hF) hG))
  let k := sPow P.par s I; change (separation U Z:ℝ)/Φpr s ≤ 2*(k/Φpr s)
  rw [←mul_div_assoc]; exact div_le_div_of_nonneg_right (he.trans (by change _≤ 2*k; linarith only [(show (e:ℝ) ≤ k from l)])) (positiveScale ..|>.le)

/-! rescaled point bounds in these very units; buy eventual enclosure
of the WHOLE reserve of every point of the adjacent-staff official support. -/
def rescaledFit (P : Spine) (s : ℕ) (A : ℝ) (x : Gaia) (r : ℝ) : Set RSpace :=
  {y|∀ j, |y j - rungSpace P A s*x j| < rungSpace P A s * r}

variable (hA : 0 < A) {u : ℕ → Cover} {x : Gaia}
include hA
lemma fitsPrinted {R : ℝ} (hR : 0 < R) (h : Appoint P.par A u x)
    (l d : ℕ) :
    ∀ᶠ s : ℕ in atTop, printedHere P.par l s (skyDeck (nodeC (u s)) d) (rescaledFit P s A x R) := by
  let S (s:ℕ) := sPow P.par s A; let u' (s:ℕ) := nodeC (u s); let t := R/2; let k := Journey.reserve P.par l
  have ht:0<t:=half_pos hR
  let y (s : ℕ) := riseX (S s) (u' s)
  have hx : Tendsto y atTop (𝓝 x) := h
  filter_upwards [Metric.tendsto_nhds.mp hx t ht,(sPower_pay P.par hA).eventually_gt_atTop (((k:ℝ)+d)/t)] with s q l'
  rw [dist_eq_norm] at q
  intro u₀ b y₀ m j
  have hp := lt_of_le_of_lt (PiLp.norm_apply_le (p:=2) (y s-x) j) q
  let g := (S s)
  have hg:0<g:=BProof.coin_pos ..
  change ‖(u' s j:ℝ)/g - x j‖ < t at hp
  rw [Real.norm_eq_abs, div_sub' hg.ne',abs_div,abs_of_pos hg, div_lt_iff₀ hg] at hp
  have hZ := (pav_v ..).1 b j
  have hz : -(d:ℝ) ≤ (↑(u₀ j):ℝ)-↑(u' s j) ∧ (↑(u₀ j):ℝ)-↑(u' s j) ≤ d := by
    have he: -(↑d:ℤ) ≤ u₀ j - u' s j ∧ u₀ j - u' s j ≤ d := by unfold u'; omega
    exact_mod_cast he
  have hf : |(Φpr s)*y₀ j-(u₀ j:ℝ)| ≤ k:= m j
  change |_ - g / Φpr s * _| < g / Φpr s * R
  rw [abs_lt] at hp ⊢; rw [abs_le] at hf; have he:(k:ℝ)+d<g*t:=(div_lt_iff₀ ht).mp l'
  have hP := positiveScale P.par s
  obtain ⟨p₁,p₂⟩ := hp; obtain ⟨p₃,p₄⟩ := hf; obtain ⟨p₅,p₆⟩ := hz; unfold t at *
  constructor <;> (field_simp; linarith)
#print axioms cannot_reach
#print axioms fitsPrinted
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
