import YM.SU5.Six.PointSpot
import YM.SU5.Six.Slices
set_option autoImplicit false
set_option maxHeartbeats 80000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine
open Aria YM.OS YM.Six Set

variable (P : Spine) (x : P.Spectrum0 3) (B D : P.Apron) (k : Axis) (p q : Vantage)
local notation "W" => P.cartage k (P.advocate 3 x k)
set_option quotPrecheck false
local notation "E" => (P.seasons k (P.advocate 3 x k)).E
/-- The analytic response-function representation along one ray. -/
def rayPair (r : Vantage) (d : ℝ) := inner ℂ (glareY x B k)
  (E d.toNNReal (W r (flashY x D k)))
lemma rayPair_analytic (r : Vantage) {d : ℝ} (h : 0 < d) :
    AnalyticAt ℝ (P.rayPair x B D k r) d := analyticAt_heat _ _ _ _ h
lemma rayPair_price (r : Vantage) (d : ℝ) (J : P.Ellis 3 x)
    (v : ∀ i : Axis,i≠k→(q-p) i = r i)
    (eqd : (q-p) k-(B.realWidth P k+D.realWidth P k) = d) (h : 0 < d) :
    P.bodyPair x B D p q = P.rayPair x B D k r d := by
  subst d
  refine (P.bodyPair_fwd x B D k p q J (sub_pos.mp h)).trans ?_
  let T := (E (Real.toNNReal ((q-p) k-(B.realWidth P k+D.realWidth P k))))
  exact congrArg (fun A : (P.ManyF k (P.advocate 3 x k)).Op => inner ℂ (glareY x B k)
    (T (A (flashY x D k)))) (of_slideP x k _ r v)

variable (s n : ℕ) (Z Z' : Window.Family)
local notation "β" => P.incB s n Z
local notation "γ" => P.incA Z' s n
local notation "d" => (2*P.costW s n k)

lemma riseAsPair (r : Vantage) (J : P.Ellis 3 x) (h : r∈P.starPair s n) :
    P.rise x s n r Z Z' = P.bodyPair x β γ 0 r := by
  simpa only [sub_zero] using
    (P.bodyPair_rise x 0 r s n Z Z' J (by rw [sub_zero]; exact h.1)).symm

lemma rise_ray_pos (r : Vantage) (t : ℝ) (J : P.Ellis 3 x)
    (h : update r k t∈P.starPair s n) (ht : d < t) :
    P.rise x s n (update r k t) Z Z' = P.rayPair x β γ k r (t-d) := by
  refine (P.riseAsPair x s n Z Z' _ J h).trans <|
    P.rayPair_price x β γ k 0 (update r k t) r (t-d) J ?_ ?_ (sub_pos.mpr ht)
  · rw [sub_zero]; intro i hi; exact update_of_ne hi ..
  rw [sub_zero,update_self,P.incA_width,P.incB_width,two_mul]

lemma rise_ray_neg (r : Vantage) (t : ℝ) (J : P.Ellis 3 x)
    (h : update r k t∈P.starPair s n) (ht : t < -d) :
    P.rise x s n (update r k t) Z Z' = P.rayPair x γ β k (-r) (-t-d) := by
  have hu := neg_lt_neg ht
  rw [neg_neg] at hu
  have he : ((0 - update r k t : Vantage) k) = -t := by simp
  have hf : (0 - update r k t) ∈ P.forwardPair γ β k := by
    change (γ).realWidth P k + (β).realWidth P k < (0 - update r k t : Vantage) k
    rw [P.incA_width,P.incB_width,he, ← two_mul]; exact hu
  refine (P.riseAsPair x s n Z Z' _ J h).trans <|
    (P.bodyPair_bwd x β γ k _ _ J hf).trans <|
      P.rayPair_price x γ β k (update r k t) 0 (-r) (-t-d) J ?_ ?_ (sub_pos.mpr hu)
  · intro i hi; rw [zero_sub,Pi.neg_apply, update_of_ne hi]; rfl
  rw [he,P.incA_width,P.incB_width,two_mul]

/-- Choose `σ` with `σ 3 = true`. -/
def bearing (σ : Axis → Bool) (i : Axis) :=
  if σ i = true then Set.Ioi (2*P.costW s n i) else Set.Iio (-(2*P.costW s n i))
local notation "I" => P.bearing s n
variable (σ : Axis → Bool)
lemma bearing_open (i : Axis) : IsOpen (I σ i) := by
  unfold bearing; split; exact isOpen_Ioi; exact isOpen_Iio
lemma bearing_path (i : Axis) : IsPreconnected (I σ i) := by
  unfold bearing; split; exact isPreconnected_Ioi; exact isPreconnected_Iio
lemma bearing_clear (hσ : σ 3 = true) : shelf (I σ) ⊆ P.starPair s n := by
  intro r h
  refine ⟨?_, ?_⟩
  · simpa [bearing,hσ] using h 3
  intro i; specialize h i
  rw [bearing] at h
  rw [lt_abs]
  split at h; · exact Or.inl h
  exact Or.inr (lt_neg.mp h)
lemma star_bearing (r : Vantage) (h : r∈P.starPair s n) :
    ∃ σ, σ 3 = true ∧ r ∈ shelf (I σ) := by
  let τ := fun i => decide (2*P.costW s n i < r i)
  refine ⟨τ,decide_eq_true h.1, ?_⟩
  intro i
  unfold bearing; split
  · next hv => exact of_decide_eq_true hv
  next hv =>
    rcases lt_abs.mp (h.2 i) with h|p; · exact False.elim (hv (decide_eq_true h))
    exact lt_neg.mp p
lemma starPair_open : IsOpen (P.starPair s n) := by
  have he : P.starPair s n = {r : Vantage | 2*P.costW s n 3 < r 3} ∩
      ⋂ i : Axis, {r | 2*P.costW s n i < |r i|} := by
    ext r; simp only [starPair,Set.mem_inter_iff,Set.mem_iInter,Set.mem_setOf_eq]
  rw [he]
  exact (isOpen_lt continuous_const (continuous_apply _)).inter
    (isOpen_iInter_of_finite (fun i=>isOpen_lt continuous_const (continuous_abs.comp (continuous_apply _))))

lemma rise_bearing (hσ : σ 3 = true) (r : Vantage) (h : r∈shelf (I σ))
    (J : P.Ellis 3 x) : AnalyticOnNhd ℝ (fun t=>P.rise x s n (update r k t) Z Z') (I σ k) := by
  have g : ∀ t∈I σ k, update r k t∈P.starPair s n := fun t u =>
    P.bearing_clear s n σ hσ <| shelf_update h u
  by_cases e : σ k = true
  · have hv : I σ k = Set.Ioi d := if_pos e
    rw [hv] at g ⊢
    intro t ht
    let f := P.rayPair x β γ k r
    have a : AnalyticAt ℝ f (t-d) := rayPair_analytic _ _ _ _ _ _ (sub_pos.mpr ht)
    refine (a.comp (f:=fun x=>x-d) (analyticAt_id.sub analyticAt_const)).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    exact (P.rise_ray_pos x k s n Z Z' r u J (g u hu) hu).symm
  have hv : I σ k = Set.Iio (-d) := if_neg e
  rw [hv] at g ⊢
  intro t ht
  let f := P.rayPair x γ β k (-r)
  have w : -t-d>0 := by have ht : t < -d := ht; linarith only [ht]
  have a : AnalyticAt ℝ f (-t-d) := rayPair_analytic _ _ _ _ _ _ w
  refine (a.comp (f:=fun x=> -x-d) (analyticAt_id.neg.sub analyticAt_const)).congr ?_
  filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
  exact (P.rise_ray_neg x k s n Z Z' r u J (g u hu) hu).symm

def EveryBearing := ∀ τ, τ 3 = true → ∃ r ∈ shelf (I τ), Clean (P.rise x s n r)

lemma pointDense (J : P.Ellis 3 x) (h : P.EveryBearing x s n) : P.starPair s n ⊆
    closure {r ∈ P.starPair s n | Clean (P.rise x s n r)} := by
  intro r v; obtain ⟨τ,e,t⟩ := P.star_bearing s n _ v
  have w : shelf (I τ) ⊆ closure {y ∈ shelf (I τ) | Clean (P.rise x s n y)} :=
    shelf_clean_dense _ _ (P.bearing_open s n τ) (P.bearing_path s n τ)
      (fun y p i j l => P.rise_bearing x i s n j l τ e y p J) (h τ e)
  apply (closure_mono _ (w t)); exact fun _ z => ⟨P.bearing_clear s n τ e z.1,z.2⟩
lemma pairDense (J : P.Ellis 3 x) (h : P.EveryBearing x s n)
    (U : Set (Vantage×Vantage)) (hu : IsOpen U) (y : ∀ z∈U, z.2-z.1∈P.starPair s n) :
    let A := {z ∈ U | Clean (P.rise x s n (z.2-z.1))}
    IsOpen A ∧ U ⊆ closure A := by
  constructor
  · exact hu.inter (clean_open ((P.rise_cont x s n).comp (continuous_snd.sub continuous_fst)))
  exact diff_dense _ hu fun z hz=> closure_mono (fun _ ht=> ht.2)
    (P.pointDense x s n J h (y z hz))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
