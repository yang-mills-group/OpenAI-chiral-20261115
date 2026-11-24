import YM.SU5.Six.Bearing
import YM.SU5.Six.ZoomReceipt
import YM.SU5.Six.NoonHeat
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
open Aria YM.OS YM.Six Set Cheer
variable (P : Spine) (x : P.Spectrum0 3) (s n : ℕ) (σ : Axis → Bool)

/-- Relative pose for the small position test only. -/
def noonPose (j : Axis) :=
    if j=3 then 10*P.dew s n else
      if σ j = true then 3*P.costW s n j else -(3*P.costW s n j)

variable {P} {c r : ℕ → ℕ} (A : Launch P c r)
set_option quotPrecheck false
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "ψ" i:max => P.noonPose (c i) (r i) σ
local notation "w" i:max => P.costW (c i) (r i)

include A
lemma noon_clear_time : ∀ᶠ i : ℕ in atTop, 2*((w i) 3)<10*(ρ i) := by
  have h := (P.costW_ratio_time c r A).eventually <|
    gt_mem_nhds (show (5:ℝ)/2<5 by norm_num)
  filter_upwards [h] with i hi
  have ht := (div_lt_iff₀ (P.dew_pos _ (A.unitSize i))).mp hi
  linarith only [ht]

lemma noon_in_shelf : ∀ᶠ i : ℕ in atTop, ∀ σ' : Axis→Bool, σ' 3 = true→
    P.noonPose (c i) (r i) σ' ∈ shelf (P.bearing (c i) (r i) σ') := by
  filter_upwards [noon_clear_time A] with i h t v j
  unfold bearing noonPose
  by_cases e : j=3
  · subst j; simpa only [↓reduceIte,v,Set.mem_Ioi]
  rw [if_neg e]
  have hj := P.costW_pos (c i) (r i) j
  split <;> simp only [Set.mem_Ioi,Set.mem_Iio] <;> linarith only [hj]

lemma noon_short :
    Tendsto (fun i => (ρ i)⁻¹ • spacePart (ψ i)) atTop (𝓝 (0:Space3)) := by
  let f (i:ℕ) (j : Fin 3) := (ψ i) j.castSucc / (ρ i)
  have was (j : Fin 3) : Tendsto (fun i=>((ψ i) j.castSucc) / (ρ i)) atTop (𝓝 0) := by
    let k : Axis := j.castSucc
    have hj : k≠3 := (Fin.castSucc_lt_last j).ne
    have hz := (P.costW_ratio_space c r A k hj).const_mul 3
    rw [mul_zero] at hz
    change Tendsto (fun i=>(ψ i) k / _) _ _
    simp_rw [noonPose,if_neg hj]
    split
    · exact hz.congr <| fun i => (mul_div_assoc ..).symm
    have ht := hz.neg
    rw [neg_zero] at ht
    exact ht.congr <| fun i => by rw [neg_div,mul_div_assoc]
  have h := ((PiLp.continuous_toLp 2 (fun _ : SpaceAxis => ℝ)).tendsto 0).comp
    (show Tendsto f atTop (𝓝 0) from tendsto_pi_nhds.mpr was)
  refine h.congr fun i => ?_
  apply PiLp.ext; intro j
  exact div_eq_inv_mul ((ψ i) j.castSucc) (ρ i)

lemma noon_taper :
    HalfLimit (fun i => tapered ((ρ i)⁻¹ • spacePart (ψ i)) 10 (P.incT (c i) (r i)/dewN A i))
      (tapered 0 10 (1/2)) := by
  apply tapered_limit (noon_short σ A)
  apply NNReal.tendsto_coe.mp
  simp_rw [NNReal.coe_div]
  push_cast; exact P.incT_ratio c r A

set_option maxHeartbeats 300000 in
lemma noon_bill (i : ℕ) :
    P.rise x (c i) (r i) (ψ i) = P.zoomBill x (c i) (r i)
      (tapered ((ρ i)⁻¹ • spacePart (ψ i)) 10 (P.incT (c i) (r i)/dewN A i)) := by
  let T := P.incT (c i) (r i)
  have hd : (dewN A i) > 0 := P.dew_pos _ (A.unitSize i)
  have he : Real.toNNReal ((ψ i) 3) = 10*dewN A i := by
    rw [noonPose,if_pos rfl]; convert Real.toNNReal_coe using 1; simp [dewN];rfl
  rw [rise,he,zoomBill,
    show (fun p => tapered ((ρ i)⁻¹ • spacePart (ψ i)) 10 (P.incT (c i) (r i)/dewN A i)
        (Cheer.zoom (ρ i) p)) = _ from funext (tapered_zoom hd _ T)]
  ext1 Z Z'; exact P.risingK_app ..

omit A
/-- Limiting matrix at noon poses. -/
def noonMat := Matrix.diagonal (fun Z : Window.Family =>
    ∫ p, tapered 0 10 (1/2) p ∂(promenade Z:Measure E4))
lemma noonMat_clean : Clean noonMat := by
  let g : Window.Family → ℂ := fun Z=>∫ p, tapered 0 10 (1/2) p ∂(promenade Z:Measure E4)
  have h (Z) : 0 < g Z := tapered_positive _ (home_bright Z) (fun {_}=> importance Z)
  constructor
  · rw [noonMat, Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>(h i).ne')
  intro i; rw [noonMat,Matrix.diagonal_apply_eq]; exact (h i).ne'

variable {x} {K : P.Register} (H : P.SixElection K x c r)
include H
lemma SixElection.noon_tends : Tendsto (fun i=>P.rise x (c i) (r i) (ψ i)) atTop
    (𝓝 noonMat) := (H.zoom.integrals (noon_taper σ H.launch)).congr
      (fun i => (noon_bill x σ H.launch i).symm)
lemma SixElection.star_works : ∀ᶠ i in atTop, P.EveryBearing x (c i) (r i) := by
  have h : ∀ᶠ i in atTop, ∀ a : Axis → Bool, Clean (P.rise x (c i) (r i) (P.noonPose (c i) (r i) a)) :=
    Filter.eventually_all.mpr (fun a => (H.noon_tends a).eventually <|
      (clean_open continuous_id).mem_nhds noonMat_clean)
  exact ((noon_in_shelf H.launch).and h).mono (fun i g τ v=>⟨_,g.1 τ v,g.2 τ⟩)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
