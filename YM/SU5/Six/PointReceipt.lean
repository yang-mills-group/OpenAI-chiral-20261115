import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Six.NoonPose
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
/-- Center sets (apply also to closures) with Euclidean time order and all
projection disjointness; for compact sets yields positive distances. -/
def AllApart (U V : Set Vantage) := ∀ p∈U, ∀ q∈V,
    p 3 < q 3 ∧ ∀ j, q j ≠ p j

variable (P : Spine) (x : P.Spectrum0 3)
/-- Pose domains priced for any pair, full footprint boxes. -/
def StarTests (s n : ℕ) (U V : Set Vantage) := ∀ p∈U, ∀ q∈V, q-p∈P.starPair s n
lemma StarTests.apart {P : Spine} {s n : ℕ} {U V : Set Vantage}
    (h : P.StarTests s n U V) (Z Z' : Window.Family) :
    AllApart (⋃ p∈U, (P.incB s n Z).crate P p) (⋃ q∈V, (P.incA Z' s n).crate P q) := by
  intro y hy z hz
  simp only [Set.mem_iUnion] at hy hz
  obtain ⟨p,g,hy⟩ := hy; obtain ⟨q,v,hz⟩ := hz
  obtain ⟨hp,hq⟩ := h p g q v
  change ∀ j, |y j - p j| ≤ P.costW s n j at hy
  change ∀ j, |z j - q j| ≤ P.costW s n j at hz
  simp only [Pi.sub_apply] at hp hq
  constructor
  · have ⟨a,b⟩ := abs_le.mp (hy 3); have ⟨c,d⟩ := abs_le.mp (hz 3); linarith only [hp,b,c]
  intro j e
  have ⟨a,b⟩ := abs_le.mp (hy j); have ⟨c,d⟩ := abs_le.mp (hz j)
  rcases lt_abs.mp (hq j) with w|w <;> linarith only [w,e,a,b,c,d]

lemma star_ready (U V : Set Vantage) (u : IsCompact U) (v : IsCompact V) (h : AllApart U V)
    (c r : ℕ → ℕ) (A : Launch P c r) : ∀ᶠ i in atTop, P.StarTests (c i) (r i) U V := by
  have hx : ∀ᶠ i in atTop, ∀ j, ∀ p∈U, ∀ q∈V,
      2*P.costW (c i) (r i) j < |(q-p : Vantage) j| := by
    apply Filter.eventually_all.mpr; intro j
    let f : Vantage×Vantage → ℝ := fun z=> |z.2 j - z.1 j|
    have hf : Continuous f := continuous_abs.comp <|
      ((continuous_apply j).comp continuous_snd).sub ((continuous_apply j).comp continuous_fst)
    obtain ⟨a,g,w⟩ := (u.prod v).exists_forall_le' hf.continuousOn
      (fun z t => abs_pos.mpr <| sub_ne_zero.mpr ((h _ t.1 _ t.2).2 j))
    have ht := (P.costW_go c r A j).eventually (gt_mem_nhds (half_pos g))
    exact ht.mono (fun i θ p t q s=> lt_of_lt_of_le (by linarith only [θ] :
          2 * P.costW (c i) (r i) j < a) (w (p,q) ⟨t,s⟩))
  filter_upwards [hx] with i hi p hp q hq
  refine ⟨?_,fun j=>hi j _ hp _ hq⟩
  have e : 0 < (q-p : Vantage) 3 := sub_pos.mpr ((h _ hp _ hq).1)
  simpa only [abs_of_pos e] using hi 3 _ hp _ hq

lemma spotMesh_go : Tendsto (P.spotMesh) atTop (𝓝 0) := NNReal.tendsto_coe.mpr (MeshClock.vanishes _)
lemma spot_seek (p : Vantage) :
    ∃ d : ℕ → Cover, Tendsto (fun t=> P.gridSpot t (d t)) atTop (𝓝 p) := by
  let f (t : ℕ) := P.spotMesh t
  let d (t : ℕ) (j : Axis) := ⌊p j / f t⌋
  refine ⟨d,tendsto_pi_nhds.mpr fun j => ?_⟩
  have h : Tendsto (fun t=>p j - f t) atTop (𝓝 (p j)) := by
    simpa using (tendsto_const_nhds (x:=p j)).sub (P.spotMesh_go)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds ?_ ?_
  · intro i
    change p j - f i ≤ (d i j : ℝ)*f i
    have ht := (div_lt_iff₀ (P.spotMesh_pos i)).mp (Int.lt_floor_add_one (p j / f i))
    dsimp [d,f] at *
    linarith only [ht]
  intro i; exact (le_div_iff₀ (P.spotMesh_pos i)).mp (Int.floor_le ..)

lemma spot_tends (s n : ℕ) (p q : Vantage) (J : P.Ellis 3 x) (h : q-p∈P.starPair s n)
    (d e : ℕ → Cover)
    (hd : Tendsto (fun t=>P.gridSpot t (d t)) atTop (𝓝 p))
    (he : Tendsto (fun t=>P.gridSpot t (e t)) atTop (𝓝 q)) :
    Tendsto (fun t=>P.spotMat x s n t (d t) (e t)) atTop (𝓝 (P.rise x s n (q-p))) := by
  have hu := he.sub hd
  refine (((P.rise_cont x s n).tendsto _).comp hu).congr' ?_
  filter_upwards [hu.eventually ((P.starPair_open s n).mem_nhds h),eventually_ge_atTop s] with t ht g
  exact (P.spotMat_rise x s n J t g (d t) (e t) ht).symm

/-!
### Public receipt at a probe `i`, before refinement

Rank in this statement is the **point** assertion in Part (ii).
-/
local notation "Z" => Window.Family
local notation "ξ" => P.advocate 3 x 3
local notation "S" => P.seasons 3 ξ
local notation "Q" => YM.OS.Semigroup.ℚmeasure S
variable (s n : ℕ)

structure Unsmeared : Prop where
  center (T : Z) :
    P.incV x T s n = (1 - (S).E (P.incT s n) : (P.ManyF 3 ξ).Op) (P.birthCloud x T s n)
  positive (T : Z) : (Q).region night (P.incV x T s n) = 0
  connected (t : ℕ) (g : s ≤ t) (p : Vantage) (d : Cover) (T : Z) :
    ∀ D ∈ [P.incA T s n,P.incB s n T],
       P.bodyOne x D p = 0 ∧ P.sixM x t (P.castAt D t d) = 0 ∧
       P.castAt D t d ∈ P.locatedIn t (D.crate P (P.gridSpot t d))
  price (p q : Vantage) (h : 2 * P.costW s n 3 < (q-p) 3) (T U : Z) :
    P.bodyPair x (P.incB s n T) (P.incA U s n) p q = P.rise x s n (q-p) T U
  spectral (r : Vantage) (T U : Z) : P.rise x s n r T U =
    (Q).pairIntegral (tapered (spacePart r) (Real.toNNReal (r 3)) (P.incT s n))
      (P.birthCloud x T s n) (P.birthCloud x U s n)
  wired (t : ℕ) (g : s ≤ t) (d e : Cover) (h : P.gridSpot t e - P.gridSpot t d ∈ P.starPair s n) :
    P.spotMat x s n t d e = P.rise x s n (P.gridSpot t e - P.gridSpot t d)
  limit (p q : Vantage) (h : q-p∈P.starPair s n)
    (d e : ℕ → Cover)
    (hd : Tendsto (fun t=>P.gridSpot t (d t)) atTop (𝓝 p))
    (he : Tendsto (fun t=>P.gridSpot t (e t)) atTop (𝓝 q)) :
    Tendsto (fun t=>P.spotMat x s n t (d t) (e t)) atTop (𝓝 (P.rise x s n (q-p)))
  rank (U V : Set Vantage) (u : IsOpen U) (v : IsOpen V) (y : P.StarTests s n U V) :
    let A := {z ∈ U ×ˢ V | Clean (P.rise x s n (z.2-z.1))}
    IsOpen A ∧ U ×ˢ V ⊆ closure A

/-- For **any** starting six-election, at all sufficiently fine `i`
(independent of pose decisions), rank in the native point kernels
on that election as above. -/
theorem SixElection.unsmeared {P : Spine} {x : P.Spectrum0 3} {K : P.Register} {c r : ℕ → ℕ}
    (H : P.SixElection K x c r) : ∀ᶠ i in atTop, P.Unsmeared x (c i) (r i) := by
  filter_upwards [H.star_works] with i h
  constructor
  · exact fun T=>P.dark ..
  · exact fun T=>P.incV_night ..
  · intro t g p d T D hd
    have f : ∀ p' : Vantage, P.bodyOne x D p' = 0 := by
      rcases List.mem_cons.mp hd with rfl|w
      · exact P.bodyOne_incA x _ _ H.ellis _
      rw [List.mem_singleton] at w
      subst D; exact fun _=>P.bodyOne_incB x _ _ H.ellis _ _
    have e : D.s ≤ t := by simp at hd; rcases hd with rfl|rfl <;> exact g
    exact ⟨f _, (P.castAt_price x H.ellis D e d).trans (f _), P.castAt_located D K e d⟩
  · exact fun p q g T U=>P.bodyPair_rise x p q _ _ T U H.ellis g
  · exact fun _ T U => P.risingK_app ..
  · exact P.spotMat_rise x _ _ H.ellis
  · exact fun p q => P.spot_tends x _ _ p q H.ellis
  intro U V u v y
  exact P.pairDense x _ _ H.ellis h _ (u.prod v)
    (fun z hz => y _ hz.1 _ hz.2)

theorem SixElection.reservePair {P : Spine} {x : P.Spectrum0 3} {K : P.Register} {c r : ℕ → ℕ}
    (H : P.SixElection K x c r) (U V : Set Vantage) (u : IsCompact (closure U))
    (v : IsCompact (closure V)) (q : AllApart (closure U) (closure V)) :
    ∀ᶠ i in atTop, P.StarTests (c i) (r i) (closure U) (closure V) :=
  P.star_ready _ _ u v q _ _ H.launch

#print axioms SixElection.unsmeared
#print axioms SixElection.reservePair
#print axioms StarTests.apart
#print axioms spot_seek
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
