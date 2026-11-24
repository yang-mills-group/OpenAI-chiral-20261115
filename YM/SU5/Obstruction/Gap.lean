import YM.SU5.Obstruction.Support

/-!
# Retesting readings: obstruction to even weak local/continuous rotation law

We don't formalize a topology on the test algebra here. The necessary condition
we disprove is already correlation continuity (at the identity, just moving W
and retesting against J). No assumptions on how the readings might be obtained
except that the value in that correlation can be approximated by the same kind
of reading of a local product, in every bounded open moved neighborhood as
specified. Thus no subtleties about rotation-composition or motion of the
character are needed.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter MeasureTheory Metric Bornology
open Lattice SU Buffered Buffered.Afterglow Tapestry Satin
open Py Py.Rate LocalLimit Preparation Journey Vale
open Tapestry.Altitude
open Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice Tower.Reconstruction
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
  {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Buffered.Family (tent Y H) → ℂ}
  {L : Rack Λ l} {B : Clay Λ l}
  {T : ℕ → ℕ → Tariff} {t : ℕ → Tariff} (D : Fashion Y H a b I E L B T t)
  (G : SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
  (C : ∀ j : Axis, Tower.Arena Y H G.history.circuit j 0 false)
  (c : (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
  (m : ℤ)

local notation "A" => Dome (tent Y H)
local notation "S" => sch Y H D G C c
local notation "J" => countertest Y H 0 (spatial m) D.toExhibition
local notation "W" => plaquetteWord Y H 0 (spatial m)
local notation "U" => regionZero Λ l m

/-- Values arbitrarily approximable even just in the J-retest, allowing all loose local tests
in the specified region as the other factor. This is only closure in ℂ. -/
def approxValues (V : Set RSpace) : Set ℂ := closure
  ((fun y : Cloud A => S (J*y)) '' (loosePol Y H V Set.univ : Set (Cloud A)))

/-- Any bona fide limit of these local retest readings would qualify. -/
theorem approx_of_limit (V : Set RSpace) {α : Type*} {q : Filter α} [q.NeBot]
    (u : α → Cloud A) (z : ℂ) (h : Tendsto (fun i => S (J * u i)) q (𝓝 z))
    (p : ∀ᶠ i in q, u i ∈ loosePol Y H V Set.univ) : z ∈ approxValues Y H D G C c m V :=
  mem_closure_of_tendsto h (p.mono fun _ t => Set.mem_image_of_mem _ t)

lemma approx_high_zero {V : Set RSpace} (p : loosePol Y H V Set.univ ≤ higherOnly Y H 0) :
    approxValues Y H D G C c m V ⊆ {0} := by
  apply closure_minimal _ isClosed_singleton
  rintro _ ⟨v,h,rfl⟩; exact (show S (J*v) = 0 from sch_high Y H 0 (spatial m) D G C c v (p h))

/-- Supports measured with the existing physical collar; even allow any prescribed bounded
open neighborhood of W's support, not insisting that a rotated test be found in the rotated
closed footprint itself. The defeating open neighborhood is rotation dependent. -/
def Retestable (x : SO) (y : ℂ) : Prop :=
  ∀ V : Set RSpace, IsOpen V → IsBounded V → U ⊆ V →
    y ∈ approxValues Y H D G C c m (roll x '' V)

lemma rotation_only_zero (φ : ℝ) (p : 0 < |φ|) (q : |φ| < Real.pi / 2) (y : ℂ)
    (w : Retestable Y H D G C c m (planeRotation φ) y) : y = 0 := by
  obtain ⟨V,h,e,u,t⟩ := rotated_only_high Y H m φ p q
  exact approx_high_zero Y H D G C c m t (w V h e u)

/-- Slack may be kept inside positive time, on both sides, for small rotations
of a positive-time footprint. -/
theorem positive_room_zero (w : (reserve Λ l : ℤ) < m) :
    ∀ᶠ φ : ℝ in 𝓝[≠] (0:ℝ), ∃ V : Set RSpace,
      IsOpen V ∧ IsBounded V ∧ U ⊆ V ∧
      V ⊆ {v : RSpace | 0 < v 0} ∧
      roll (planeRotation φ) '' V ⊆ {v : RSpace | 0 < v 0} ∧
      loosePol Y H (roll (planeRotation φ) '' V) Set.univ ≤ higherOnly Y H 0 ∧
      approxValues Y H D G C c m (roll (planeRotation φ) '' V) ⊆ {0} := by
  filter_upwards [rotated_tight Λ l m (isOpen_lt continuous_const (continuous_apply _))
    (positive_side Λ l m w)] with φ h
  obtain ⟨V,i,b,v,p,q,h⟩ := h
  have hv := no_sites_no_coarse Y H (roll (planeRotation φ) '' V) h
  exact ⟨V,i,b,v,p,q,hv,approx_high_zero Y H D G C c m hv⟩

lemma path_mixes :
    ∀ᶠ φ : ℝ in 𝓝[>] (0:ℝ), 0 < |φ| ∧ |φ| < Real.pi / 2 := by
  have he : ∀ᶠ φ : ℝ in 𝓝 (0:ℝ), |φ| < Real.pi / 2 :=
    continuous_abs.continuousAt (gt_mem_nhds (by rw [abs_zero]; apply half_pos Real.pi_pos))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ))] with φ a b
  exact ⟨abs_pos.mpr ((Set.mem_Ioi.mp b).ne'),a⟩

-- Thus this much more specific retesting continuity along ONE ordinary
-- path of proper rotations is already incompatible with local reachability.
theorem path_gap (u : ℝ → ℂ)
    (e : ∀ᶠ φ : ℝ in 𝓝[>] (0:ℝ), Retestable Y H D G C c m (planeRotation φ) (u φ)) :
    ¬ Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 (S (J*W))) := by
  intro h
  have ht : u =ᶠ[𝓝[>] (0:ℝ)] fun _ => (0:ℂ) := by
    filter_upwards [path_mixes,e] with i p q
    exact rotation_only_zero Y H D G C c m i p.1 p.2 (u i) q
  have hu : S (J*W) = 0 := tendsto_nhds_unique_of_eventuallyEq h tendsto_const_nhds ht
  rw [sch_JW] at hu
  exact one_ne_zero hu

lemma along_rotations : Tendsto planeRotation (𝓝[>] (0:ℝ)) (𝓝[≠] (1:SO)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨rotation_limit.mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [path_mixes] with φ h
  exact Set.mem_compl_singleton_iff.mpr (rotation_ne h.1 h.2)

/-- Even approximate movement of W, requiring only localization of its answers to the J-retest
in arbitrary bounded open moved neighborhoods separately at each such rotation, rules out
continuity of that fixed retested correlation at the identity (with its correct value there). -/
theorem continuity_gap (u : SO → ℂ)
    (p : ∀ᶠ x : SO in 𝓝[≠] (1 : SO), Retestable Y H D G C c m x (u x))
    (v : u 1 = S (J*W)) : ¬ ContinuousAt u 1 := by
  intro h
  apply path_gap Y H D G C c m (u ∘ planeRotation) (along_rotations.eventually p)
  rw [← v]
  exact h.tendsto.comp (rotation_limit.mono_left nhdsWithin_le_nhds)

/-- In particular with exact support movement of the single W and the unmodified products. -/
lemma not_continuous_local (τ : SO → Cloud A)
    (i : τ 1 = W)
    (p : ∀ᶠ x : SO in 𝓝[≠] (1 : SO), ∀ V : Set RSpace, IsOpen V → IsBounded V →
      U ⊆ V → τ x ∈ Pol Y H (roll x '' V)) :
    ¬ ContinuousAt (fun x : SO => S (J * τ x)) 1 := by
  apply continuity_gap Y H D G C c m (fun x => S (J*τ x)) _ (by rw [i])
  filter_upwards [p] with x h
  intro V a b e
  exact subset_closure (Set.mem_image_of_mem _ (loose_in_region Y H _ (h V a b e)))

/-- Summary on one and the same character of the election (input `c`, so in particular applies
to that sample). Correlation continuity cost is already impossible at this one rotation test. -/
def Obstruction : Prop :=
    ∃ M : ℕ, Even M ∧ (reserve Λ l : ℕ) < M ∧
      let V := regionZero Λ l M
      let F := plaquetteWord Y H 0 (spatial M)
      let Q := countertest Y H 0 (spatial M) D.toExhibition
      IsCompact V ∧ V ⊆ {v : RSpace | 0 < v 0} ∧
      F ∈ PolAt Y H 0 V ∧ Q ∈ PolAt Y H 1 V ∧ Q*F ∈ PolAt Y H 1 V ∧
      S (Q*F) = 1 ∧
      (∀ y : Cloud A, y ∈ higherOnly Y H 0 → S (Q*y) = 0) ∧
      (∀ φ : ℝ, 0 < |φ| → |φ| < Real.pi / 2 →
        ∃ O : Set RSpace, IsOpen O ∧ IsBounded O ∧ V ⊆ O ∧
          loosePol Y H (roll (planeRotation φ) '' O) Set.univ ≤ higherOnly Y H 0 ∧
          approxValues Y H D G C c M (roll (planeRotation φ) '' O) ⊆ {0}) ∧
      (∀ u : SO → ℂ,
        (∀ᶠ x : SO in 𝓝[≠] (1 : SO), Retestable Y H D G C c M x (u x)) →
        u 1 = S (Q*F) → ¬ ContinuousAt u 1)

lemma obstruction_holds : Obstruction Y H D G C c := by
  let n := reserve Λ l+1
  let M := n+n
  have hm : reserve Λ l < M := by unfold M n; omega
  refine ⟨M,⟨n,rfl⟩,hm,?_⟩
  obtain ⟨p,q,r,u,e⟩ := unit_gap Y H 0 (spatial M) D G C c
  refine ⟨footprint_compact ..,positive_side Λ l M (by exact_mod_cast hm),p,q,r,u,e,?_,
    continuity_gap Y H D G C c M⟩
  intro φ m m'; obtain ⟨V,h,k,v,s⟩ := rotated_only_high Y H M φ m m'
  exact ⟨V,h,k,v,s,approx_high_zero Y H D G C c M s⟩

end YM.CF.SatinRotation
#print axioms YM.CF.SatinRotation.path_gap
#print axioms YM.CF.SatinRotation.continuity_gap
#print axioms YM.CF.SatinRotation.not_continuous_local
#print axioms YM.CF.SatinRotation.obstruction_holds
