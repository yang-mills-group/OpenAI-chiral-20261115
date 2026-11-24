import YM.SU5.Rotation.Moved

/-!
# Support plus (one-factor) retested continuity is impossible

Even if the correlation value using a purported rotated W is merely recoverable to
arbitrary accuracy by retesting with *any* local ambient block observables in place
of the rotated W. All on the same character. Not an estimate with positive distance
between the insertions, nor simultaneous-test rotation invariance alone.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
open Exhibition Tower.Selected Tapestry.RotationGap
open Bornology
open YM.SU5Rotation

section test
variable {Λ:Preparation} {l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ} {E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l} {B:Clay Λ l}
    {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} (D:Fashion Y H a b I E L B T t)
    (G:GroundExtension (i:=a) (k:=b) (E:=E) Y H) (C:∀ j:Axis, Tower.Arena Y H G.history.circuit j 0 false)
    (χ: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
    (M:ℤ)
local notation "K" => tent Y H
local notation "Δ" => Dome (tent Y H)
local notation "J" => retestJ Y H D.toExhibition (squareAt M)
local notation "W" => coarseW Y H (squareAt M)
local notation "Sχ" => sch Y H D G C χ
local notation "U" => budgetU Λ l M

/-- Approximation allowed here is in the VALUES, with this fixed local J. -/
def pricesFrom (V : Subalgebra ℂ (Altitude.Cloud Δ)) : Set ℂ :=
  closure ((fun x => (Sχ) (J*x)) '' (V:Set (Altitude.Cloud Δ)))

lemma of_such_limits {N:Type*} {F:Filter N} [NeBot F] (V : Subalgebra ℂ (Altitude.Cloud Δ))
    (f:N→Altitude.Cloud Δ) (φ:ℂ) (h: ∀ᶠ n in F, f n ∈ V) (p:Tendsto (fun n=> (Sχ) (J*f n)) F (𝓝 φ)) :
    φ ∈ pricesFrom Y H D G C χ M V :=
  isClosed_closure.mem_of_tendsto p (h.mono (fun i u=> subset_closure (Set.mem_image_of_mem _
    (show f i ∈ (V:Set (Altitude.Cloud Δ)) from u))))

theorem only_zero {V : Subalgebra ℂ (Altitude.Cloud Δ)} (p:V ≤ highOnly Y H) :
    pricesFrom Y H D G C χ M V = {0} := by
  refine Set.Subset.antisymm (closure_minimal ?_ isClosed_singleton) ?_
  · rintro x ⟨x,h,rfl⟩; exact Set.mem_singleton_iff.mpr (selected_JZ Y H D G C χ _ (p h))
  apply Set.singleton_subset_iff.mpr
  exact subset_closure (Set.mem_image_of_mem (fun x => (Sχ) (J*x))
    (show (0:Altitude.Cloud Δ)∈(V:Set (Altitude.Cloud Δ)) from V.zero_mem) |> fun h=> by
      simpa only [mul_zero,map_zero] using h)

/-- The pointwise gap (all the indicated angles). -/
theorem open_region_gap {θ : ℝ} (h:θ≠0) (e:|θ|<Real.pi/2) :
    ∃ O : Set RSpace, IsOpen O ∧ IsBounded O ∧ U ⊆ O ∧
      AmbientAt Y H (Plane.turn θ '' O) ≤ highOnly Y H ∧
      pricesFrom Y H D G C χ M (AmbientAt Y H (Plane.turn θ '' O))={0} ∧
      (Sχ) (J*W)=1 := by
  obtain ⟨O,hO,hB,hU,v⟩ := moved_region Y H M h e
  exact ⟨O,hO,hB,hU,v,only_zero Y H D G C χ M v,selected_JW ..⟩

/-- Small-angle obstruction version even just requiring recovery of the retest when both
regions stay in **strictly positive time halfspace**. This would follow from recovery at
every sufficiently small punctured angle in *every* (bounded open) neighborhood allowed
by localization of W, in particular any containing U. Note the order of quantifiers! -/
def FitsMotion (P : ℝ → ℂ) : Prop :=
  ∀ᶠ θ : ℝ in 𝓝[≠] 0,
    ∀ O : Set RSpace, IsOpen O → IsBounded O → budgetU Λ l M ⊆ O →
      O ⊆ upperRoom 0 → Plane.turn θ '' O ⊆ upperRoom 0 →
      P θ ∈ pricesFrom Y H D G C χ M (AmbientAt Y H (Plane.turn θ '' O))

theorem prices_zero (hM : (Journey.reserve Λ l:ℤ)<M) (P : ℝ → ℂ)
    (p:FitsMotion Y H D G C χ M P) : ∀ᶠ θ : ℝ in 𝓝[≠] 0, P θ = 0 := by
  filter_upwards [p,in_halfspaces Λ l hM] with θ h e
  obtain ⟨O,t,w,v,f,q,e⟩ := e
  have hp := h O t w v f q
  rw [only_zero Y H D G C χ M (forbids_coarse Y H M θ e)] at hp
  exact Set.mem_singleton_iff.mp hp

/-- Failure of retested continuity (`eq:ret` of f9574346).
Limits of local retest prices (any filters/nets with eventual localization too)
are already allowed by `FitsMotion`. No extension, action, quotient, topology
on observables or vacuum-rotation hypothesized. -/
theorem obstruction (hM : (Journey.reserve Λ l:ℤ)<M) (P : ℝ → ℂ)
    (p:FitsMotion Y H D G C χ M P) : ¬ Tendsto P (𝓝[≠] 0) (𝓝 ((Sχ) (J*W))) := by
  intro h; rw [selected_JW] at h
  have hz : (1:ℂ)=0 := tendsto_nhds_unique_of_eventuallyEq h tendsto_const_nhds
    (prices_zero Y H D G C χ M hM P p)
  exact one_ne_zero hz

theorem not_continuous (hM : (Journey.reserve Λ l:ℤ)<M) (P : Plane.SO4 → ℂ)
    (v : P 1=(Sχ) (J*W)) (p : FitsMotion Y H D G C χ M (fun θ => P (Plane.rotate θ))) :
    ¬ ContinuousAt P 1 := fun h => obstruction Y H D G C χ M hM _ p
      (by rw [←v]; exact h.tendsto.comp Plane.lim_rotate)

/-- Not even an orbit of W with this continuity and localization -- thus rules out (e.g.) an
action extending to all proper rotations *on this test algebra* with test localization on
bounded open sets, and independently-moved, retested selected correlation continuous at the
identity. Here is a precise exact-image version requiring `Z : SO(4) → Cloud`, Z(1)=W,
and localization near 0 angle of the images of W in the **Pol** algebra. (Don't even impose
the other action properties.) -/
theorem exact_orbit_fails (hM : (Journey.reserve Λ l:ℤ)<M) (Z : Plane.SO4 → Altitude.Cloud Δ)
    (v : Z 1=W) (p : ∀ᶠ θ : ℝ in 𝓝[≠] 0, ∀ O : Set RSpace, IsOpen O → IsBounded O →
      W ∈ Pol Y H O → Z (Plane.rotate θ) ∈ Pol Y H (Plane.turn θ '' O)) :
    ¬ ContinuousAt (fun g => (Sχ) (J * Z g)) 1 := by
  apply not_continuous Y H D G C χ M hM _ (by rw [v])
  filter_upwards [p] with θ h O e k u _ _
  have ht : W ∈ Pol Y H O := pol_of_level Y H (isotone Y H u (coarse_in ..))
  exact subset_closure (Set.mem_image_of_mem _ ((pol_ambient Y H _)
    (h O e k ht) : Z (Plane.rotate θ) ∈ (AmbientAt Y H (Plane.turn θ '' O) : Set _)))

/-- Scope check. If the open slack were fixed *before* passing to sufficiently small
angles, even W itself could be used in the target sets. The hypothesis we refute (with
continuity) allows specifically the footprint to be tested in however-tight bounded open regions
at EACH such angle (angle-neighborhood not depending on O). -/
lemma fixed_neighborhood (O : Set RSpace) (h : IsOpen O) (e : budgetU Λ l M ⊆ O) :
    ∀ᶠ θ in 𝓝 0, W ∈ Pol Y H (Plane.turn θ '' O) := by
  have he : ({0}: Set ℝ) ×ˢ budgetU Λ l M ⊆ Function.uncurry Plane.turn ⁻¹' O := by
    rintro ⟨θ,x⟩ p; obtain ⟨p,q⟩ := p; have he : θ=0 := p; subst θ; change Plane.turn 0 x∈ O
    rw [Plane.turn_zero]; exact e q
  obtain ⟨u,v,a,_,b,d,f⟩ := generalized_tube_lemma isCompact_singleton (compactU Λ l M)
    (h.preimage Plane.continuous_turn) he
  have hx : Tendsto Neg.neg (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg (G:=ℝ)).continuousAt (x:=0) |>.tendsto
  filter_upwards [hx.eventually (show ∀ᶠ t in 𝓝 0, t∈ u from a.mem_nhds (b (Set.mem_singleton _)))] with θ e'
  have hO : budgetU Λ l M ⊆ Plane.turn θ '' O := by
    intro x p; refine ⟨Plane.turn (-θ) x, ?_, by simpa only [neg_neg] using Plane.turn_inverse (-θ) x⟩
    change (-θ,x)∈ Function.uncurry Plane.turn ⁻¹' O; apply f; exact ⟨e', d p⟩
  exact pol_of_level Y H (isotone Y H hO (coarse_in ..))

/-- Statement for export to the Election. The unit gap on every high-only observable in the
ambient polynomial algebra. M uniform in the two computations in that the same
chosen plaquette works through all small angles (and any M sufficiently positive will do).
The failure with even very weak assumptions on motion tested by these actual Sch readings.
For actual orbits localized in the resolution net use e.g. `exact_orbit_fails`. -/
def FixedResolutionGap : Prop :=
  ∀ M:ℤ, (Journey.reserve Λ l:ℤ)<M →
    let U₀ := budgetU Λ l M
    let W₀ := coarseW Y H (squareAt M)
    let J₀ := retestJ Y H D.toExhibition (squareAt M)
    IsCompact U₀ ∧ U₀ ⊆ upperRoom 0 ∧ W₀∈ PolAt Y H 0 U₀ ∧ J₀∈ PolAt Y H 1 U₀ ∧
    (Sχ) (J₀ * W₀)=1 ∧ (∀ Z∈ highOnly Y H, (Sχ) (J₀ * Z)=0) ∧
    (∀ θ:ℝ, θ≠0 → |θ|<Real.pi/2 →
      ∃ O : Set RSpace, IsOpen O ∧ IsBounded O ∧ U₀ ⊆ O ∧
        AmbientAt Y H (Plane.turn θ '' O) ≤ highOnly Y H ∧
        pricesFrom Y H D G C χ M (AmbientAt Y H (Plane.turn θ '' O))={0}) ∧
    ∀ P : ℝ → ℂ, FitsMotion Y H D G C χ M P → ¬ Tendsto P (𝓝[≠] 0) (𝓝 ((Sχ) (J₀ * W₀)))

theorem result : FixedResolutionGap Y H D G C χ := by
  intro n hn V W' J'
  refine ⟨compactU ..,strictly_future Λ l hn,coarse_in Y H (squareAt n),
    retest_in Y H D.toExhibition (squareAt n),selected_JW Y H D G C χ (squareAt n),
    fun _ h=> selected_JZ Y H D G C χ (squareAt n) h,
    ?_, obstruction Y H D G C χ n hn⟩
  intro θ h e; obtain ⟨O,v,w,f,t,g,_⟩ := open_region_gap Y H D G C χ n h e
  exact ⟨O,v,w,f,t,g⟩

end test
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction

#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.fixed_neighborhood
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.of_such_limits
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.result
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.exact_orbit_fails
