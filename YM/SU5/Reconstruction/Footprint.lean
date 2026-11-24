import VerifiedSatinSelectedSectors
/-! Euclidean support, rung-zero matter units. See `the construction notes`. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-- A ball in the physical max norm (over the four axes). -/
noncomputable def stamp (Λ : Preparation) (l s : ℕ) (x : Cover) : Set RSpace :=
  Metric.closedBall (PhaseChoice.location Λ s x) ((reserve Λ l : ℝ)*gaugeMesh Λ s)

noncomputable def silhouette (Λ : Preparation) (l s : ℕ) (S : Finset Cover) : Set RSpace :=
  ⋃ x ∈ S, stamp Λ l s x

section
open Set
variable {Λ : Preparation} {l s : ℕ} {S T : Finset Cover} {U : Set RSpace} {x : Cover} {u v : RSpace}

lemma clock_units (Λ : Preparation) (s : ℕ) :
    gaugeMesh Λ s=1/(2*precisionAt Λ s) := rfl
lemma spatial_units (Λ : Preparation) (s : ℕ) (x : Cover) :
    location Λ s x = gaugePosition Λ s x := by
  ext i
  unfold location gaugePosition
  rw [clock_units,markZ]
  ring

lemma silhouette_compact (Λ : Preparation) (l s : ℕ) (S : Finset Cover) :
    IsCompact (silhouette Λ l s S) := S.finite_toSet.isCompact_biUnion fun x _ => isCompact_closedBall ..
lemma silhouette_iff : u∈silhouette Λ l s S ↔ ∃ x∈S,u∈stamp Λ l s x := by
  simp [silhouette]

lemma stamp_abs : u∈ stamp Λ l s x ↔
    ∀ i, |u i-gaugePosition Λ s x i|≤ (reserve Λ l:ℝ)*gaugeMesh Λ s := by
  have p : 0≤ (reserve Λ l:ℝ)*gaugeMesh Λ s := mul_nonneg (by positivity) (gaugeMesh_pos ..).le
  rw [stamp,mem_closedBall,spatial_units,dist_eq_norm,pi_norm_le_iff_of_nonneg p]
  simp only [Pi.sub_apply,Real.norm_eq_abs]

lemma half_in_stamp (v : RSpace) :
    (fun i=> v i/2)∈ stamp Λ l s x ↔ v∈ Tapestry.shield Λ l s x := by
  rw [stamp_abs]; unfold Tapestry.shield
  have ht := positiveScale Λ s
  have hx := gaugeMesh_pos Λ s
  let h (i : Axis) := v i
  have he (i : Axis) : v i/2-gaugePosition Λ s x i=(precisionAt Λ s*v i-x i)*gaugeMesh Λ s := by
    rw [gaugePosition,clock_units]
    field_simp
  change (∀ i, |_ - _| ≤ _) ↔ (∀ i, |_ - _| ≤ _)
  simp_rw [he,abs_mul,abs_of_pos hx,mul_le_mul_iff_left₀ hx]

lemma supported_iff : SupportedPhysically Λ l s S U ↔ silhouette Λ l s S ⊆ U := by
  constructor
  · intro h u hu; obtain ⟨x,hx,px⟩ := silhouette_iff.mp hu
    let v : RSpace := fun i => 2 * u i
    have t : (fun i : Axis => v i/2)=u := funext fun i=>by unfold v; ring
    have e : v∈Tapestry.shield Λ l s x := (half_in_stamp v).mp (t.symm ▸ px)
    rw [← t]; exact h x hx e
  intro h x hx u v
  exact h (silhouette_iff.mpr ⟨x,hx,(half_in_stamp u).mpr v⟩)

lemma sheltered_still (n : ℕ) :
    silhouette Λ l (s+n) (volumeAround Λ l n S) ⊆ silhouette Λ l s S :=
  supported_iff.mp ((supported_iff.mpr Set.Subset.rfl).persists n)

lemma stamp_range {δ : ℝ} {j : Axis} (D : PhysicalHush (Λ:=Λ) (l:=l) s j S T δ)
    (p : u∈silhouette Λ l s S) (q : v∈silhouette Λ l s T) : u j+δ ≤ v j := by
  obtain ⟨x,i,h⟩ := silhouette_iff.mp p; obtain ⟨y,k,w⟩ := silhouette_iff.mp q
  have hx := (abs_le.mp (stamp_abs.mp h j)).2
  have hv := (abs_le.mp (stamp_abs.mp w j)).1
  have hh := D.2 0 x i y k
  change gaugePosition Λ s x j+ (reserve Λ l:ℝ)*gaugeMesh Λ s+δ ≤
    gaugePosition Λ s y j - (reserve Λ l:ℝ)*gaugeMesh Λ s at hh
  linarith
lemma stamp_disjoint {δ : ℝ} {j : Axis} (D : PhysicalHush (Λ:=Λ) (l:=l) s j S T δ) :
    Disjoint (silhouette Λ l s S) (silhouette Λ l s T) := by
  apply Set.disjoint_left.mpr; intro x hx ht
  have h := stamp_range D hx ht
  linarith [D.1]

lemma silhouette_union : silhouette Λ l s (S ∪ T) = silhouette Λ l s S ∪ silhouette Λ l s T := by
  ext x; simp only [Set.mem_union,silhouette_iff, Finset.mem_union]; aesop

end

/-- Local algebra on authorized heights with SU(5) gauge invariance. Explicit carrier
(a union, not freeing up losing the height data). `true` is the full even system, `false`
requires first-link continuous in the source. -/
noncomputable def localEuclidean (Λ : Preparation) (l : ℕ) (K : Calibration) (wide : Bool) (A : Set RSpace) : Subalgebra ℂ (Cloud (Dome K)) where
  carrier := {x|∃ (s : ℕ) (U : Set RSpace), IsCompact U ∧ U ⊆ A ∧ x∈ circum Λ l K wide U (Set.Iic s)}
  zero_mem' := ⟨0,∅,isCompact_empty,Set.empty_subset _,Subalgebra.zero_mem _⟩
  one_mem' := ⟨0,∅,isCompact_empty,Set.empty_subset _,Subalgebra.one_mem _⟩
  algebraMap_mem' z := ⟨0,∅,isCompact_empty,Set.empty_subset _,Subalgebra.algebraMap_mem _ z⟩
  add_mem' {x y} p q := by
    obtain ⟨s,U,h,t,m⟩ := p; obtain ⟨r,W,u,v,k⟩ := q
    exact ⟨max s r,U∪W,h.union u,Set.union_subset t v,
      (circum Λ l K wide (U∪W) (Set.Iic (max s r))).add_mem
        (wellGrows Λ K l wide _ _ _ _ (Set.Iic_subset_Iic.mpr (le_max_left ..)) (Set.preimage_mono (Set.subset_union_left)) m)
        (wellGrows Λ K l wide _ _ _ _ (Set.Iic_subset_Iic.mpr (le_max_right ..)) (Set.preimage_mono (Set.subset_union_right)) k)⟩
  mul_mem' {x y} p q := by
    obtain ⟨s,U,h,t,m⟩ := p; obtain ⟨r,W,u,v,k⟩ := q
    exact ⟨max s r,U∪W,h.union u,Set.union_subset t v,
      (circum Λ l K wide (U∪W) (Set.Iic (max s r))).mul_mem
        (wellGrows Λ K l wide _ _ _ _ (Set.Iic_subset_Iic.mpr (le_max_left ..)) (Set.preimage_mono (Set.subset_union_left)) m)
        (wellGrows Λ K l wide _ _ _ _ (Set.Iic_subset_Iic.mpr (le_max_right ..)) (Set.preimage_mono (Set.subset_union_right)) k)⟩

section
variable {Λ : Preparation} {l : ℕ} {K : Calibration} {x : Cloud (Dome K)} {wide : Bool} {s : ℕ} {U A : Set RSpace}
lemma local_iff : x∈localEuclidean Λ l K wide A ↔
    ∃ (s : ℕ) (U : Set RSpace), IsCompact U ∧ U ⊆ A ∧ x∈ circum Λ l K wide U (Set.Iic s) := Iff.rfl
lemma local_in (h : U ⊆ A) : localEuclidean Λ l K wide U ≤ localEuclidean Λ l K wide A := by
  intro y ⟨s,W,t,p,q⟩; exact ⟨s,W,t,p.trans h,q⟩
lemma local_wide : localEuclidean Λ l K wide A ≤ localEuclidean Λ l K true A := by
  intro y ⟨s,W,t,p,q⟩; exact ⟨s,W,t,p,wellWider Λ K l wide (handstamp W) (Set.Iic s) q⟩
lemma local_at (p : IsCompact U) (h : x∈ circum Λ l K wide U (Set.Iic s)) : x∈ localEuclidean Λ l K wide U := ⟨s,U,p,Set.Subset.rfl,h⟩
lemma local_singlet (p : x∈ localEuclidean Λ l K wide U) : x∈ FiniteGaugeDataPoly K ∧ ∀ u:GPhysical, rainfall Λ K u x=x := by
  obtain ⟨s,W,_,_,t⟩ := p
  exact ⟨wellPolynomial Λ K l wide (handstamp W) (Set.Iic s) t,((well_spec Λ K l wide (handstamp W) _).mp t).2⟩

end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
