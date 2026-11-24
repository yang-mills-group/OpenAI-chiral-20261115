import YM.SU5.Obstruction.Proper
import YM.SU5.Obstruction.Contact

/-!
# No zero-level collar in the moved region

An angle-dependent open slack (no claim with fixed padding independent
of the rotation) for every such mixing rotation. Works even in the larger
loose algebra; we can afford to localize just up to representatives for the
reading against the single J.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter MeasureTheory Metric
open Lattice SU Buffered Buffered.Afterglow Tapestry Satin
open Py Py.Rate LocalLimit Preparation Journey Vale
open Tapestry.Altitude
open Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice Tower.Reconstruction
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra

section Geometry

/-- Face in axes 2,3. Base point high on the time axis when making the positive half-space test. -/
def spatial (m : ℤ) : Lattice.Face ℤ := (m • step 0, ⟨(2,3),by decide⟩)

variable (Λ : Preparation) (l : ℕ) (m : ℤ)

lemma common_time (u : Cover) (p : u ∈ faceSites (spatial m)) : u 0 = m := by
  rw [faceSites_list] at p
  change u ∈ [m • step 0, m • step 0 + step 2,
    m • step 0 + step 2 + step 3,m • step 0 + step 3,m • step 0].toFinset at p
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at p
  rcases p with rfl|rfl|rfl|rfl|rfl <;> simp [show (0:Axis) ≠ 2 by decide, show (0:Axis) ≠ 3 by decide]

def regionZero := footprint Λ l 0 (faceSites (spatial m))
def halfLength := (reserve Λ l : ℝ) * gaugeMesh Λ 0
lemma halfLength_pos : 0 < halfLength Λ l :=
  mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (gaugeMesh_pos Λ 0)

local notation "r" => halfLength Λ l
local notation "g" => gaugeMesh Λ 0
local notation "U" => regionZero Λ l m

lemma time_bounds (v : RSpace) (p : v ∈ U) : |v 0 - (m:ℝ)*g| ≤ r := by
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp p
  obtain ⟨q, z⟩ := Set.mem_iUnion.mp hx
  have he := common_time m x q
  have h₀ := (show v ∈ collar Λ l 0 x from z).1 0
  have h₁ := (show v ∈ collar Λ l 0 x from z).2 0
  rw [lower_gauge,gaugePosition,he] at h₀; rw [upper_gauge,gaugePosition,he] at h₁
  unfold halfLength; rw [abs_le]; constructor <;> linarith

lemma positive_side (h : (reserve Λ l : ℤ) < m) :
    U ⊆ {v : RSpace | 0 < v 0} := by
  intro v hv
  have ht := (abs_le.mp (time_bounds Λ l m v hv)).1
  have he : halfLength Λ l < (m:ℝ)*g :=
    mul_lt_mul_of_pos_right (by exact_mod_cast h) (gaugeMesh_pos Λ 0)
  change 0 < v 0; linarith

private lemma width_excess (φ : ℝ) (p : 0 < |φ|) (q : |φ| < Real.pi / 2) :
    r < r * (Real.cos φ + |Real.sin φ|) := by
  have ht := abs_lt.mp q
  have hc := Real.cos_pos_of_mem_Ioo (show φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from ht)
  have hs := abs_pos.mpr (mixes p q)
  have h := Real.sin_sq_add_cos_sq φ
  exact lt_mul_of_one_lt_right (halfLength_pos Λ l)
    (by nlinarith [sq_abs (Real.sin φ), mul_pos hc hs])

private lemma corners (x : Cover) :
    collarLower Λ l 0 x ∈ collar Λ l 0 x ∧
    collarUpper Λ l 0 x ∈ collar Λ l 0 x := by
  have h : collarLower Λ l 0 x ≤ collarUpper Λ l 0 x := by
    intro i
    have hp := halfLength_pos Λ l
    change location Λ 0 x i - r ≤ location Λ 0 x i + r
    linarith
  exact ⟨⟨le_rfl,h⟩,⟨h,le_rfl⟩⟩

private lemma crosses {u v : RSpace} (x : Cover) (i : Axis)
    (hu : u ∈ collar Λ l 0 x) (hv : v ∈ collar Λ l 0 x) :
    update u i (v i) ∈ collar Λ l 0 x := by
  constructor <;> intro j <;> by_cases h : j = i
  · subst j; rw [update_self]; exact hv.1 i
  · rw [update_of_ne h]; exact hu.1 j
  · subst j; rw [update_self]; exact hv.2 i
  rw [update_of_ne h]; exact hu.2 j

private def strip (φ : ℝ) :=
  {u : RSpace | |u 0 - (m:ℝ)*g| < r * (Real.cos φ + |Real.sin φ|)}

-- Project onto the rotated 0 direction.
private lemma endpoints (x : Cover) (φ : ℝ) :
    ∃ v ∈ collar Λ l 0 x, ∃ w ∈ collar Λ l 0 x,
      (Real.cos φ * w 0 + Real.sin φ * w 1) - (Real.cos φ * v 0 + Real.sin φ * v 1) =
        2 * (r * (Real.cos φ + |Real.sin φ|)) := by
  let a := collarLower Λ l 0 x
  let b := collarUpper Λ l 0 x
  have h := corners Λ l x
  by_cases e : 0 ≤ Real.sin φ
  · refine ⟨a,h.1,b,h.2,?_⟩
    unfold a b collarLower collarUpper halfLength
    rw [abs_of_nonneg e]; ring
  have ht : (0 : Axis) ≠ 1 := by decide
  refine ⟨update a 1 (b 1), crosses Λ l x 1 h.1 h.2,
    update b 1 (a 1), crosses Λ l x 1 h.2 h.1,?_⟩
  simp only [update_of_ne ht, update_self, abs_of_neg (lt_of_not_ge e)]
  unfold a b collarLower collarUpper halfLength
  ring

private lemma no_fit (φ : ℝ) (x : Cover) :
    ¬ collar Λ l 0 x ⊆ roll (planeRotation φ) '' strip Λ l m φ := by
  intro h
  obtain ⟨v,hv,w,hw,a⟩ := endpoints Λ l x φ
  obtain ⟨u,s,rfl⟩ := h hv
  obtain ⟨u',s',rfl⟩ := h hw
  rw [roll_project,roll_project] at a
  have ht := (abs_lt.mp (show |u 0-(m:ℝ)*g| < _ from s)).1
  have h' := (abs_lt.mp (show |u' 0-(m:ℝ)*g| < _ from s')).2
  linarith

lemma rigid_image (f : SO) {V : Set RSpace} (p : IsOpen V) (q : Bornology.IsBounded V) :
    IsOpen (roll f '' V) ∧ Bornology.IsBounded (roll f '' V) := by
  obtain ⟨u,hu⟩ := roll_homeo f
  rw [← hu]; refine ⟨u.isOpenMap V p,?_⟩
  apply Bornology.IsBounded.subset ((q.isCompact_closure.image u.continuous).isBounded)
  exact Set.image_mono subset_closure

/-- Open bounded neighborhood of the footprint; in the rigidly moved region, not even
one level-zero site pays the support rule. -/
lemma rotated_no_fit (φ : ℝ) (p : 0 < |φ|) (q : |φ| < Real.pi / 2) :
    ∃ V : Set RSpace, IsOpen V ∧ Bornology.IsBounded V ∧ U ⊆ V ∧
      ∀ x : Cover, ¬ collar Λ l 0 x ⊆ roll (planeRotation φ) '' V := by
  let F := strip Λ l m φ
  obtain ⟨b,z⟩ := (show IsCompact U from footprint_compact ..).isBounded.subset_ball (0 : RSpace)
  have ht : IsOpen F := isOpen_lt (((continuous_apply (0:Axis)).sub continuous_const).abs) continuous_const
  refine ⟨F ∩ ball 0 b,ht.inter isOpen_ball,
    isBounded_ball.subset Set.inter_subset_right, fun x hx => ?_,fun x h => ?_⟩
  · exact ⟨lt_of_le_of_lt (time_bounds _ _ _ x hx) (width_excess Λ l φ p q), z hx⟩
  exact no_fit Λ l m φ x (Set.Subset.trans h (Set.image_mono Set.inter_subset_left))

lemma fit_collar {F : Set RSpace} {S : Finset Cover} (x : Cover) (s : ℕ) (h : x ∈ S)
    (p : SupportedPhysically Λ l s S F) : collar Λ l s x ⊆ F := by
  intro u hu
  let v : RSpace := fun i => 2 * u i
  have he : (fun i : Axis => v i/2) = u := by funext i; unfold v; ring
  have ht := p x h
  rw [shield_collar] at ht
  rw [← he]
  apply ht (a:=v)
  change (fun i : Axis => v i/2) ∈ collar Λ l s x; rw [he]; exact hu

/-- If desired, the slack can even be taken to stay inside a prescribed
larger open (before AND after movement), once the rotation is small. In
particular one may keep both regions strictly inside positive time. Still
no claim of a uniform nonzero budget of slack. -/
lemma rotated_tight {E : Set RSpace} (p : IsOpen E) (h : U ⊆ E) :
    ∀ᶠ φ : ℝ in 𝓝[≠] (0:ℝ),
      ∃ V : Set RSpace, IsOpen V ∧ Bornology.IsBounded V ∧ U ⊆ V ∧ V ⊆ E ∧
        roll (planeRotation φ) '' V ⊆ E ∧
        ∀ x : Cover, ¬ collar Λ l 0 x ⊆ roll (planeRotation φ) '' V := by
  let f (x : ℝ × RSpace) := roll (planeRotation x.1) x.2
  have hf : Continuous f := by
    have hc : Continuous (fun x : ℝ => planeRotation x) := plane_continuous
    unfold f roll
    exact (continuous_subtype_val.comp (hc.comp continuous_fst)).matrix_mulVec continuous_snd
  have hF (x : RSpace) : f (0,x) = x := by
    change roll (planeRotation 0) x = _; rw [plane_zero]; exact Matrix.one_mulVec _
  have hi : ({0} : Set ℝ).prod U ⊆ f ⁻¹' E := by
    rintro ⟨a,x⟩ ⟨(ha : a = 0),t⟩
    subst a; change f (0,x) ∈ E; rw [hF]; exact h t
  obtain ⟨O,G,v,w,h₀,t,s⟩ := generalized_tube_lemma isCompact_singleton
    (show IsCompact U from footprint_compact ..) (p.preimage hf) hi
  have he : ∀ᶠ φ : ℝ in 𝓝 (0:ℝ), |φ| < Real.pi / 2 :=
    continuous_abs.continuousAt (gt_mem_nhds (by rw [abs_zero]; apply half_pos Real.pi_pos))
  filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds he,
    (self_mem_nhdsWithin : ({0} : Set ℝ)ᶜ ∈ 𝓝[≠] (0:ℝ)),
    (show ∀ᶠ φ : ℝ in 𝓝 (0:ℝ), φ ∈ O from v.mem_nhds (h₀ (Set.mem_singleton 0))).filter_mono
      nhdsWithin_le_nhds] with φ ha hb hc
  obtain ⟨V,o,p₀,k,b⟩ := rotated_no_fit Λ l m φ (abs_pos.mpr hb) ha
  refine ⟨V ∩ (G ∩ E),o.inter (w.inter p),p₀.subset Set.inter_subset_left,
    (fun x hx => ⟨k hx,t hx,h hx⟩),
    Set.Subset.trans Set.inter_subset_right Set.inter_subset_right,?_,fun x he => ?_⟩
  · rintro _ ⟨x,z,rfl⟩; exact (s (a:=(φ,x)) ⟨hc,z.2.1⟩)
  exact b x (Set.Subset.trans he (Set.image_mono Set.inter_subset_left))

end Geometry

section Exhausted

lemma emptySupport_scalar {K : Calibration} {b w : Bool} {f : Buffered.Family K}
    (p : InTest K w ∅ b f) : ∃ c : ℂ, f = c • (1 : Buffered.Family K) := by
  induction p with
  | @seed x h =>
    have ha (u v : Lifted.PairsC) : x u = x v :=
      h.locus u v (by intro i p; simp at p) (by intro i p; simp at p)
    exact ⟨x (1,1),funext fun m => funext fun z =>
      congrArg (fun v : ℂ => v • (1 : Fock.FC _)) (ha _ _)⟩
  | creator i h v => simp at v
  | remover i h v => simp at v
  | zero => exact ⟨0,by rw [zero_smul]⟩
  | one => exact ⟨1,by rw [one_smul]⟩
  | smul r _ ih => obtain ⟨c,e⟩ := ih; exact ⟨r*c,by rw [e,smul_smul]⟩
  | add _ _ ih jh => obtain ⟨c,e⟩ := ih; obtain ⟨b,h⟩ := jh; exact ⟨c+b,by rw [e,h,add_smul]⟩
  | mul _ _ ih jh =>
    obtain ⟨c,e⟩ := ih; obtain ⟨b,h⟩ := jh
    refine ⟨c*b,?_⟩; rw [e,h,Algebra.smul_mul_assoc,one_mul,smul_smul]

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "A" => Dome K

lemma no_sites_no_coarse (V : Set RSpace) (p : ∀ x, ¬ collar Λ l 0 x ⊆ V) :
    loosePol Y H V Set.univ ≤ higherOnly Y H 0 := by
  rw [loosePol, generating]
  apply Algebra.adjoin_le
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_,y,hy,rfl⟩ := Set.mem_iUnion.mp hi
  change y ∈ keep Λ l i K true (handstamp V) at hy
  cases i with
  | zero =>
    obtain ⟨S,h,t⟩ := (keeps ..).mp hy
    have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun u z => p u (fit_collar Λ l u 0 z t))
    subst S
    obtain ⟨r,w⟩ := emptySupport_scalar ((locates K ∅ true).mp h)
    have v : y = r • (1 : Dome K) := Subtype.ext w
    change pinhole A 0 y ∈ higherOnly Y H 0
    rw [v,map_smul,map_one]
    exact (higherOnly Y H 0).smul_mem ((higherOnly Y H 0).one_mem) r
  | succ n =>
    rw [higherOnly_eq]; apply Algebra.subset_adjoin
    exact Set.mem_iUnion.mpr ⟨n+1, Set.mem_iUnion.mpr
      ⟨Set.mem_Ici.mpr (by omega),Set.mem_image_of_mem _ (Set.mem_univ y)⟩⟩

lemma loose_in_region (V : Set RSpace) : Pol Y H V ≤ loosePol Y H V Set.univ :=
  fun _ h => ((well_spec ..).mp h).1

lemma rotated_only_high (m : ℤ) (φ : ℝ) (p : 0 < |φ|) (q : |φ| < Real.pi / 2) :
    ∃ V : Set RSpace, IsOpen V ∧ Bornology.IsBounded V ∧ regionZero Λ l m ⊆ V ∧
      loosePol Y H (roll (planeRotation φ) '' V) Set.univ ≤ higherOnly Y H 0 := by
  obtain ⟨V,s,v,a,h⟩ := rotated_no_fit Λ l m φ p q
  exact ⟨V,s,v,a,no_sites_no_coarse Y H _ h⟩

end Exhausted
end YM.CF.SatinRotation
#print axioms YM.CF.SatinRotation.rotated_only_high
