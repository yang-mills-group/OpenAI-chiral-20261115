import YM.SU5.Rotation.UnitGap
import YM.SU5.Rotation.Plane
import YM.SU5.Relativistic.Grades

/-!
# Tiny time-space rotations forbid any level-zero collar

Take projections, *with the stated closed physical shields*. Allow an angle-dependent
open neighborhood of the footprint, and even keep the target strictly in the positive
time halfspace when the angle is sufficiently small. Pass this geometry through the
existing definition of the algebra, prior to imposing gauge invariance; the result
will also test any gauge-invariant targets.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 320000
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
open Real (cos sin)

section geometry
variable (Λ:Preparation) (l:ℕ)

/-- Set in primary paper, footprints need no enlargement at base.
Can take any `M` here (for positive time, take above reserve). -/
def squareAt (M : ℤ) : Face ℤ := (M • Lattice.step 0,⟨(2,3),by decide⟩)

def budgetU (M : ℤ) := footprint Λ l 0 (RotationGap.sites (squareAt M))

theorem compactU (M : ℤ) : IsCompact (budgetU Λ l M) := footprint_compact ..

lemma flat_time {M:ℤ} {x:Cover} (h:x∈RotationGap.sites (squareAt M)) : x 0=M := by
  simp [RotationGap.sites, squareAt, square, visits] at h
  rcases h with h|h|h|h|h <;> subst x <;>
    norm_num [step_apply, show (0:Axis) ≠ 2 by decide, show (0:Axis) ≠ 3 by decide]

def radius0 := (Journey.reserve Λ l : ℝ) * Selected.gaugeMesh Λ 0

theorem pos_radius : 0 < radius0 Λ l := by
  unfold radius0
  apply mul_pos (_ : (0:ℝ) < ↑(Journey.reserve Λ l)) (Selected.gaugeMesh_pos Λ 0)
  unfold Journey.reserve; positivity

local notation "r" => radius0 Λ l
local notation "g" => Selected.gaugeMesh Λ 0

lemma proj_U {M : ℤ} {x} (h : x∈ budgetU Λ l M) :
    x 0 ∈ Set.Icc ((M:ℝ)*g - r) ((M:ℝ)*g + r) := by
  obtain ⟨y,h⟩ := Set.mem_iUnion.mp h; obtain ⟨q,h⟩ := Set.mem_iUnion.mp h
  have E := flat_time (M:=M) (x:=y) q
  have he := (show x∈ collar Λ l 0 y from h).2 0
  have hh := (show x∈ collar Λ l 0 y from h).1 0
  rw [lower_gauge, gaugePosition, E] at hh
  rw [upper_gauge, gaugePosition, E] at he
  exact ⟨hh,he⟩

theorem strictly_future {M : ℤ} (e : (Journey.reserve Λ l:ℤ) < M) :
    budgetU Λ l M ⊆ upperRoom 0 := by
  intro x h
  have he : (Journey.reserve Λ l:ℝ) < M := by exact_mod_cast e
  exact lt_of_lt_of_le (sub_pos.mpr (mul_lt_mul_of_pos_right he (Selected.gaugeMesh_pos ..)))
    (proj_U Λ l h).1

/-- Any point in the range box in the first two coordinates can be realized
in the collar. Other coordinates will not enter the width test. -/
private lemma realize (u : Cover) (a b : ℝ) (pa : |a| ≤ r) (pb : |b| ≤ r) :
    ∃ x∈ collar Λ l 0 u, x 0=(u 0:ℝ)*g + a ∧ x 1=(u 1:ℝ)*g + b := by
  let d (i:Axis) := if i=0 then a else if i=1 then b else 0
  let x (i:Axis) := (u i:ℝ)*g + d i
  have hd (i:Axis) : |d i| ≤ r := by unfold d; split_ifs <;> simp [*,(pos_radius Λ l).le]
  refine ⟨x, ?_,?_⟩
  · constructor <;> intro i
    · rw [lower_gauge]; exact (show (u i:ℝ)*g - r ≤ (u i:ℝ)*g + d i by linarith [(abs_le.mp (hd i)).1])
    rw [upper_gauge]; exact (show (u i:ℝ)*g + d i ≤ (u i:ℝ)*g + r by linarith [(abs_le.mp (hd i)).2])
  simp [d,x,show (1:Axis) ≠ 0 by decide]

/-- Price the open slack about the pre-rotation region with just one slab. -/
def tube (θ : ℝ) (M : ℤ) : Set RSpace :=
  (fun x:RSpace => x 0) ⁻¹' Set.Ioo ((M:ℝ)*g - (cos θ + |sin θ|)*r)
    ((M:ℝ)*g + (cos θ + |sin θ|)*r)

theorem open_tube (θ : ℝ) (M : ℤ) : IsOpen (tube Λ l θ M) := isOpen_Ioo.preimage (continuous_apply _)

theorem slack (M : ℤ) {θ : ℝ} (h : θ≠0) (e : |θ|<Real.pi/2) : budgetU Λ l M ⊆ tube Λ l θ M := by
  have h₁ := SU5Rotation.Plane.more_width h e
  intro x v
  have hx := proj_U Λ l v
  have ha := mul_lt_mul_of_pos_right h₁ (pos_radius Λ l); rw [one_mul] at ha
  change _ < x 0 ∧ x 0 < _
  constructor <;> linarith [hx.1,hx.2]

/-- Width obstruction even if asking just that one level-0 site fit the
*tube*, which has open slack with respect to the required footprint. Equality
of half-width `(cos θ + |sin θ|)*r` against this open tube already suffices. -/
theorem width_obstruction (M : ℤ) (θ : ℝ) (u : Cover) :
    ¬ collar Λ l 0 u ⊆ (SU5Rotation.Plane.turn θ '' tube Λ l θ M) := by
  -- it is a slack tube only for qualified angles
  intro h
  let b := (if 0 ≤ sin θ then radius0 Λ l else -(radius0 Λ l))
  have hb : |b| = r := by unfold b; split <;> simp only [abs_neg,abs_of_pos (pos_radius Λ l)]
  have hs : sin θ * b = |sin θ| * r := by
    unfold b; split
    · next s=> rw [abs_of_nonneg s]
    next s=> rw [abs_of_neg (lt_of_not_ge s),mul_neg,neg_mul]
  obtain ⟨x,hx,a₁,a₂⟩ := realize Λ l u r b (abs_le.mpr ⟨by linarith [pos_radius Λ l],le_rfl⟩) hb.le
  obtain ⟨y,hy,b₁,b₂⟩ := realize Λ l u (- (radius0 Λ l)) (-b) (by rw [abs_neg,abs_of_pos (pos_radius Λ l)]) (by rw [abs_neg,hb])
  obtain ⟨p,hp,hpx⟩ := h hx
  obtain ⟨q,hq,hqy⟩ := h hy
  have hp' := SU5Rotation.Plane.proj_turn θ p; rw [hpx,a₁,a₂] at hp'
  have hq' := SU5Rotation.Plane.proj_turn θ q; rw [hqy,b₁,b₂] at hq'
  obtain ⟨_,p'⟩ := (show p 0 ∈ Set.Ioo _ _ from hp)
  obtain ⟨q',_⟩ := (show q 0 ∈ Set.Ioo _ _ from hq)
  linarith only [hp',hq',hs,p',q']

/-- On the physical support rule, hence with Tapestry page units *converted*. -/
theorem no_sites (M : ℤ) (θ : ℝ) (O : Set RSpace) (h : O ⊆ tube Λ l θ M) {S:Finset Cover}
    (e : SupportedPhysically Λ l 0 S (SU5Rotation.Plane.turn θ '' O)) : S=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u p
  apply width_obstruction Λ l M θ u
  refine Set.Subset.trans ?_ (Set.image_mono h)
  intro x hx; exact collar_inside e (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨p,hx⟩⟩)

lemma tube_nbhd (M : ℤ) {θ : ℝ} (h:θ≠0) (e:|θ|< Real.pi/2) (V : Set RSpace)
    (hV : IsOpen V) (pV : budgetU Λ l M ⊆ V) :
    ∃ O : Set RSpace, IsOpen O ∧ IsBounded O ∧ budgetU Λ l M ⊆ O ∧ O ⊆ V ∧ O ⊆ tube Λ l θ M := by
  obtain ⟨d,hd⟩ := (compactU Λ l M).isBounded.subset_ball 0
  refine ⟨Metric.ball 0 d ∩ (V ∩ tube Λ l θ M), Metric.isOpen_ball.inter (hV.inter (open_tube ..)),
    Metric.isBounded_ball.subset Set.inter_subset_left, ?_,fun _ h=>h.2.1,fun _ h=> h.2.2⟩
  intro x v; exact ⟨hd v,pV v,slack Λ l M h e v⟩

lemma future_open : IsOpen (upperRoom 0) := isOpen_Ioi.preimage (continuous_apply _)

/-- Slack *also* allowing the two regions to stay positive, for all
sufficiently small nonzero angles (compare the earlier construction). -/
lemma in_halfspaces {M : ℤ} (hM : (Journey.reserve Λ l:ℤ) < M) :
    ∀ᶠ θ : ℝ in 𝓝[≠] 0, ∃ O : Set RSpace, IsOpen O ∧ IsBounded O ∧ budgetU Λ l M ⊆ O ∧
      O ⊆ upperRoom 0 ∧ (SU5Rotation.Plane.turn θ '' O) ⊆ upperRoom 0 ∧ O ⊆ tube Λ l θ M := by
  let Z := Function.uncurry SU5Rotation.Plane.turn ⁻¹' upperRoom 0
  have hp : ({0}: Set ℝ) ×ˢ budgetU Λ l M ⊆ Z := by
    rintro ⟨θ,x⟩ hx; obtain ⟨hx,hx'⟩ := hx
    have e : θ=0 := hx; subst θ; change SU5Rotation.Plane.turn 0 x ∈ upperRoom 0
    rw [SU5Rotation.Plane.turn_zero]; exact strictly_future Λ l hM hx'
  obtain ⟨u,v,e,f,g',l',m⟩ := generalized_tube_lemma isCompact_singleton (compactU Λ l M)
    (future_open.preimage SU5Rotation.Plane.continuous_turn) hp
  have he : u∈ 𝓝[≠] (0:ℝ) := mem_nhdsWithin_of_mem_nhds (e.mem_nhds (g' (Set.mem_singleton _)))
  filter_upwards [SU5Rotation.Plane.eventually_angles, he] with θ hb hw
  obtain ⟨O,o,k,w,w',u'⟩ := tube_nbhd Λ l M hb.1 hb.2 v f l'
  refine ⟨O,o,k,w,?_,?_,u'⟩
  · intro z hz
    rw [← SU5Rotation.Plane.turn_zero z]
    change ((0:ℝ),z) ∈ Function.uncurry SU5Rotation.Plane.turn ⁻¹' upperRoom 0
    apply m; exact ⟨g' (Set.mem_singleton _), w' hz⟩
  rintro z ⟨y,h,rfl⟩
  change (θ,y) ∈ Function.uncurry SU5Rotation.Plane.turn ⁻¹' upperRoom 0
  apply m; exact ⟨hw,w' h⟩

lemma image_open {O:Set RSpace} (p:IsOpen O) (θ:ℝ) : IsOpen (SU5Rotation.Plane.turn θ '' O) :=
  (SU5Rotation.Plane.turnHomeo θ).isOpenMap O p
lemma image_bounded {O:Set RSpace} (p:IsBounded O) (θ:ℝ) :
    IsBounded (SU5Rotation.Plane.turn θ '' O) :=
  (p.isCompact_closure.image (SU5Rotation.Plane.continuous_turn_single θ)).isBounded.subset
    (Set.image_mono subset_closure)
end geometry

section algebra
variable {Λ : Preparation} {l : ℕ}
    (Y: Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "Δ" => Dome (tent Y H)

lemma empty_scalar {C:Calibration} {wide b : Bool} {f:Family C} (h:InTest C wide ∅ b f) :
    ∃ c:ℂ, f=c • (1:Family C) := by
  induction h with
  | @seed f p =>
    have hu (x y : PairsC) : f x=f y := p.locus x y (by simp [Agrees]) (by simp [Agrees])
    refine ⟨f (1,1),?_⟩; funext m u; unfold scalar; rw [hu _ (1,1)]; rfl
  | creator => simp_all
  | remover => simp_all
  | zero=> exact ⟨0,(zero_smul ..).symm⟩
  | one => exact ⟨1,(one_smul ..).symm⟩
  | smul a _ h => obtain ⟨b,rfl⟩ := h; exact ⟨a*b,(mul_smul ..).symm⟩
  | add _ _ h t => obtain ⟨a,rfl⟩ := h; obtain ⟨b,rfl⟩ := t; exact ⟨a+b,(add_smul ..).symm⟩
  | mul _ _ h t =>
    obtain ⟨a,rfl⟩ := h; obtain ⟨b,rfl⟩ := t
    exact ⟨a*b, by rw [Algebra.smul_mul_assoc, one_mul, mul_smul]⟩

/-- T₀(V) in the test gap (ambient, conversion to Tapestry units, all levels,
not just gauge singlets). -/
abbrev AmbientAt (V : Set RSpace) := jetty Λ l (tent Y H) true (handstamp V) Set.univ

/-- Thus even if an observable is a linear combination with cancellation
and/or has rainfall invariance coupling its slots, it is high-only. -/
theorem forbids_coarse (M : ℤ) (θ : ℝ) {O : Set RSpace} (h : O ⊆ tube Λ l θ M) :
    AmbientAt Y H (SU5Rotation.Plane.turn θ '' O) ≤ highOnly Y H := by
  let V := SU5Rotation.Plane.turn θ '' O
  change jetty Λ l K true (handstamp V) Set.univ ≤ _
  rw [generating]; apply Algebra.adjoin_le
  intro x p; obtain ⟨i,p⟩ := Set.mem_iUnion.mp p; obtain ⟨_,y,q,rfl⟩ := Set.mem_iUnion.mp p
  by_cases e:i=0
  · subst i
    obtain ⟨S,q₁,q₂⟩ := (keeps ..).mp (show y∈ keep Λ l 0 K true (handstamp V) from q)
    rw [no_sites Λ l M θ O h q₂] at q₁
    obtain ⟨c,h⟩ := empty_scalar ((Tapestry.locates ..).mp q₁)
    change pinhole Δ 0 y ∈ highOnly Y H
    rw [show y=c • (1 : Dome K) from Subtype.ext h,map_smul,map_one]
    exact (highOnly Y H).smul_mem (Subalgebra.one_mem _) _
  change pinhole Δ i y ∈ highOnly Y H
  exact pokes (Set.Ici 1) (fun i=> keep Λ l i K true Set.univ) (show i∈ Set.Ici 1 from Nat.pos_of_ne_zero e)
    (rooms Λ l i K true (handstamp V) (Set.subset_univ _) q)

lemma pol_ambient (V : Set RSpace) : Pol Y H V ≤ AmbientAt Y H V :=
  fun _ p => ((well_spec ..).mp p).1

theorem moved_region (M : ℤ) {θ : ℝ} (h:θ ≠ 0) (e:|θ| < Real.pi/2) :
    ∃ O : Set RSpace, IsOpen O ∧ IsBounded O ∧ budgetU Λ l M ⊆ O ∧
      AmbientAt Y H (SU5Rotation.Plane.turn θ '' O) ≤ highOnly Y H := by
  obtain ⟨O,x,y,z,_,t⟩ := tube_nbhd Λ l M h e _ isOpen_univ (Set.subset_univ _)
  exact ⟨O,x,y,z,forbids_coarse Y H M θ t⟩
end algebra
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction

#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.in_halfspaces
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.moved_region
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.width_obstruction
