import YM.SU5.Selected.Region
import YM.SU5.Selected.RootWitness
import YM.Ground.Spectrum
/-!
# A.e. selection in the common ground of the entire coherent history

Paper plan:
use `shade` even-steps/clock spacing and all countable spatial grid unitaries.
Their countably weighted average in Slabs singles out the joint ground *as a locus*.
Accepting this lot like that in the normalized state GNS is a real-part max, and we
use pillars (measure of the ground *for the chosen axis*, other axis ground vectors
agree as previous file). The integral of the second moment of the **limit** of the
averages equals the compressed vector norm, exactly integral of the square modulus
of the conditioned reading, due to commutativity and faithfulness. DCT thus identifies
the points inside each aperture with a.e. rank one across *all* axes.
Generic results imported from `YM.Ground.Spectrum` are `tiny` and `supports` (themselves
used there for another history), on completely general continuous space/algebra; no
local state data from that construction or its spectrum postulates are used here.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
variable (P : Spine)(j : Axis)
local notation "A" => P.Hil j
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "V"=> P.law
local notation "π"=> P.history
local notation "Qt"=>P.projection.clipped
local notation "C₀"=> P.room j
local notation "M"=> timeMesh P.par
local notation "U" i:max=> P.shiftOp j i
local notation "Ω"=> P.floorVec j
local notation "B"=> P.Slabs j
local notation "W"=> P.Ensemble j
instance : StarOrderedRing (P.Slabs j) := sub_positive  («A»:=(A).Op) _
instance : StarOrderedRing (P.Ensemble j) := sub_positive  («A»:=(P.groundHil j).Op) _
local notation "℘" => P.compressionAlgebra j
abbrev euclOp := advance P.run P.large P.law P.history.circuit j 0 false (P.room j)
lemma heat_admitted (t : ℝ≥0) : P.euclOp j t∈ P.slabAlgebra j := by
  rcases eq_zero_or_pos t with rfl|p; · rw [euclOp,advance_source]; exact one_mem _
  let y : ℝ≥0→ℂ:=fun a=> ((a:ℝ):ℂ)*Complex.I; let x :ℕ→ℕ:=fun s=> ⌊ t / mill M s⌋₊+1; let S :ℕ→ℝ≥0:=fun s=> whenly M s (x s)
  have he(a:ℝ≥0)(h:0<a):continued Y H V (π).circuit j 0 false C₀ (y a)= P.euclOp j a:= agrees_euclid Y H V (π).circuit j 0 false C₀ h
  rw [← he t p]
  have hp(a:ℝ≥0)(h:0<a): y a∈ {x:ℂ| 0<x.im}:=by change 0 < (y a).im; simpa [y] using (show (0:ℝ)<(a:ℝ) by exact_mod_cast h)
  have h : Tendsto (fun s=> y (S s)) atTop (𝓝 (y t)):= (by unfold y; fun_prop : Continuous y).continuousAt.tendsto.comp (shade M t)
  apply (P.wholeClosed j).mem_of_tendsto ((holo Y H V (π).circuit j 0 false C₀ _ (hp _ p)).continuousAt.tendsto.comp h)
  refine Eventually.of_forall (fun n=>?_); have ht:0<x n:=Nat.zero_lt_succ _
  simp only [Function.comp_apply]; rw [he _ (when_pos M _ _ ht),show P.euclOp j (S n)=_ from (ticket_birth Y H V n π Qt j false C₀ (x n) ht).symm]; exact P.blocks_admitted j (P.tile_one j n _ ht _)
noncomputable def Eucl (t : ℝ≥0) : P.Slabs j := ⟨P.euclOp j t,P.heat_admitted j t⟩
lemma heat_norm (t : ℝ≥0): ‖P.Eucl j t‖ ≤1 := advance_small ..
abbrev movesOf (x : Grid j) : P.Slabs j := ⟨U x,P.moves_admitted j x⟩
lemma grow (g : Grid j): ‖P.movesOf j g‖ ≤1 := by
  -- helper lemma norm of adjoint
  exact (CStarRing.norm_of_mem_unitary (P.shift_unitary j g)).le
abbrev Slot0 := (ℕ × ℕ) ⊕ (Grid j)
abbrev dial (v : Slot0 j) : B:= Sum.elim (fun x : ℕ×ℕ=> P.Eucl j (whenly M x.1 x.2)) (P.movesOf j) v
abbrev starsVisible := (exists_surjective_nat (Slot0 j)).choose
def shiftsAndTimes (n : ℕ) : P.Slabs j:= P.dial j (starsVisible j n)
lemma visible {L : B → Prop} : (∀ i, L (P.shiftsAndTimes j i)) ↔
    (∀ s n, L (P.Eucl j (whenly (timeMesh P.par) s n))) ∧ ∀ g, L (P.movesOf j g):=by
  constructor
  · intro p; have ht (x:Slot0 j): L (P.dial j x):= by obtain ⟨n,rfl⟩:= (exists_surjective_nat (Slot0 j)).choose_spec x; exact p n
    exact ⟨fun s n=> ht (.inl (s,n)),fun g=> ht (.inr g)⟩
  intro p x; unfold shiftsAndTimes
  cases starsVisible j x with
  | inl i=> exact p.1 ..
  | inr g=> exact p.2 g
lemma slots_small (n : ℕ): ‖P.shiftsAndTimes j n‖≤1:= (P.visible j (L:=fun x=> ‖x‖≤1)).mpr ⟨fun _ _=>P.heat_norm j _,P.grow j⟩ n

def jointTest : P.Slabs j:= cog (P.shiftsAndTimes j)
local notation "J"=> P.jointTest j
lemma testing_norm : ‖P.jointTest j‖ ≤1:= cog_norm_le _ (P.slots_small j)
lemma joint_ext (G : Hilbert)(ρ : P.Slabs j→⋆ₐ[ℂ] G.Op) (y : G) : ρ (P.jointTest j) y=y ↔
    (∀ s n,ρ (P.Eucl j (whenly (timeMesh P.par) s n)) y=y) ∧ ∀g,ρ (P.movesOf j g) y=y :=
  (cog_fixes (P.shiftsAndTimes j) (P.slots_small j) ρ y).trans (P.visible j (L:=fun x=>ρ x y=y))
lemma joint_is : ((P.jointTest j).val.eqLocus (1:(A).Op))= (P.vacuum j) := by
  apply SetLike.ext; intro x
  change (J).val x = x ↔ _; rw [P.ground_ok j]
  rw [show (J).val= (P.slabAlgebra j).subtype J from rfl,P.joint_ext j A (P.slabAlgebra j).subtype]
  refine ⟨fun p=> ⟨fun t=>?_,p.2⟩,fun p=>⟨fun s n=> p.1 _,p.2⟩⟩
  apply tendsto_nhds_unique ((advance_strong Y H V (π).circuit j 0 false C₀ x).continuous.continuousAt.tendsto.comp (shade M t))
  exact tendsto_const_nhds.congr (fun i=> (p.1 i _).symm)
lemma joint_limit (x : A) : Tendsto (fun n=> (sweep (P.jointTest j) n).val x) atTop (𝓝 (P.inHil j (P.piZero j x))):=by
  have p:=(sweep_maps (J) (P.testing_norm j) (show P.Slabs j →⋆ₐ[ℂ] (A).Op from (P.slabAlgebra j).subtype) x)
  -- rw Submodule with dependent instance via congruent equality
  suffices H' : ∀ u v:Submodule ℂ A, ∀ [u.HasOrthogonalProjection][v.HasOrthogonalProjection], u=v→ (u.orthogonalProjectionOnto x).val=(v.orthogonalProjectionOnto x).val by
    change Tendsto _ _ (𝓝 (((P.vacuum j).orthogonalProjectionOnto x).val)); rw [← H' _ _ (P.joint_is j)]; exact p
  intro X Y₁ p q HX; subst Y₁; rfl
lemma joint_shadow : P.shadow j (P.jointTest j)=1:= by
  apply Subtype.ext; ext1 x
  change P.piZero j ((J).val x.val)=x
  have h:x.val∈ (J).val.eqLocus 1:= (P.joint_is j).symm ▸ x.property
  rw [show (J).val x.val=x.val from h]; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

section select
local notation "ω"=> P.groundZero j
local notation "ℍ"=> P.groundHil j
private lemma sub_pos_compress (G : Hilbert) (N : Submodule ℂ G) [CompleteSpace N] (x : G.Op) (e : 0 ≤ x) :
    0 ≤ (N.orthogonalProjectionOnto).comp (x.comp (N.subtypeL)) := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr; rw [← N.adjoint_subtypeL]; exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp e).adjoint_conj N.subtypeL
lemma positive_ (x : P.Slabs j) (e : 0≤x) : 0 ≤ P.shadow j x := sub_pos_compress (A) (P.vacuum j) x.val e
noncomputable def portion (t:P.Spectrum0 j) : (P.Slabs j)→ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
  ((P.chi j t).toLinearMap.comp (P.shadow j).toLinearMap) (by
    intro x h; simpa only [LinearMap.comp_apply] using! show (0:ℂ)≤P.chi j t (P.shadow j x) from
      map_nonneg (P.chi j t) (P.positive_ j x h))
lemma portion_val (t:P.Spectrum0 j) (x : P.Slabs j) : P.portion j t x=P.chi j t (P.shadow j x):=rfl
lemma portion_unit (t:P.Spectrum0 j) : P.portion j t 1=1:=by rw [P.portion_val,P.shadow_one,map_one]
lemma portion_joint (t : P.Spectrum0 j) : P.portion j t (P.jointTest j)=1:=by rw [P.portion_val,P.joint_shadow,map_one]
lemma portion_cont (x : P.Slabs j) : Continuous (fun t=> P.portion j t x):= P.chi_joint j _

/-- Time mesh plus all transverse mesh movements are tested in the GNS of a portion; the root contains its cyclic vector. -/
lemma portion_root (x:P.Spectrum0 j) : origin (P.portion j x)∈ rooted (P.portion j x) (P.jointTest j) :=
  (gns_full _ (P.portion_unit j x) _ (P.testing_norm j)).mpr (by rw [P.portion_joint]; rfl)

local notation "X"=> P.Spectrum0 j
open Spectral MeasureTheory.Measure
-- use Borel: topology second countable via alignment. use letI in measure proofs so no universe conflicts
noncomputable instance : MeasurableSpace (P.Spectrum0 j) := borel _
instance : BorelSpace (P.Spectrum0 j) := ⟨rfl⟩
lemma metricX (R : P.Register) : MetrizableSpace (P.Spectrum0 j) := by
  haveI : SeparableSpace (W):= P.component_space_sep j R
  exact OS.Ground.tiny _ (denseRange_denseSeq W)
noncomputable def farRep : Rep.CC (P.Spectrum0 j) →⋆ₐ[ℂ] (P.groundHil j).Op :=
  (P.compressionAlgebra j).subtype.comp ((gelfandStarTransform W).symm : _→⋆ₐ[ℂ] _)
lemma fromFar (x : W) : P.farRep j (gelfandStarTransform W x)=x.val:= congrArg (fun x' : W=> x'.val) ((gelfandStarTransform W).symm_apply_apply _)
-- Actual measure component. topology as supplied by character space, `metricX` ensures Borel etc with registered continuous tests
noncomputable def pillars : Measure (P.Spectrum0 j) := Rep.sees («H»:=P.groundHil j) (P.farRep j) (P.groundZero j)
local notation "μ"=> P.pillars j
instance : IsFiniteMeasure (P.pillars j):= by unfold pillars; infer_instance
instance normalization : IsProbabilityMeasure (P.pillars j):=by
  apply isProbabilityMeasure_iff_real.mpr; unfold pillars; rw [Rep.size]; rw [P.ground_norm,one_pow]
lemma recovery (x: W) : (∫ a, P.chi j a x ∂ (P.pillars j))=inner ℂ (P.groundZero j) (x.val (P.groundZero j)):= by
  have h:= Rep.pairings («H»:=P.groundHil j) (P.farRep j) (P.groundZero j) (gelfandStarTransform W x)
  rw [P.fromFar] at h; exact h
lemma pillar_support (Q : P.Register) : (P.pillars j).IsOpenPosMeasure:= by
  haveI : MetrizableSpace X:= P.metricX j Q; letI := metrizableSpaceMetric X
  apply OS.Ground.supports
  intro x hx; obtain ⟨i,rfl⟩:= (gelfandStarTransform W).surjective x; change P.farRep j (gelfandStarTransform W i) ω=0 at hx; rw [P.fromFar] at hx; change gelfandStarTransform W i=0; rw [P.separating j i hx,map_zero]

variable (k : Axis)
local notation "Φ" a:max => P.portion k (P.otherSpectrum j k a)
local notation "ζ"=> P.groundZero k
local notation "Ωk"=> P.floorVec k
local notation "Jk"=> P.jointTest k
lemma axis_portion_cont (x:P.Slabs k) : Continuous (fun a=> P.portion k (P.otherSpectrum j k a) x) :=
  (P.portion_cont k x).comp (P.otherSpectrum j k).continuous
lemma recovery_all (x:P.Ensemble k) : (∫ a, P.chi k (P.otherSpectrum j k a) x ∂ (P.pillars j))=inner ℂ (P.groundZero k) (x.val (P.groundZero k)):=by
  simp_rw [P.translates]; rw [recovery]; exact P.invariant_integrator k j _
lemma grants (x:P.Slabs k) : (∫ a, P.portion k (P.otherSpectrum j k a) x ∂ (P.pillars j))=inner ℂ (P.floorVec k) (x.val (P.floorVec k)):=by
  simp_rw [portion_val]; rw [recovery_all]; exact P.see_shadow k x
lemma grants2 (x:P.Slabs k) : (∫ a, ‖P.portion k (P.otherSpectrum j k a) x‖^2 ∂ (P.pillars j))= ‖P.piZero k (x.val (P.floorVec k))‖^2:=by
  -- apply commutativity; not monotone in anything!
  let b:= P.shadow k x
  have hs(v):star (P.chi k v b)*(P.chi k v b)= ↑(‖P.chi k v b‖^2 :ℝ):=by
    rw [Complex.sq_norm,← Complex.mul_conj (P.chi k v b)]; rw [mul_comm]; rfl
  have h:= P.recovery_all j k (star b*b); simp_rw [map_mul,map_star,hs] at h
  have he:inner ℂ (ζ) ((star b*b).val ζ) = inner ℂ (b.val ζ) (b.val ζ):= ContinuousLinearMap.adjoint_inner_right b.val ζ (b.val ζ)
  rw [he,inner_self_eq_norm_sq_to_K,integral_complex_ofReal] at h
  change _=((‖b.val ζ‖^2:ℝ))
  apply Complex.ofReal_injective; push_cast; exact h
lemma grains (x:P.Slabs k) (n : ℕ) :
    (∫ a, grain (P.portion k (P.otherSpectrum j k a)) (P.jointTest k) n x ∂ (P.pillars j))=
      ‖(sweep (P.jointTest k) n).val (x.val Ωk)‖^2:=by
  unfold grain; let b:= sweep Jk n*x
  change (∫ a, RCLike.re ((Φ a) (star b*b)) ∂ P.pillars j)=_
  rw [integral_re ((P.axis_portion_cont j k (star b*b)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),P.grants];
  have he: inner ℂ (Ωk) ((star b*b).val Ωk)=inner ℂ (b.val Ωk) (b.val Ωk):= ContinuousLinearMap.adjoint_inner_right b.val _ _
  rw [he]; exact (@inner_self_eq_norm_sq ℂ _ _ _ _ (b.val Ωk))
lemma saturation (x:P.Slabs k) : ∀ᵐ a ∂ (P.pillars j), jointResidual
    (P.portion k (P.otherSpectrum j k a)) (P.jointTest k) x=‖(P.portion k (P.otherSpectrum j k a)) x‖^2:=by
  let f (a:X):= Φ a
  let G (a:X):= jointResidual (f a) Jk x; let F (n:ℕ) (a:X):=grain (f a) Jk n x; let D(a:X):=‖f a x‖^2
  have h₁ (a:X): f a 1=1:= P.portion_unit ..; have h₂: ‖Jk‖≤1:= P.testing_norm k
  have h' (a:X): (f a Jk).re=1:= by unfold f; rw [P.portion_joint]; rfl
  have h (n:ℕ): Continuous (F n) := Complex.continuous_re.comp (P.axis_portion_cont j k _)
  have he n t: ‖F n t‖ ≤ ‖x‖^2:= by
    obtain ⟨p,v⟩:= root_below (f t) (h₁ t) Jk h₂ x n; rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤F n t from p)]; exact v
  have hm n: AEStronglyMeasurable (F n) μ := (h n).aestronglyMeasurable
  have ht a: Tendsto (fun n=>F n a) atTop (𝓝 (G a)):= grain_limit (f a) Jk h₂ x
  have hg:Integrable G μ:= (integrable_const («μ»:=P.pillars j) (‖x‖^2)).mono' (aestronglyMeasurable_of_tendsto_ae _ hm (Eventually.of_forall ht))
    (Eventually.of_forall (fun t=> le_of_tendsto (ht t|>.norm) (Eventually.of_forall (fun i=>he i t))))
  have hv:Tendsto (fun n=>∫ a, F n a ∂ (P.pillars j)) atTop (𝓝 (∫ a,G a ∂ (P.pillars j))):=
    tendsto_integral_of_dominated_convergence _ hm (integrable_const (‖x‖^2)) (fun n=> Eventually.of_forall (he n)) (Eventually.of_forall ht)
  have hy:Tendsto (fun n=>∫ a, F n a ∂ (P.pillars j)) atTop (𝓝 (∫ a,D a ∂ (P.pillars j))):=by
    unfold F D f; simp_rw [P.grants2,P.grains]; exact ((P.joint_limit k (x.val Ωk)).norm.pow 2)
  have hs : D =ᵐ[P.pillars j] G := (integral_eq_iff_of_ae_le
    ((Continuous.pow (P.axis_portion_cont j k x|>.norm) 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hg
    (Eventually.of_forall (fun a=> residual_above (f a) (h₁ a) Jk h₂ (h' a) x))).mp (tendsto_nhds_unique hy hv)
  exact hs.symm

/-- Test saturation on the whole C⋆-algebra. -/
def lodestarHere (v : P.Spectrum0 j) : Prop:= ∀ x, jointResidual (P.portion j v) (P.jointTest j) x= ‖P.portion j v x‖^2
def lodestar (v:P.Spectrum0 j) : Prop:= ∀ k : Axis, P.lodestarHere k (P.otherSpectrum j k v)
lemma many_stars (R : P.Register) : ∀ᵐ x ∂(P.pillars j), P.lodestar j x:= by
  apply ae_all_iff.mpr; intro i; haveI := P.slabs_separable i R
  let f:=denseSeq (P.Slabs i)
  filter_upwards [ae_all_iff.mpr (fun n=> P.saturation j i (f n))] with x hx
  let S:= P.otherSpectrum j i x; let Y₀:= P.portion i S; let F:=(jointResidual Y₀ (P.jointTest i))
  apply congrFun (show F=(fun a=>‖Y₀ a‖^2) from (denseRange_denseSeq _).equalizer
    (residual_cont ..) ((map_continuous (P.portion i S)).norm.pow 2) (funext hx))
lemma approved_exists (R : P.Register) {O : Set (P.Spectrum0 j)} (p : IsOpen O) (h : O.Nonempty) : ∃ x∈ O, P.lodestar j x :=by
  haveI:=P.pillar_support j R
  exact exists_mem_of_measure_ne_zero_of_ae (p.measure_ne_zero _ h) (ae_mono (Measure.restrict_le_self) (P.many_stars j R))
-- Note: even on the original axis, formulate selection at `otherSpectrum`; no mathematical loss at the tests
lemma extremal_here {t : P.Spectrum0 j}(e:P.lodestarHere j t) : pure0 (P.portion j t) :=
  root_pure _ (P.portion_unit j t) _ (P.testing_norm j) (by rw [P.portion_joint]; rfl) e
lemma rank_here {t : P.Spectrum0 j}(e:P.lodestarHere j t): rooted (P.portion j t) (P.jointTest j)=Submodule.span ℂ {origin (P.portion j t)}:=
  root_rank _ (P.portion_unit j t) _ (P.testing_norm j) (by rw [P.portion_joint]; rfl) e
end select
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.grants2
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.positive_
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.many_stars
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pillar_support
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.extremal_here
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.rank_here
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.joint_ext
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.joint_is
