import YM.SU5.FiniteGaugeData.Marked.Variation.Hearth
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Local normed space in the Afterglow FiniteGaugeData election

A slightly different (equivalent) norm convention from Crimson, on the **same actual F**.
S is a finite set of gauge sites on the cover, at the GIVEN observing resolution; stencils
mean the even chiral (no colour-invariance restriction yet), two-link, bounded Borel
operator marks with that support. We deliberately keep the points, not L^∞ equivalence.
Define the precise local Banach spaces. Recover the native operator bound in either direction,
including on the whole family, and equality of these F's even by evaluating at *one* roomy period.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra

variable (S : Finset Cover) (K : Calibration)

/-- Use a norm with pointwise, not a.e., comparison. -/
abbrev Tiles := WithDiscreteTopology PairsC

abbrev tile : PairsC ≃ Tiles := (WithTopology.equiv PairsC ⊥).symm

abbrev Ink := BoundedContinuousFunction Tiles ℂ

def swatches : Submodule ℂ Ink where
  carrier := {f | Coeff true S (fun x => f (tile x))}
  add_mem' := by
    intro A B (a : Coeff _ _ _) (b : Coeff _ _ _)
    refine ⟨fun _=>by contradiction, Girt.kitE _ _ (fun (i j : ℂ)=> i+j) (by fun_prop) a.env b.env,?_⟩
    exact fun _ _ p q=> congrArg₂ (fun (i j:ℂ)=>i+j) (a.locus _ _ p q) (b.locus _ _ p q)
  zero_mem' := ⟨fun _ => by contradiction, Girt.rite_c _,fun _ _ _ _=>rfl⟩
  smul_mem' := fun c A (h : Coeff _ _ _) => show _ from (hue S ⟨_,h⟩ c).property

@[simp] lemma swatches_mem (f : Ink) : f ∈ swatches S ↔ Coeff true S (fun x=> f (tile x)) := Iff.rfl

theorem swatches_closed : IsClosed (swatches S : Set Ink) := by
  apply IsSeqClosed.isClosed
  intro u x (a : ∀ i : ℕ, _ ∈ _) h
  change ∀ i, Coeff true S (fun y => (u i) (tile y)) at a
  change Coeff true S (fun y => x (tile y))
  have he (y : PairsC) : Tendsto (fun i => u i (tile y)) atTop (𝓝 (x (tile y))) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h).tendsto_at _
  refine ⟨fun _=>by contradiction,
    ⟨measurable_of_tendsto_metrizable (fun i => (a i).env.meas) (tendsto_pi_nhds.mpr he),
      ‖x‖, fun y=> BoundedContinuousFunction.norm_coe_le_norm x _⟩,?_⟩
  exact fun y z p q => tendsto_nhds_unique (he y) ((he z).congr'
    (Eventually.of_forall fun i=> ((a i).locus _ _ p q).symm))

instance : CompleteSpace (swatches S) := (swatches_closed S).completeSpace_coe

abbrev tint (f : swatches S) (x : PairsC) : ℂ := f.val (tile x)

lemma tint_add (f g : swatches S) : tint S (f + g) = tint S f + tint S g := rfl
lemma tint_sub (f g : swatches S) : tint S (f - g) = tint S f - tint S g := rfl
lemma tint_scale (f : swatches S) (c : ℂ) : tint S (c • f)= c • tint S f := rfl

def toPurse (f : swatches S) : Purse S := ⟨_, show Coeff true S (tint S f) from f.property⟩

lemma swatches_norm_le {f : swatches S} {r : ℝ} (p : 0 ≤ r) :
    ‖f‖ ≤ r ↔ ∀ x, ‖tint S f x‖ ≤ r := by
  rw [show ‖f‖ = ‖f.val‖ from rfl, BoundedContinuousFunction.norm_le p]
  exact tile.surjective.forall

lemma tint_bound (f : swatches S) (x : PairsC) : ‖tint S f x‖ ≤ ‖f‖ :=
  (swatches_norm_le S (norm_nonneg _)).mp le_rfl x

private lemma tint_inj : Injective (tint S) := fun _ _ v => Subtype.ext <|
  BoundedContinuousFunction.ext (tile.surjective.forall.mpr (congrFun v))

def ofPurse (p : Purse S) : swatches S := by
  let h := p.property.env.cost
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun x : Tiles=> p.val (tile.symm x))
    continuous_of_discreteTopology h.choose (fun x=> h.choose_spec _),?_⟩
  apply (swatches_mem ..).2; simpa using p.property

lemma tint_ofPurse (p : Purse S) : tint S (ofPurse S p) = p.val := by
  funext x
  change p.val (tile.symm (tile x))=p.val x
  rw [Equiv.symm_apply_apply]

lemma toPurse_ofPurse (p : Purse S) : toPurse S (ofPurse S p)=p := Subtype.ext (tint_ofPurse ..)
lemma ofPurse_toPurse (p : swatches S) : ofPurse S (toPurse S p)=p := tint_inj S (tint_ofPurse ..)

/-- Banach stencil representation of the whole even grammar on S. -/
abbrev Palette := Evens S → swatches S

def singleNote (u : Chorus) : swatches S →ₗ[ℂ] Buffered.Family K where
  toFun f := note K (tint S f) u
  map_add' f g := note_plus K u _ _
  map_smul' c f := by
    funext m x
    change note K _ _ _ _ = c • note K _ _ _ _
    rw [note_v, note_v, smul_smul, tint_scale, Pi.smul_apply]
    rfl

def pigment : Palette S →ₗ[ℂ] Buffered.Family K :=
  ∑ i : Evens S, (singleNote S K (tagWord S i.val)).comp (LinearMap.proj i)

lemma pigment_formula (f : Palette S) : pigment S K f =
    ∑ i : Evens S, note K (tint S (f i)) (tagWord S i.val) := by rw [pigment,LinearMap.sum_apply]; rfl

def native (n : Side) : Palette S →ₗ[ℂ] Buffered.Mark (K.c n) :=
  (LinearMap.proj n).comp (pigment S K)
lemma native_formula (n : Side) (f : Palette S) : native S K n f = pigment S K f n := rfl

lemma pigment_test (f : Palette S) : InTest K true S false (pigment S K f) := by
  rw [pigment_formula]
  refine InTest.sum _ _ (fun i _=> ?_)
  exact Eq.mp (congrArg (fun b => InTest K true S b (note K (tint S (f i)) (tagWord S i.val))) i.property) (note_t K _ (toPurse S (f i)).property (Satin.brand S i.val))

lemma encode {f : Buffered.Family K} (p : InTest K true S false f) : ∃ u : Palette S, pigment S K u=f := by
  obtain ⟨a,v⟩ := circulation S K p
  exact ⟨fun i=> ofPurse S (a i), by rw [v, pigment_formula]; simp_rw [tint_ofPurse]⟩

def count : ℝ := Fintype.card (Evens S)
lemma count_nonneg : 0 ≤ count S := by unfold count; positivity

lemma native_bound (f : Palette S) (n : Side) (x : Fields (K.c n)) : ‖native S K n f x‖ ≤ count S*‖f‖ := by
  simp_rw [native_formula,pigment_formula,Finset.sum_apply]
  exact (norm_sum_le ..).trans ((sum_le_sum (fun (i:Evens S) _ => (pitched K _ _ _ _).trans
    ((tint_bound S (f i) _).trans (norm_le_pi_norm f i)))).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul]; rfl))

lemma pigment_bound (f : Palette S) (n : Side) (x : Fields (K.c n)) : ‖pigment S K f n x‖ ≤ count S*‖f‖ :=
  native_bound ..

lemma palette_norm {f : Palette S} {n : Side} (p : Hosp S (K.c n)) {y : ℝ}
    (h : ∀ x, ‖native S K n f x‖ ≤ y) : ‖f‖ ≤ y := by
  have ht := ruby S K (pigment S K f) (fun i=>toPurse S (f i)) (pigment_formula ..) p y
    (show ∀ x, ‖pigment S K f n x‖ ≤ y from h)
  have hz : 0 ≤ y := (norm_nonneg _).trans (h (1,1))
  exact (pi_norm_le_iff_of_nonneg hz).mpr (fun i=> (swatches_norm_le S hz).mpr (ht i))

theorem native_injective {n : Side}(p : Hosp S (K.c n)) : Injective (native S K n) := by
  intro f g h
  apply sub_eq_zero.mp
  refine norm_le_zero_iff.mp (palette_norm S K p (f:=f-g) ?_)
  intro x
  rw [map_sub, h, sub_self]; exact norm_zero.le

lemma suitable : ∀ᶠ n : Side in atTop, Hosp S (K.c n) :=
  (separates K S).mono (fun _ p=> ⟨p⟩)

theorem pigment_injective : Injective (pigment S K) := by
  obtain ⟨n,p⟩ := (suitable S K).exists
  exact fun _ _ h => native_injective S K p (congrFun h n)

theorem native_ext {n : Side}(p : Hosp S (K.c n)) {f g : Buffered.Family K}
    (a : InTest K true S false f) (b : InTest K true S false g) (h : f n=g n) : f=g := by
  obtain ⟨u,rfl⟩ := encode S K a
  obtain ⟨v,rfl⟩ := encode S K b
  exact congrArg _ (native_injective S K p (a₁:=u) (a₂:=v) h)
end YM.CF.Buffered.Concord
