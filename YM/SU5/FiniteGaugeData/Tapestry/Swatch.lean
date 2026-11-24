import YM.SU5.FiniteGaugeData.Marked.Variation.Hearth
import Mathlib.Analysis.Normed.Lp.lpSpace
/-!
# A Banach coordinate system for the FiniteGaugeData supported even marked tests

These are **not** almost-everywhere classes. We want to put the advanced physical
readers in the very same spaces, in particular even when the output-link laws
may change along the periods. Support and norm always refer to a single level's
mesh.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

abbrev PairBounded := ↥(lp (fun _ : PairsC => ℂ) ∞)

lemma pairLe (c : PairBounded) (x : PairsC) : ‖c x‖ ≤ ‖c‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero c x

variable (S : Finset Cover)
protected def pigments : Submodule ℂ PairBounded where
  carrier := {f| Measurable (show PairsC → ℂ from ⇑f) ∧ ∀ x y : PairsC, Agrees S x.1 y.1 → Agrees S x.2 y.2 → f x=f y}
  zero_mem' := ⟨(show Measurable (fun _ : PairsC => (0:ℂ)) from measurable_const),fun _ _ _ _=>rfl⟩
  add_mem' {f g} a b := ⟨(show Measurable (fun x=>f x+g x) from a.1.add b.1),fun _ _ p q=> congrArg₂ (· + ·) (a.2 _ _ p q) (b.2 _ _ p q)⟩
  smul_mem' c f a := ⟨(show Measurable (fun x=>c*f x) from a.1.const_mul c),fun _ _ p q=>congrArg (c * ·) (a.2 _ _ p q)⟩

abbrev Pigment := ↥(Tapestry.pigments S)

theorem pigments_closed : IsClosed (Tapestry.pigments S:Set PairBounded) := by
  apply IsSeqClosed.isClosed
  intro f g hf e
  have hlim (x : PairsC) : Tendsto (fun i=> f i x) atTop (𝓝 (g x)) := (lp.lipschitzWith_one_eval ∞ x).continuous.continuousAt.tendsto.comp e
  have p (i) : Measurable (⇑(f i)) ∧ _ := (hf i : f i∈{f:PairBounded| _})
  exact ⟨measurable_of_tendsto_metrizable (fun i=> (p i).1) (tendsto_pi_nhds.mpr hlim), fun x y q t=> tendsto_nhds_unique_of_eventuallyEq (hlim x) (hlim y) (Eventually.of_forall fun i=> (p i).2 x y q t)⟩

instance : CompleteSpace (Pigment S) := (pigments_closed S).completeSpace_coe

def daub (f : Pigment S) : PairsC → ℂ := ⇑(show PairBounded from f.val)
lemma authentic (f : Pigment S) : Coeff true S (daub S f) := by
  have h : Measurable (daub S f) ∧ ∀ x y, Agrees S x.1 y.1 → Agrees S x.2 y.2 → daub S f x=daub S f y:= f.property
  exact ⟨fun _=>by contradiction,⟨h.1,‖f.val‖,pairLe f.val⟩,h.2⟩

def pigment {g:PairsC→ℂ} (h:Coeff true S g) : Pigment S := by
  have he : Memℓp g ∞ := by
    obtain ⟨C,hb⟩:= h.env.cost
    apply memℓp_infty; refine ⟨C,?_⟩; rintro x ⟨z,rfl⟩; exact hb z
  exact ⟨(show PairBounded from ⟨g,he⟩),h.env.meas,h.locus⟩
@[simp] lemma daub_pigment {g:PairsC→ℂ} (p:Coeff true S g) : daub S (pigment S p)=g := rfl

def daubL : Pigment S →ₗ[ℂ] (PairsC → ℂ) where
  toFun := daub S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma daub_inj : Injective (daub S) := fun _ _ h=> Subtype.ext (lp.ext h)
lemma daubLe (f : Pigment S) (x) : ‖daub S f x‖ ≤ ‖f‖ := pairLe f.val x
lemma pigmentLe (f : Pigment S) {C:ℝ} (c:0≤C)(h:∀ x,‖daub S f x‖ ≤ C) : ‖f‖ ≤ C:=lp.norm_le_of_forall_le (f:=f.val) c h

abbrev Swatch := (Satin.Evens S) → Pigment S
variable (K : Calibration)

def render : Swatch S →ₗ[ℂ] Family K where
  toFun f:= ∑ x:Evens S, note K (daub S (f x)) (tagWord S x.val)
  map_add' f g:= by
    simp_rw [Pi.add_apply,show ∀ f g,daub S (f+g)=daub S f+daub S g from fun _ _=>rfl, note_plus,sum_add_distrib]
  map_smul' z f:= by
    change _ = z • ∑ x:Evens S,note K (daub S (f x)) (tagWord S x.val)
    rw [Finset.smul_sum]; refine sum_congr rfl fun x _=>?_ ; funext m u; simp only [Pi.smul_apply,note_v]; change (z * _) • _= _; rw [mul_smul]; rfl

lemma render_eq (f:Swatch S): render S K f=∑ x:Evens S, note K (daub S (f x)) (tagWord S x.val) := rfl
lemma texture (f:Swatch S): InTest K true S false (render S K f):= by
  rw [render_eq]; refine InTest.sum univ _ fun i _=>?_ ; exact (by simpa only [i.property] using note_t K _ (authentic S (f i)) (brand S i.val))
lemma rendered {F:Family K} (h:InTest K true S false F) : ∃ f:Swatch S, render S K f=F:=by
  obtain ⟨a,t⟩:= circulation S K h
  exact ⟨fun i=>pigment S (a i).property, t.symm⟩

def fabric {F:Family K} (h:InTest K true S false F) : Swatch S := (rendered S K h).choose
lemma render_fabric {F:Family K} (h:InTest K true S false F) : render S K (fabric S K h) = F := (rendered S K h).choose_spec

def appear (m:Side) : Swatch S →ₗ[ℂ] Mark (K.c m):=(LinearMap.proj m).comp (render S K)
lemma appearRender (m:Side)(f:Swatch S) : render S K f m=appear S K m f:=rfl
lemma appearSupport (m:Side)(f:Swatch S) : AtSupport false (region S (K.c m)) (appear S K m f) := (texture S K f).support _
lemma appearSpool (m:Side)(f:Swatch S) (x:Fields (K.c m)) :
    appear S K m f x=∑ i:Evens S, daub S (f i) (Prod.map (onC _) (onC _) x) • spool (K.c m) (tagWord S i.val) := by
  rw [←appearRender,render_eq]; simp_rw [Finset.sum_apply,note_v,spool_sing]

abbrev spread (S : Finset Cover) : ℝ := Fintype.card (Satin.Evens S)
lemma swatchLe (f:Swatch S) {C:ℝ} (c:0≤C)(h:∀ i x, ‖daub S (f i) x‖ ≤ C) : ‖f‖ ≤ C:= (pi_norm_le_iff_of_nonneg c).2 fun i=> pigmentLe S (f i) c (h i)
lemma appearLe (m:Side)(f:Swatch S)(x:Fields (K.c m)) : ‖appear S K m f x‖ ≤ spread S * ‖f‖ := by
  rw [←appearRender,render_eq]; simp_rw [Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>‖f‖) ?_).trans_eq ?_)
  · exact fun i _=> (pitched K _ _ m x).trans ((daubLe S (f i) _).trans (norm_le_pi_norm ..))
  rw [sum_const,nsmul_eq_mul,card_univ]
lemma renderLe (m:Side)(f:Swatch S)(x:Fields (K.c m)) : ‖render S K f m x‖ ≤ spread S * ‖f‖ := appearLe ..

lemma sampling (m:Side) (p:Hosp S (K.c m)) (f:Swatch S) {C:ℝ} (h:∀ x, ‖appear S K m f x‖ ≤ C) : ‖f‖ ≤ C:= swatchLe S f ((norm_nonneg _).trans (h (1,1))) (ruby S K (render S K f) (fun i=>⟨_,authentic S (f i)⟩) rfl p C h)
lemma appear_inj (m:Side)(p:Hosp S (K.c m)) : Injective (appear S K m) := by
  intro f g h; apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  apply sampling S K m p; rw [map_sub,h,sub_self]; simp
lemma render_inj : Injective (render S K) := by
  obtain ⟨m,p⟩:= (separates K S).exists
  exact fun _ _ h=> appear_inj S K m ⟨p⟩ (congr_fun h m)
lemma fabric_render (f:Swatch S) (h : InTest K true S false (render S K f) := texture S K f) : fabric S K h=f:=render_inj S K (render_fabric ..)
end YM.CF.Buffered.Afterglow.Tapestry
