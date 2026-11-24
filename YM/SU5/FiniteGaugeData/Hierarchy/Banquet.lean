import YM.SU5.FiniteGaugeData.Hierarchy.Dic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
/-! # Supported wide local test space in coefficient form, Banach in sup-norm of local Borel data
(no quotient by a measure at any period). -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra

abbrev DataMenu := WithTopology PairsC ⊥
abbrev RawQ := BoundedContinuousFunction DataMenu ℂ

def slit (f : RawQ) (x : PairsC) : ℂ := f (WithTopology.toTopology _ x)

variable (S : Finset Cover)

def boundedCoeffs (S : Finset Cover) : Submodule ℂ RawQ where
  carrier := {f | Coeff true S (slit f)}
  add_mem' {x y} (hx:Coeff true S _) (hy:Coeff true S _) := ⟨
      fun _=>by contradiction, Girt.kitE _ _ (fun (i j:ℂ)=>i+j) (by fun_prop) hx.env hy.env,
      fun _ _ a b=>congrArg₂ (fun (i j:ℂ)=>i+j) (hx.locus _ _ a b) (hy.locus _ _ a b)⟩
  zero_mem' := ⟨fun _=>by contradiction, Girt.rite_c _,fun _ _ _ _=>rfl⟩
  smul_mem' c {x} (p:Coeff true S _) := (Satin.hue S ⟨_,p⟩ c).property

lemma bca_mem (f : RawQ) : f ∈ boundedCoeffs S ↔ Coeff true S (slit f):= Iff.rfl
lemma slit_cc (x:PairsC): Continuous (fun f:RawQ=>slit f x):= continuous_eval_const (F:=RawQ) (WithTopology.toTopology ⊥ x)
lemma bca_closed : IsClosed (boundedCoeffs S:Set RawQ) := by
  rw [← isSeqClosed_iff_isClosed]
  intro f t p hp
  have v(n) := ((bca_mem S (f n)).mp (p n)).env.meas
  have h(x:PairsC): Tendsto (fun i=>slit (f i) x) atTop (𝓝 (slit t x)):= ((slit_cc x).tendsto t).comp hp
  refine (bca_mem S t).2 ⟨fun _=>by contradiction,
    ⟨measurable_of_tendsto_metrizable v (tendsto_pi_nhds.mpr h),‖t‖,fun x=> t.norm_coe_le_norm _⟩,?_⟩
  intro x y i j
  exact tendsto_nhds_unique_of_eventuallyEq (h x) (h y) (Eventually.of_forall fun n=> ((bca_mem S (f n)).mp (p n)).locus x y i j)

instance : CompleteSpace (boundedCoeffs S) := (bca_closed S).completeSpace_coe

abbrev BC := ↥(boundedCoeffs S)
abbrev unroll (x : BC S) : Purse S := ⟨slit x.val,x.property⟩
def stockUp {f:PairsC→ℂ}(p:Coeff true S f): BC S :=
  let x:RawQ:=BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun v:DataMenu=> f v.ofTopology) p.env.cost.choose (fun _=> p.env.cost.choose_spec _)
  ⟨x,p⟩
lemma pristine {f:PairsC→ℂ}(p:Coeff true S f) : slit (stockUp S p).val=f:=rfl
lemma slit_ext {f g:RawQ}(p:slit f=slit g) : f=g:= by ext x; exact congrFun p x.ofTopology
lemma stock_eq {f g:BC S} (h:(unroll S f).val=(unroll S g).val) : f=g:= Subtype.ext (slit_ext h)
lemma stock_n (f:BC S)(x:PairsC): ‖(unroll S f).val x‖ ≤ ‖f‖ := f.val.norm_coe_le_norm _
lemma stock_n_iff {a:ℝ}(ha:0≤a)(f:BC S): ‖f‖≤a ↔ ∀ x:PairsC, ‖(unroll S f).val x‖ ≤ a := by
  exact ⟨fun v x=> (stock_n S f x).trans v,fun v=> (BoundedContinuousFunction.norm_le ha).2 (fun x:DataMenu=> v x.ofTopology)⟩

abbrev Catalog := Key S → BC S
abbrev source (g:Catalog S) : Score S := fun a => slit (g a).val
def composeQ (K:Calibration)(S:Finset Cover) : Catalog S →ₗ[ℂ] Family K where
  toFun f:= composeLetters K S (source S f)
  map_add' f g := letters_more K S (source S f) (source S g)
  map_smul' c f := letters_scalar K S (source S f) c
variable {C:ℝ}{m N:Side}
variable (K:Calibration)
-- linear inhabited
lemma compose_t (f:Catalog S) : InTest K true S false (composeQ K S f) := letters_t K S _ fun i=>(f i).property
lemma certify (f:Family K) (p:InTest K true S false f): ∃ g:Catalog S, composeQ K S g=f:= by
  obtain ⟨a,e⟩:=circulation S K p; exact ⟨fun i=>stockUp S (a i).property,e.symm⟩
def certifyAs (f:Family K) (p:InTest K true S false f): Catalog S:=Classical.choose (certify S K f p)
lemma certified (f:Family K) (p:InTest K true S false f): composeQ K S (certifyAs S K f p) = f:= Classical.choose_spec (certify S K f p)

lemma take_source (h : Hosp S (K.c m)) (x: Catalog S) : takeScore S h ((composeQ K S x) m) = source S x := take_letters K S h _ (fun i=> (x i).2)
lemma into_catalog (h : Roomy S (K.c m)) {f:Mark (K.c m)} (p : AtSupport false (region S (K.c m)) f) : ∃ x:Catalog S,(composeQ K S x) m=f :=
  ⟨fun a=>stockUp S (take_coeff S h p a), letters_take K S _ p⟩
lemma catalog_eq (h : Hosp S (K.c m)) {x y: Catalog S} (p : (composeQ K S x) m=(composeQ K S y) m) : x=y:= by
  have hx:source S x=source S y:=by rw [←take_source S K h x,p,take_source]
  exact funext fun i=>stock_eq S (congrFun hx i)

lemma roomy_sides : ∀ᶠ m:Side in atTop, Roomy S (K.c m) := (separates K (tips S)).mono fun _ p=>⟨p⟩
lemma compose_inj : Injective (composeQ K S) := by
  obtain ⟨m,h⟩:= (roomy_sides S K).exists; exact fun f g t=> catalog_eq S K (roomy_hosp S h) (congrFun t m)

-- tag space inhabited (can be empty S)
abbrev vacuumTag : Key S:= ⟨∅,by simp [tagWord,Sound.treble]⟩
instance : Nonempty (Key S):=⟨vacuumTag S⟩ -- avoid duplication from Subtype?

def duration (S : Finset Cover):ℝ:= (Fintype.card (Key S):ℝ)
lemma duration_pos : 0< duration S := by unfold duration; positivity

lemma catalogue_norm_le (p:0≤C)(x:Catalog S) : ‖x‖≤ C ↔ ∀ a v,‖source S x a v‖ ≤ C:= by
  rw [pi_norm_le_iff_of_nonneg p]; exact forall_congr' fun a=> stock_n_iff S p (x a)
lemma price_letter (f:Catalog S) (x:Key S) (v) : ‖source S f x v‖ ≤ ‖f‖ := (catalogue_norm_le S (norm_nonneg _) _).1 le_rfl x v
lemma compose_price (f:Catalog S)(m:Side)(v:Fields (K.c m)) : ‖composeQ K S f m v‖ ≤ duration S * ‖f‖ := by
  change ‖(composeLetters K S (source S f)) m v‖ ≤ _
  rw [composeLetters]; simp_rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=> (Sound.pitched ..).trans (price_letter S f i _))).trans; simp [duration]
lemma offered_bound (x:Catalog S)(h : Hosp S (K.c m)) {w:ℝ} (p:∀ v:Fields (K.c m), ‖(composeQ K S x) m v‖ ≤ w): ‖x‖≤ w:= by
  have u:0≤w:=(norm_nonneg _).trans (p (1,1))
  apply (catalogue_norm_le S u x).2; intro a z; rw [← take_source S K h]; exact (selector_n S h a _).trans (p _)

end YM.CF.Buffered.Afterglow.Hierarchy
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.bca_closed
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.compose_inj
