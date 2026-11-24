import YM.Sextet.Scent
/-!
# Geometry intertwinement of single-height smear tickets

OS opposition and grid displacement at real center weights and native resolution readings.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
section RealSmears
open scoped ContDiff
variable (j:Axis) (d c:ℝ) (p:Vantage) (f:Vantage→ℝ)

lemma turnΩ {α:Type*}[AddCommGroup α] : Involutive (@mirrorΩ j α _) := by
  intro x; funext i; by_cases h:i=j <;> simp [mirrorΩ,h]

lemma turnΩ_smooth (n:ℕ∞ω): ContDiff ℝ n (mirrorΩ j : Vantage→Vantage) := by
  apply contDiff_pi.mpr
  intro i; unfold mirrorΩ; by_cases h:i=j
  · simp_rw [if_pos h]; exact (contDiff_apply ..).neg
  simp_rw [if_neg h]; exact contDiff_apply ..

lemma turnΩ_volume : MeasurePreserving (mirrorΩ j : Vantage→Vantage) volume volume := by
  let u:=fun i:Axis=> if i=j then Neg.neg else (id:ℝ→ℝ)
  have a : (mirrorΩ j : Vantage→Vantage)=fun y i=>u i (y i) := by
    funext x i; by_cases h:i=j <;> simp [mirrorΩ,h,u]
  rw [a]
  refine measurePreserving_pi (fun _=>volume) (fun _=>volume) (fun i=>?_)
  unfold u; by_cases h:i=j
  · rw [if_pos h]; exact Measure.measurePreserving_neg _
  rw [if_neg h]; exact MeasurePreserving.id _

lemma turnΩ_embed : MeasurableEmbedding (mirrorΩ j : Vantage→Vantage) := by
  have t := (turnΩ_volume j).measurable
  exact MeasurableEmbedding.of_measurable_inverse t (by
    rw [((turnΩ j).surjective).range_eq]; exact MeasurableSet.univ) t (turnΩ j)

lemma turnΩ_integral {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u:Vantage→ E) : (∫ y, u (mirrorΩ j y))=∫ y, u y :=
  (turnΩ_volume j).integral_comp (turnΩ_embed j) _

/-- Transport a real-valued weight for reflected question at plane 0.
First pose in a general cross reading is instead given its weight on *arrived*
centers. `turnSmear` builds that weight when starting with e.g. a
strict-positive-time test at axis 3 for the first body *before* reflecting it. -/
def turnSmear : Vantage→ℝ := f ∘ mirrorΩ j

lemma turn_twice : turnSmear j (turnSmear j f)=f :=
  funext fun _=>congrArg f ((turnΩ j) _)

lemma turn_support : tsupport (turnSmear j f)=(mirrorΩ j) '' tsupport f := by
  have p (g:Vantage→ℝ) : tsupport (turnSmear j g) ⊆ (mirrorΩ j) ⁻¹' tsupport g :=
    tsupport_comp_subset_preimage _ (turnΩ_smooth j ∞).continuous
  exact le_antisymm (fun y v=>⟨_,p _ v,turnΩ j y⟩) (by
    rintro _ ⟨y,h,rfl⟩; exact p _ ((turn_twice j f).symm ▸ h))

lemma turn_compact (h:HasCompactSupport f) : HasCompactSupport (turnSmear j f) :=
  by rw [HasCompactSupport,turn_support]; exact IsCompact.image h (turnΩ_smooth j ∞).continuous

lemma turn_cont (h:Continuous f) : Continuous (turnSmear j f) :=
  h.comp (turnΩ_smooth j ∞).continuous

lemma turn_smooth {n:ℕ∞ω} (h:ContDiff ℝ n f) : ContDiff ℝ n (turnSmear j f) :=
  h.comp (turnΩ_smooth j n)

lemma turn_integral : (∫ y, turnSmear j f y)=∫ y, f y :=turnΩ_integral ..

lemma turn_before_iff : BeforeWall j d (-c) (turnSmear j f) ↔ AfterWall j d c f := by
  unfold BeforeWall AfterWall; rw [turn_support]
  constructor
  · intro h y v
    have u:=h _ (Set.mem_image_of_mem _ v)
    simp only [mirrorΩ, ↓reduceIte] at u; linarith
  rintro h _ ⟨y,u,rfl⟩
  simp only [mirrorΩ, ↓reduceIte]; linarith [h _ u]

lemma turn_after_iff : AfterWall j d (-c) (turnSmear j f) ↔ BeforeWall j d c f := by
  rw [← turn_before_iff, turn_twice,neg_neg]

lemma turn_past (h:AfterWall j d 0 f) : BeforeWall j d 0 (turnSmear j f) := by
  simpa using (turn_before_iff j d 0 f).mpr h

/-- Common translation convention (move placement by `p`). -/
def shiftSmear : Vantage→ℝ := f ∘ (·-p)

lemma shift_back : shiftSmear (-p) (shiftSmear p f)=f := by
  funext y; exact congrArg f (by change y - -p - p=y; rw [sub_neg_eq_add,add_sub_cancel_right])

lemma shift_support : tsupport (shiftSmear p f)=(·+p) '' tsupport f := by
  have a (v:Vantage) (g:Vantage→ℝ) : tsupport (shiftSmear v g) ⊆ (·-v) ⁻¹' tsupport g :=
    tsupport_comp_subset_preimage _ (by fun_prop)
  exact le_antisymm (fun y h=>⟨_,a _ _ h,sub_add_cancel _ _⟩) (by
    rintro _ ⟨y,h,rfl⟩; change y+p∈_; rw [← sub_neg_eq_add]; exact a _ _ ((shift_back p f).symm ▸ h))

lemma shift_compact (h:HasCompactSupport f) : HasCompactSupport (shiftSmear p f) :=
  by rw [HasCompactSupport,shift_support]; exact IsCompact.image h (continuous_id.add continuous_const)

lemma shift_cont (h:Continuous f) : Continuous (shiftSmear p f) :=
  h.comp (continuous_id.sub continuous_const)

lemma shift_smooth {n:ℕ∞ω} (h:ContDiff ℝ n f) : ContDiff ℝ n (shiftSmear p f) :=
  h.comp (by fun_prop)

lemma shift_integral : (∫ y, shiftSmear p f y)=∫ y, f y := integral_sub_right_eq_self ..

lemma shift_before_iff : BeforeWall j d (c+p j) (shiftSmear p f) ↔ BeforeWall j d c f := by
  unfold BeforeWall; rw [shift_support]
  constructor
  · intro h y v
    have u:=h _ (Set.mem_image_of_mem (·+p) v)
    rw [Pi.add_apply] at u; linarith
  rintro h _ ⟨y,u,rfl⟩
  change y j+p j+_< _; linarith [h _ u]

lemma shift_after_iff : AfterWall j d (c+p j) (shiftSmear p f) ↔ AfterWall j d c f := by
  unfold AfterWall; rw [shift_support]
  constructor
  · intro h y v
    have u:=h _ (Set.mem_image_of_mem (·+p) v)
    rw [Pi.add_apply] at u; linarith
  rintro h _ ⟨y,u,rfl⟩
  change _< y j+p j-_; linarith [h _ u]
end RealSmears

section Poses
variable (P:Spine) (A:P.Apron) (j:Axis) (t:ℕ) (f:Vantage→ℝ)

lemma oppose_foot (y:Vantage) : P.footBill (A.kiss P j) (mirrorΩ j y)=
    (mirrorΩ j) '' P.footBill A y := by
  have p (z:Vantage) : mirrorΩ j z∈P.footBill (A.kiss P j) (mirrorΩ j y) ↔ z∈P.footBill A y := by
    refine forall_congr' fun i=>?_ ; unfold mirrorΩ
    by_cases h:i=j
    · subst i; rw [if_pos rfl,if_pos rfl,show -z j - -y j= -(z j-y j) by ring,abs_neg]
      rfl
    rw [if_neg h,if_neg h]; rfl
  exact le_antisymm (fun z k=>⟨_,(p _).mp (by rw [turnΩ j z]; exact k),turnΩ j z⟩)
    (by rintro _ ⟨z,h,rfl⟩; exact (p _).mpr h)

lemma oppose_layer : P.poseLayer (A.kiss P j) (turnSmear j f)=(mirrorΩ j) '' P.poseLayer A f := by
  unfold poseLayer; rw [turn_support]
  ext z
  constructor
  · rintro ⟨_,⟨y,h,rfl⟩,v⟩
    obtain ⟨x,g,e⟩:=(P.oppose_foot A j y) ▸ v
    exact ⟨_,⟨y,h,g⟩,e⟩
  rintro ⟨x,⟨y,h,v⟩,rfl⟩
  exact ⟨_,Set.mem_image_of_mem _ h,(P.oppose_foot A j y).symm ▸ Set.mem_image_of_mem (mirrorΩ j) v⟩

theorem oppose_paint (h:HasCompactSupport f) :
    P.reflectTest j (P.paintMark A t f)=P.paintMark (A.kiss P j) t (turnSmear j f) := by
  unfold paintMark
  rw [LinearMap.map_smulₛₗ,Complex.conj_ofReal,map_finsum _ (P.fine_finite t h _)]
  refine congrArg (((P.macroTick t^4:ℝ):ℂ) • ·) <|
     finsum_eq_of_bijective _ (turnΩ j).bijective (fun q=>?_)
  rw [LinearMap.map_smulₛₗ,Complex.conj_ofReal,P.oppose_aim,P.oppose_grid]
  unfold turnSmear; rw [Function.comp_apply,turnΩ j _]

/-- Exact OS rule on these tickets; `corePlane` uses marks 0 on all heights. -/
theorem oppose_poly (h:HasCompactSupport f) :
    P.corePlane.oppose P.par j P.calibration (P.paintPoly A t f)=
      P.paintPoly (A.kiss P j) t (turnSmear j f) :=
  (P.star_pin ..).trans (congrArg (Altitude.pinhole _ _) (P.oppose_paint A j t f h))

lemma shift_foot (y u:Vantage) : P.footBill A (y+u)=(·+u) '' P.footBill A y := by
  have p (z:Vantage) : z+u∈P.footBill A (y+u) ↔ z∈P.footBill A y := by
    simp [footBill]
  exact le_antisymm (fun z k=>⟨_,(p (z-u)).mp (by rw [sub_add_cancel]; exact k), sub_add_cancel _ _⟩)
    (by rintro _ ⟨z,h,rfl⟩; exact (p _).mpr h)

lemma shift_layer (u:Vantage) : P.poseLayer A (shiftSmear u f)=(·+u) '' P.poseLayer A f := by
  unfold poseLayer; rw [shift_support]
  ext z
  constructor
  · rintro ⟨_,⟨y,h,rfl⟩,v⟩
    replace v : z∈P.footBill A (y+u) := v
    obtain ⟨x,g,e⟩:=(P.shift_foot A y u) ▸ v
    exact ⟨_,⟨y,h,g⟩,e⟩
  rintro ⟨x,⟨y,h,v⟩,rfl⟩
  exact ⟨y+u,Set.mem_image_of_mem (·+u) h,(P.shift_foot A y u).symm ▸ Set.mem_image_of_mem (·+u) v⟩

lemma grid_add (p q:Cover) : P.grid t (p+q)=P.grid t p + P.grid t q := by
  funext i; simp [_root_.mul_add,grid_eq]

/-- Any physical common displacement that is implemented exactly (at this `t`). -/
theorem shift_paint (p:Cover) (h:HasCompactSupport f) :
    P.chartAll p (P.paintMark A t f)=P.paintMark A t (shiftSmear (P.grid t p) f) := by
  unfold paintMark
  rw [map_smul,map_finsum _ (P.fine_finite t h _)]
  refine congrArg (((P.macroTick t^4:ℝ):ℂ) • ·) <|
    finsum_eq_of_bijective (p+·) (Equiv.addLeft p).bijective (fun q=>?_)
  unfold shiftSmear aimMark
  simp only [map_smul,Function.comp_apply]
  rw [P.grid_add,add_sub_cancel_left,P.chart_ids]

/-- Use `ordinate` list for applying one grid translation on all coordinates; use
`2*p` where `p` is in *our* full ticks since `P.fullWalk` uses half that displacement.
Polynomial transport here used only on single-height ingredients/products there. -/
def walkList (p:Cover) : List Axis → P.Effect ≃ₐ[ℂ] P.Effect
  | []=>.refl
  | i::L=>(walkList p L).trans (P.fullWalk i t (2*p i))

lemma walkList_pinhole (p:Cover) (L:List Axis) (F:P.Test) :
    P.walkList t p L (Altitude.pinhole _ t F)=
      Altitude.pinhole _ t (P.cruise L p F) := by
  induction L with
  | nil=>rfl
  | cons i L b=>
    rw [walkList,AlgEquiv.trans_apply,b,P.walk_pin _ _ _ (le_refl t),
        show smill P.par t t (2*p i)=2*p i by simp [smill],P.cruise_step]
    rfl

lemma shift_poly (p:Cover) (h:HasCompactSupport f) :
    P.walkList t p ordinate (P.paintPoly A t f)=P.paintPoly A t (shiftSmear (P.grid t p) f) :=
  (P.walkList_pinhole ..).trans (congrArg (Altitude.pinhole _ _) (P.shift_paint A t f p h))
end Poses
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
