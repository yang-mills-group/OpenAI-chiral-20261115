import YM.SU5.Selected.Glyph
/-!
# Threshold: the OS Hilbert of a panel point with slab insertions and coherent translations.

Includes verification of cylinder products / spatial motion **in the character state** (the latter
still on the whole grid of the resolution tower, checking its definition as a representation of ALL
this grid, no continuum approximation yet). Also a density theorem -- this is the genuine
Hilbert completion of positive local marks, i.e. we did not add independent GNS generators not
obtainable from the local filtered system.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "Θu" q:max => account Y H V q Q Qt j strict C f
local notation "L" => procession Y H V Q Qt j strict C f
local notation "R₀" => joint (traveller Y H V Q Qt j strict C) (procession Y H V Q Qt j strict C f)
lemma above_door : Ω ∈ joint (traveller Y H V Q Qt j strict C) (procession Y H V Q Qt j strict C f) :=
  VacuumState.grounded (Φ) _ (travellers Y H V Q Qt j strict C) (setupState Y H V Q Qt j strict C f)
lemma firm_door (Vf : Victory Y H V Q Qt strict j C f) (x : Ρ) (h : x ∈ R₀) : ∃ z : ℂ, z • Ω=x := Vf.1 x h
lemma barn_door (Vf : Victory Y H V Q Qt strict j C f) (x : 𝔅) :
    (R₀).starProjection (Oa x) = Φ x • Ω := projects Φ _ (travellers Y H V Q Qt j strict C)
      (setupState Y H V Q Qt j strict C f) Vf.1 x

/-- bud is linear on each resolution (remember, NOT claiming a subalgebra inclusion from s to t). -/
def arriving : (Tower.Field Y H s j 0 strict) →ₗ[ℂ] indoor Y H V Q Qt j strict C f where
  toFun := bud Y H V s Q Qt j strict C f
  map_add' x y := by
    let z := a₀ s (x+y) - (a₀ s x + a₀ s y)
    have e (t : 𝔙 s) : inner ℂ (a₀ s t) z=0 := by
      unfold z; rw [inner_sub_right,inner_add_right,earns,earns,earns,
        map_add (M₁ s),mul_add, ← accounts,←accounts,←accounts,map_add,sub_self]
    apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    change inner ℂ (a₀ s (x+y) - _) z = 0; rw [inner_sub_left,inner_add_left,e,e,e]; simp
  map_smul' c x := by
    let z := a₀ s (c • x) - c • a₀ s x
    have e (t : 𝔙 s) : inner ℂ (a₀ s t) z=0 := by
      unfold z; rw [inner_sub_right, inner_smul_right,earns,earns,map_smul (M₁ s),Algebra.mul_smul_comm,
        ← accounts,←accounts,map_smul]; simp -- check direction
    apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    change inner ℂ (a₀ s (c • x) - c • a₀ s x) z=0; rw [inner_sub_left,inner_smul_left,e,e]; simp
local notation "P₁" t:max => arriving Y H V t Q Qt j strict C f
lemma arriving_eq (x : 𝔙 s) : (P₁ s) x=a₀ s x := rfl

/-- Moving to a high enough common level computes the mixed-resolution representation
on any vector from the actor set. -/
lemma slotted {w : ℕ} (x : Entry Y H s j strict w) (p : 0 < w) (y : 𝔙 s) :
    (Π (E₀ s x p)) (a₀ s y) = a₀ s (slabT Y H s j strict w x y) := by
  obtain ⟨u,q,z,yh⟩ := artist_fits_slab Y H s j strict y
  let e := edit Y H s j strict w u x z
  rw [←yh,turns Y H V s Q Qt j strict C f z q,arrive_mul,entrance_pair]
  have t : e.val=slabT Y H s j strict w x z.val :=
    Subtype.ext (by unfold e; rw [slab_eq, editor])
  rw [← t, turns Y H V s Q Qt j strict C f e (by omega : 0 < w+u)]
lemma slot_high {w : ℕ} (x : Entry Y H s j strict w) (p : 0 < w) (t : ℕ) (k : s≤t) (y : 𝔙 t) :
    (Π (E₀ s x p)) (a₀ t y) = a₀ t (slabT Y H t j strict _ (furnished Y H s Q j strict w x t k) y) := by
  rw [show E₀ s x p=E₀ t (furnished Y H s Q j strict w x t k) (Nat.mul_pos (pow_pos Λ.R.L.property _) p) from Subtype.ext (refined_box Y H V s Q Qt j strict C w x p t k), slotted]
lemma slot_time (y : 𝔙 s) (n : ℕ) :
    (Π (ψ s n)) (a₀ s y) = a₀ s (tick Y H s j 0 strict (2*n) y) := by
  rcases Nat.eq_zero_or_pos n with h|p
  · rw [h, show ψ s 0=1 from Subtype.ext (by change advance Y H V Q.circuit j 0 strict C _=_; rw [when_zero, advance_source]; rfl), map_one]
    apply congrArg (bud Y H V s Q Qt j strict C f)
    apply Subtype.ext; rw [timed_apply]; exact (relocate_zero K j (field_test Y H s j 0 strict y)).symm
  rw [← entrance_heat Y H V s Q Qt j strict C p, slotted]; apply congrArg _; apply Subtype.ext
  rw [slab_eq, timed_apply]; exact one_mul _
lemma entrance_moves {w : ℕ} (x : Entry Y H s j strict w) (p : 0 < w) (u : Trans j) (d : ℤ) :
    (Σ₁ u (notch Μ s d)) * (E₀ s x p) = (E₀ s (alongS Y H s j strict w x u d) p) * (Σ₁ u (notch Μ s d)) :=
  Subtype.ext (shape_across Y H V s Q Qt j strict C w x p u d) -- tune
lemma turns_across (u : Trans j) (d : ℤ) (x : 𝔙 s) :
    (Π (Σ₁ u (notch Μ s d))) (a₀ s x)=a₀ s (sail Y H s j 0 strict u.val u.property (2*d) x) := by
  obtain ⟨w,p,y,ht⟩ := artist_fits_slab Y H s j strict x
  let X := alongS Y H s j strict w y u d
  let U := Σ₁ u (notch Μ s d)
  rw [←ht,turns Y H V s Q Qt j strict C f y p,arrive_mul,entrance_moves,←arrive_mul,arrive_vec Y H V Q Qt j strict C f U]
  change (Π (E₀ s X p)) ((Π (Σ₁ u (notch Μ s d))) Ω)=a₀ s X.val
  rw [jamb,turns Y H V s Q Qt j strict C f X p,arrive_vec]

-- persist through Xα labels for normal_form. note if using `rcases p foc` with subst may cost.
private lemma whorl (x : (A).Op) (p : x ∈ Submonoid.closure (breezes Y H V Q j strict C)) :
    ∃ z : (driveAlgebra Y H V Q Qt j strict C), z.val=x ∧ (Π z) Ω=Ω := by
  induction p using Submonoid.closure_induction with
  | one => exact ⟨1,rfl,by rw [map_one]; rfl⟩
  | mem x p =>
    obtain ⟨u,d,h⟩ := (show x ∈ breezes Y H V Q j strict C from p) -- tune order
    exact ⟨Σ₁ u d,h.symm,jamb Y H V Q Qt j strict C f u d⟩
  | mul x y px py tx ty =>
    obtain ⟨v,hv,k⟩ := tx; obtain ⟨w,hw,e⟩ := ty
    refine ⟨v*w,congrArg₂ (·*·) hv hw,?_⟩
    rw [map_mul,ContinuousLinearMap.mul_apply,e,k]

local notation "Xα" => breezes Y H V Q j strict C
local notation "Bα" => objects Y H V Q Qt j strict C
local notation "Z" => Bα ∪ Xα
open scoped Pointwise
private lemma stroll_basis (x : (A).Op) (p : x ∈ Submonoid.closure (Z ∪ star Z)) :
    ∃ z : (driveAlgebra Y H V Q Qt j strict C), z.val=x ∧ ∃ (s : ℕ) (v : (𝔙 s)), Oa z=(P₁ s) v := by
  obtain ⟨a,b,h⟩ := normal_form Y H V Q Qt j strict C p
  obtain ⟨t,k,v⟩ := whorl Y H V Q Qt j strict C f a b
  rcases h with h | ⟨v',⟨s,w,u,q,e⟩,g⟩
  · refine ⟨t,k.trans h.symm,0,unity Y H j 0 strict 0,?_⟩
    rw [arriving_eq, root,arrive_vec,v]
  let L' := E₀ s u q
  refine ⟨L'*t, ?_,s,u.val, ?_⟩
  · exact (congrArg₂ (·*·) e.symm k).trans g.symm
  rw [arriving_eq,turns Y H V s Q Qt j strict C f u q]; change Oa (L'*t)=Oa L'; rw [arrive_vec,arrive_vec,map_mul,ContinuousLinearMap.mul_apply,v]

local notation "Rw" t:max => LinearMap.range (P₁ t)
lemma stroll_mono : Monotone (fun s : ℕ => LinearMap.range (arriving Y H V s Q Qt j strict C f)) := fun i k p _ ⟨v,t⟩ =>
  ⟨Raise Y H Q.circuit j 0 strict i k p v, (flourishes Y H V i Q Qt j strict C f k p v).trans t⟩
noncomputable def stroll := ⨆ i : ℕ, LinearMap.range (arriving Y H V i Q Qt j strict C f)
lemma stroll_exact : (stroll Y H V Q Qt j strict C f : Set (Ρ)) = ⋃ i : ℕ, range (bud Y H V i Q Qt j strict C f) := by
  rw [stroll,Submodule.coe_iSup_of_directed _ (stroll_mono Y H V Q Qt j strict C f).directed_le]; rfl

def rollin : driveAlgebra Y H V Q Qt j strict C →L[ℂ] indoor Y H V Q Qt j strict C f := by
  let W : 𝔅 →ₗ[ℂ] (Ρ) := (ContinuousLinearMap.apply ℂ (Ρ) Ω).toLinearMap.comp (L).toAlgHom.toLinearMap
  refine ⟨W,?_⟩
  change Continuous W
  rw [show (W : _ → _) = Oa from funext (fun x => (arrive_vec Y H V Q Qt j strict C f x).symm)]
  exact arrive_cont Y H V Q Qt j strict C f
lemma rollin_eq (x : 𝔅) : rollin Y H V Q Qt j strict C f x=Oa x := (arrive_vec Y H V Q Qt j strict C f x).symm

private lemma stroll_in : Set.range (arrive Y H V Q Qt j strict C f) ⊆ closure (stroll Y H V Q Qt j strict C f : Set _) := by
  let B := 𝔅; let L' := rollin Y H V Q Qt j strict C f; let V' := stroll Y H V Q Qt j strict C f; let T := V'.topologicalClosure
  let M := T.comap L'.toLinearMap; let P := M.map (𝔅).subtype.toAlgHom.toLinearMap
  have HP : IsClosed (P : Set (A).Op) := (drive_closed Y H V Q Qt j strict C).isClosedEmbedding_subtypeVal.isClosedMap _ (V'.isClosed_topologicalClosure.preimage L'.continuous)
  have HT : (StarAlgebra.adjoin ℂ Z).toSubalgebra.toSubmodule ≤ P := by
    rw [StarAlgebra.adjoin_eq_span]; apply Submodule.span_le.mpr; intro x h; obtain ⟨k,m,s,v,g⟩ := stroll_basis Y H V Q Qt j strict C f x h
    refine ⟨k,?_,m⟩; change rollin Y H V Q Qt j strict C f k ∈ T
    rw [rollin_eq,g]; exact V'.le_topologicalClosure ((le_iSup (fun i : ℕ => Rw i) s) (LinearMap.mem_range_self _ _))
  rintro _ ⟨u,rfl⟩
  have h : u.val ∈ P := closure_minimal (s:=(StarAlgebra.adjoin ℂ Z : Set (A).Op)) (fun x v => HT v) HP u.property
  obtain ⟨v,e,k⟩ := h
  have he : v=u := Subtype.ext k
  rw [←he,←rollin_eq]; exact e

theorem stroll_dense : Dense (⋃ i : ℕ, range (bud Y H V i Q Qt j strict C f)) := by
  rw [← stroll_exact]
  intro x
  exact closure_minimal (stroll_in Y H V Q Qt j strict C f) isClosed_closure (arrive_dense Y H V Q Qt j strict C f x)

/-- Therefore an actual rank test in terms of the translated and shifted mark vectors is possible. -/
lemma inner_future (x y : Ρ) (p : ∀ (u : ℕ) (z : (𝔙 u)), inner ℂ (a₀ u z) x=inner ℂ (a₀ u z) y) : x=y := by
  apply (stroll_dense Y H V Q Qt j strict C f).denseRange_val.eq_of_inner_right ℂ; intro v
  obtain ⟨u,t⟩ := Set.mem_iUnion.mp v.property
  obtain ⟨z,h⟩ := t; change inner ℂ v.val x = _; rw [←h,p]

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.stroll_dense
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.slot_high
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.inner_future
