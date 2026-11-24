import YM.SU5.Selected.Refinement
/-!
# Pay the hypothesized countability on the actual cap and slab system

Not just existence of countably many actor vectors at almost every *finite period*. Use the
next level on the SAME history as the interacting estimates and pay a *separable*
set of transported operators in the local topology. This indeed **lifts** all
of the choices for a fixed entry box and width already at level s. Need also show
continuity of the operator assignment on these fixed domains. We buy this by the
closed graph criterion on the ACTUAL OS H where the bounded operators have been bought by
a different estimate (StationMaster.lean), not the sup-operator norm they carry on
an individual host's finite presentation.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 350000
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
open Tapestry TopologicalSpace
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "R" => Aurora Y H V Q j strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "β" s:max f:max p:max => boxOp Y H V s Q Qt j strict C _ f p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
variable (S : Finset Cover)

def fitting : Submodule ℂ (Swatch S) := (marksAlgebra (tent Y H) strict).toSubmodule.comap (render S K)
local notation "X" => fitting Y H strict S
lemma fitsMarks (x : X) : render S K x.val ∈ marksAlgebra K strict := x.property

lemma render_cont (Z' : Calibration) (n : Side) (u : Fields (Z'.c n)) :
    Continuous (fun v : Swatch S => render S Z' v n u) :=
  let a := (LinearMap.proj («R»:=ℂ) (φ:=fun _ : Fields (Z'.c n) => FC (Single (Z'.c n))) u).comp (appear S Z' n)
  (a.mkContinuous (spread S) fun v => renderLe S Z' n v u).continuous -- tune

instance whole_fitting : CompleteSpace (X) := by
  suffices h : IsClosed (X : Set (Swatch S)) from h.completeSpace_coe
  apply IsSeqClosed.isClosed
  intro f x hf t
  refine (show render S K x ∈ marksAlgebra K strict from
    ⟨aux_test (texture S K x), fun u => ?_⟩)
  intro m g y
  have he (z : Fields ((K).c m)) : Tendsto (fun i => render S K (f i) m z) atTop
      (𝓝 (render S K x m z)) := (render_cont S K m z).continuousAt.tendsto.comp t
  refine tendsto_nhds_unique_of_eventuallyEq (he (simultaneous g y))
    (((Fock.breeze _).continuousAt.tendsto).comp (he y))
    (Eventually.of_forall fun i => ?_) -- tune Ambig
  let p : Marks K strict := ⟨render S K (f i),hf i⟩
  exact (marksSpec strict p).2 u m g y

variable {w : ℕ} (q : Between (tent Y H) j 0 (ruler Λ.block*w) S) (k' : 0 < w)

/-- All of these can be placed at precisely this one width - room needn't grow
with the mark. -/
def patron (x : X) : Entry Y H s j strict w := by
  have p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S := by
    rw [area0]
    exact fun i m => (q i m).1
  have k : render S K x.val ∈ purpose K (meshface (Λ:=Λ) 0 s) j strict :=
    (purpose_ok ..).2 ⟨⟨S,texture S K x.val,p⟩,
      (marksSpec strict (⟨_, fitsMarks Y H strict S x⟩ : Marks K strict)).2⟩
  exact ⟨(⟨_,k⟩ : (𝔙 s)), S, texture S K x.val,q⟩

local notation "i₀" => patron Y H s j strict S q

def shellLinear : (X) →ₗ[ℂ] (A).Op where
  toFun x := β s (i₀ x) k'
  map_add' x y := by
    apply test_high Y H V s Q j strict C; intro t e f
    let D₀(x:X) := slabT Y H t j strict (L₀^(t-s)*w) (furnished Y H s Q j strict w (i₀ x) t e)
    have he (x:X) := snatch Y H V s Q Qt j strict C w (i₀ x) k' e f
    rw [ContinuousLinearMap.add_apply,he,he,he]
    have h : D₀ (x+y) f = D₀ x f+D₀ y f := by
      apply Subtype.ext; unfold D₀; repeat' rw [slab_eq]
      change stream Y H D s _ (render S K ((x+y : X).val))*_=_
      rw [AddSubmonoid.coe_add,map_add,woven_add Y H Q.circuit _ _
        (aux_test (texture ..)) (aux_test (texture ..)),add_mul]
      rfl
    change arrows Y H V _ j 0 strict C t (D₀ (x+y) f)=_
    rw [h,map_add]; rfl
  map_smul' z x := by
    apply test_high Y H V s Q j strict C; intro t e f
    let D₀(x:X) := slabT Y H t j strict (L₀^(t-s)*w) (furnished Y H s Q j strict w (i₀ x) t e)
    have he (x:X) := snatch Y H V s Q Qt j strict C w (i₀ x) k' e f
    rw [ContinuousLinearMap.smul_apply,he,he]
    have h : D₀ (z • x) f = z • D₀ x f := by
      apply Subtype.ext; unfold D₀; repeat' rw [slab_eq]
      change stream Y H D s _ (render S K ((z • x : X).val))*_=_
      rw [Submodule.coe_smul,map_smul,woven_smul Y H Q.circuit _ _ (aux_test (texture ..)),Algebra.smul_mul_assoc]; rfl
    change arrows Y H V _ j 0 strict C t (D₀ (z • x) f)=z • _; rw [h,map_smul]; rfl
local notation "L" => shellLinear Y H V s Q Qt j strict C S q k'

/-- Pay matrix elements linearly; do *not* have to straighten separations or invoke
another interaction estimate for these. Multiply any local tests (including wide) and pay
E of the whole product by fixed support estimates AFTER moving the input to this level. -/
lemma actor_continuous_bills (t : ℕ) (e : s ≤ t) (x y : 𝔙 t) :
    Continuous (fun z : X => inner ℂ ((ιₜ t) y) (L z ((ιₜ t) x))) := by
  let U := (L₀^(t-s)*w)
  let M := meshface (Λ:=Λ) 0 t
  let p := relocate K j (U:ℤ) x.val
  let g := mirror K j M y.val
  obtain ⟨B,Hx⟩ := (show TestFamily K true p from move_ok K j _ (field_test Y H t j 0 strict x)).paid -- tune
  -- ambiguity f? annotate
  obtain ⟨W,Hy⟩ := (show TestFamily K true g from reflect_ok K j _ (field_test Y H t j 0 strict y)).paid
  obtain ⟨Tx,px⟩ := Journey.valuation Y H Hx; obtain ⟨Ty,py⟩ := Journey.valuation Y H Hy
  let S' := volumeAround Λ l (t-s) S
  let U₀ := W ∪ (S'∪B)
  obtain ⟨T,e',h⟩ := fares Y H s Q S (t-s)
  obtain ⟨r,v⟩ := (h 1 zero_lt_one).exists
  let A' := toll Y H t U₀ * Ty * (T*spread S)*Tx
  let f := (innerSL ℂ ((ιₜ t) y)).toLinearMap.comp ((ContinuousLinearMap.apply ℂ A ((ιₜ t) x)).toLinearMap.comp L) -- apply?
  refine (f.mkContinuous A' fun z => ?_).continuous
  change ‖inner ℂ ((ιₜ t) y) (L z ((ιₜ t) x))‖ ≤ _
  let f' := render S K z.val; let k₀ := texture S K z.val; let F := stream Y H D s (t-s) f'
  change ‖inner ℂ ((ιₜ t) y) ((β s (i₀ z) k') ((ιₜ t) x))‖ ≤ _
  rw [snatch Y H V s Q Qt j strict C w (i₀ z) k' e, stems Y H V, slab_eq]
  change ‖E t (g * (F * p))‖ ≤ _
  have hv : InTest K true S' false F := (proceeds Y H Q.circuit s (t-s) k₀).1
  have hh : InTest K true U₀ false (g*(F*p)) :=
    (Hy.mono subset_union_left).mul ((hv.mono (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right)).mul (Hx.mono (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_right)))
  have hp : pay F (T*(spread S * ‖(z:X)‖)) := (v f' k₀ (spread S * ‖(z:X)‖) (fun i => renderLe S K i z.val)).1
  apply (E_bound Y H V t U₀ hh (pay_mul (show pay g Ty from py) (pay_mul hp (show pay p Tx from px)))).trans (le_of_eq ?_)
  unfold A'; ring!

open _root_.YM.Kernel
lemma shell_cont : Continuous (shellLinear Y H V s Q Qt j strict C S q k') := by
  refine @LinearMap.continuous_of_seq_closed_graph ℂ _ (↑(X)) _ (inferInstanceAs (NormedSpace ℂ (X))) _ ((A).Op) _ _ _ L ?_
  intro u x y h t
  apply test_high Y H V s Q j strict C; intro i p g
  apply all_voices Y H Q.circuit j 0 strict C; intro z f
  let t' := max i z; let e' := le_max_left i z; let k := le_max_right i z
  let X' := Raise Y H Q.circuit j 0 strict z t' k f
  let Z := Raise Y H Q.circuit j 0 strict i t' e' g
  rw [← join_actor Y H V Q.circuit j 0 strict C i t' e' g,
    ← join_actor Y H V Q.circuit j 0 strict C z t' k f]
  let i' := (ιₜ t') X'; let v := (ιₜ t') Z
  have h1 : Tendsto (fun i=> inner ℂ i' (L (u i) v)) atTop (𝓝 (inner ℂ i' (L x v))) := (actor_continuous_bills Y H V s Q Qt j strict C S q k' t' (p.trans e') Z X').continuousAt.tendsto.comp h
  have h2 : Tendsto (fun i=> inner ℂ i' (L (u i) v)) atTop (𝓝 (inner ℂ i' (y v))) := tendsto_const_nhds.inner (((ContinuousLinearMap.apply ℂ A v).continuous.continuousAt).tendsto.comp t)
  exact tendsto_nhds_unique h2 h1


include V Q Qt
local notation "S'" => wingspan Λ l S
local notation "xRen" => renovate Y H s Q S

noncomputable def merchandise := {x : (Ark.Ht Y H Q.circuit j 0 strict C).Op |
  ∃ v : fitting Y H strict S, x=shellLinear Y H V s Q Qt j strict C S q k' v}
include q in
private lemma acuteness : Between (tent Y H) j 0 (ruler Λ.block*((L₀^(s+1-s)*w:ℕ):ℤ))
    (wingspan Λ l S) := by
  have h := expands_shape Y H q (s+1-s)
  rw [show s+1-s = 1 by omega] at *
  convert h using 1
  · push_cast; ring
  rfl

lemma merch_separable : IsSeparable (merchandise Y H V s Q Qt j strict C S q k') := by
  let k₀ := L₀^(s+1-s)*w
  let A' := fitting Y H strict S'
  let q' := acuteness Y H V s Q Qt j S q -- include Strict etc tune
  have h₀ : 0 < k₀ := Nat.mul_pos (pow_pos Λ.R.L.property _) k'
  let f := shellLinear Y H V (s+1) Q Qt j strict C S' q' h₀
  have p : IsSeparable (Set.range (xRen)) := venue_separable Y H V s Q S
  have h : IsSeparable (f '' {x : (↑A' : Type) | x.val ∈ Set.range (xRen)}) :=
    SelectionAnalysis.separable_small _ _ p f (shell_cont Y H V (s+1) Q Qt j strict C S' q' h₀)
  apply h.mono
  rintro _ ⟨x,rfl⟩
  let g := furnished Y H s Q j strict w (i₀ x) (s+1) (Nat.le_succ _)
  let y := xRen x.val
  have he(g' : Family K) : stream Y H D s (s+1-s) g'= D s g' := by rw [show s+1-s = 1 by omega]; rfl
  have hy : g.val.val=render (wingspan Λ l S) K y := by
    change stream Y H D s (s+1-s) ((render S K) x.val) = _
    rw [he]; exact (renovate_eq Y H s Q S x.val).symm
  let Z : X := x
  let z : (↑A' : Type) := ⟨y,by
    change render (wingspan Λ l S) K y ∈ marksAlgebra K strict
    rw [←hy]; exact (actorLabel Y H (s+1) j strict g.val).property⟩
  have hx : patron Y H (s+1) j strict _ q' z=g := Subtype.ext (Subtype.ext hy.symm)
  refine ⟨z,⟨x.val,rfl⟩,?_⟩
  change β (s+1) (patron Y H (s+1) j strict _ q' z) h₀ = β s (i₀ x) k'
  rw [hx]; exact (refined_box Y H V s Q Qt j strict C w (i₀ x) k' (s+1) (Nat.le_succ _)).symm

lemma object_separable : IsSeparable (objects Y H V Q Qt j strict C) := by
  let f (S : Finset Cover) (s w : ℕ) := ⋃ (p : 0 < w) (k : Between K j 0 (ruler Λ.block*w) S), merchandise Y H V s Q Qt j strict C S k p
  have ht : IsSeparable (⋃ (S:Finset Cover) (s:ℕ) (w:ℕ), f S s w) := .iUnion fun _ => .iUnion fun _ => .iUnion fun _ => .iUnion fun _ => .iUnion fun _ => merch_separable Y H V _ Q Qt j strict C _ _ _
  apply ht.mono
  rintro _ ⟨s,w,g,p,rfl⟩
  obtain ⟨S,h,k⟩ := g.property
  refine Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨w,
    Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨k,?_⟩⟩⟩⟩⟩
  obtain ⟨x,h⟩ := rendered S K h
  let v : fitting Y H strict S := ⟨x, by
    change render S K x ∈ marksAlgebra K strict; rw [h]
    exact (actorLabel Y H s j strict g.val).property ⟩
  refine ⟨v,?_⟩
  change β s g p = β s (patron Y H s j strict S k v) p
  rw [show patron Y H s j strict S k v=g from Subtype.ext (Subtype.ext h)]

-- Reconstructed C* countabilities used below
lemma drive_separable : SeparableSpace (driveAlgebra Y H V Q Qt j strict C) := by
  apply SelectionAnalysis.separable_cstar
  apply (object_separable Y H V Q Qt j strict C).union
  let f (x : Trans j × ℕ × ℤ) := ((ladder Y H V Q.circuit j 0 strict C).crew x.1).play (notch (timeMesh Λ) x.2.1 x.2.2)
  apply (Set.countable_range f).isSeparable.mono
  rintro _ ⟨x,d,rfl⟩; obtain ⟨s,i,rfl⟩ := notch_exists _ d; exact ⟨(x,s,i),rfl⟩

lemma display_separable : SeparableSpace (displayAlgebra Y H V Q Qt j strict C) := by
  haveI := drive_separable Y H V Q Qt j strict C
  let f := fun x : 𝔅 => (reduceToDisplay Y H V Q Qt j strict C x).val
  have hf : Continuous f := continuous_subtype_val.comp (reduceToDisplay Y H V Q Qt j strict C).continuous
  apply SelectionAnalysis.separable_cstar
  exact (isSeparable_range hf).mono (by rintro _ ⟨x,rfl⟩; exact cap_has_source Y H V Q Qt j strict C x)

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.shell_cont
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.drive_separable
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.display_separable
