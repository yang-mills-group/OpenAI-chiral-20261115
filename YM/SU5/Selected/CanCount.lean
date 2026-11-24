import YM.SU5.Selected.BoxFinance

/-! Countable determination of concrete norm station (density in *operator
norm*). Includes originally non-sup-separable test functions (all bounded Borel
at a site). Achieved using compact transfer charts and operator realization
at this selected-history extension. Doesn't deduce stage-by-stage uniform price
as n grows. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set TopologicalSpace
open Tapestry (Swatch render texture)
variable (S: Finset Cover) (s u:ℕ)
local notation "r"=>wingspan Λ l S
local notation "R"=>render (r) K
local notation "Bx"=>boxes Y H V G j strict C
local notation "Uk"=>shifts Y H V G j strict C
local notation "Tx"=>transfer Y H G S s
local notation "St"=>stationC Y H V G j strict C

include V in
lemma range_fits : IsSeparable (Set.range Tx) := by
  let X (n:ℕ) := closure ( (Tx) '' closedBall 0 (n:ℝ))
  have he(n):IsSeparable (X n):=
    ((show IsCompactOperator (Tx).toLinearMap from compact_resolution Y H V G S s).isCompact_closure_image_closedBall _).isSeparable
  refine (IsSeparable.iUnion he).mono ?_
  rintro y ⟨a,rfl⟩
  obtain ⟨n,h⟩:=exists_nat_ge ‖a‖
  exact mem_iUnion.mpr ⟨n,(subset_closure ⟨a,mem_closedBall_zero_iff.mpr h,rfl⟩ : Tx a∈X n)⟩

noncomputable def segmentBoxes : Set (A →L[ℂ] A) :=
  {x| ∃ (f:Entry Y H s j strict u) (p:0<u), Between (tent Y H) j 0 (ruler Λ.block*u) S ∧
      InTest K true S false f.val.val ∧ x=B s f p}
lemma segment_small : IsSeparable (segmentBoxes Y H V G j strict C S s u) := by
  let n := (Λ.R.L.val)^((s+1)-s)*u
  rcases eq_or_ne (segmentBoxes Y H V G j strict C S s u) ∅ with h|h
  · rw [h]; exact Set.countable_empty.isSeparable
  have hu : Between K j 0 (ruler Λ.block * u) S ∧ 0<u := by
    obtain ⟨x,f,p,q,e⟩:= nonempty_iff_ne_empty.mpr h; exact ⟨q,p⟩
  have hb : Between K j 0 (ruler Λ.block*n) (r) := by
    have he:=expands_shape Y H hu.1 1
    unfold n; rw [show s+1-s=1 from by omega,Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact he
  have hn:0<n:=Nat.mul_pos (pow_pos Λ.R.L.property _) hu.2
  let fwd:=boxCLM Y H V G j strict C (r) (s+1) n hb hn
  let Q:= (Submodule.subtype (hues Y H strict (r))) ⁻¹' (Set.range Tx)
  have Qv : IsSeparable Q:= preSeparates _ _ (range_fits Y H V G S s)
  refine (Qv.image fwd.continuous).mono ?_
  rintro z ⟨f,p,h,a,t⟩
  obtain ⟨w,c⟩:=Tapestry.rendered S K a
  let u' := Tx w
  let f' := furnished Y H s G.history j strict u f (s+1) (by omega)
  have he: R u'= f'.val.val := by
    rw [←transferred Y H G S s w]
    change G.refine s (render S K w)=stream Y H G.refine s (s+1-s) f.val.val
    rw [c,show s+1-s=1 from by omega]; rfl
  let x: hues Y H strict (r) := ⟨u', fun p=>by rw [he]; exact ((purpose_ok ..).1 f'.val.property).2 p⟩
  refine ⟨x, mem_range_self w,?_⟩
  rw [t]; change (B (s+1) (toEntry Y H j strict (r) (s+1) n hb x) hn)=_
  rw [refined_box Y H V s G.history G.clipped j strict C u f p (s+1) (by omega)]
  exact congrArg (fun x: Entry Y H (s+1) j strict n=> boxOp Y H V (s+1) G.history G.clipped j strict C n x hn) (Subtype.ext (Subtype.ext he) : toEntry Y H j strict (r) (s+1) n hb x=f')
where
 preSeparates (T: Finset Cover)(Z: Submodule ℂ (Swatch T)) {U : Set (Swatch T)} (p:IsSeparable U) : IsSeparable (Z.subtype ⁻¹' U) := (Topology.IsInducing.isSeparable_preimage Topology.IsInducing.subtypeVal p)

lemma boxes_separable : IsSeparable Bx := by
  apply (IsSeparable.iUnion (fun x: Finset Cover × ℕ×ℕ => segment_small Y H V G j strict C x.1 x.2.1 x.2.2)).mono
  rintro x ⟨s,u,f,p,e⟩
  obtain ⟨S,m,t⟩ := f.property
  exact mem_iUnion.mpr ⟨(S,s,u), f,p,t,m,e⟩ -- nesting?

lemma shifts_separable : IsSeparable Uk := by
  let f := fun t : Trans j × MeshClock.marks (timeMesh Λ) => shift Y H V G j strict C t.1 t.2
  exact (countable_range f).isSeparable.mono fun x ⟨a,t,e⟩ => ⟨(a,t),e.symm⟩

private theorem sepMon {W:Type*} [Monoid W] [TopologicalSpace W] [ContinuousMul W] {X:Set W}
    (p:IsSeparable X):IsSeparable (Submonoid.closure X:Set W) := by
  let f (c:W×W):= c.1*c.2
  let S (g:Set W) := g ∪ f '' (g ×ˢ g)
  let T := Nat.rec (motive:=fun _=> Set W) (insert 1 X) (fun _ => S)
  have ht(n): IsSeparable (T n):=by
    induction n with
    | zero=> exact (Set.countable_singleton _).isSeparable.union p -- insert?
    | succ n ih=> exact ih.union ((ih.prod ih).image (continuous_fst.mul continuous_snd))
  apply (IsSeparable.iUnion ht).mono
  have he(x y:ℕ)(p:x≤y): T x ⊆ T y:= monotone_nat_of_le_succ (f:=T) (fun i=> show T i ⊆ T (i+1) from Set.subset_union_left) p
  intro x p
  change x∈Submonoid.closure X at p
  rw [mem_iUnion]; induction p using Submonoid.closure_induction with
  | mem x p=> exact ⟨0,Set.mem_insert_of_mem _ p⟩
  | one=> exact ⟨0,Set.mem_insert _ _⟩
  | mul x y _ _ p q =>
    obtain ⟨i,u⟩:=p; obtain ⟨j,v⟩:=q
    exact ⟨max i j+1,Or.inr ⟨(x,y),⟨he _ _ (le_max_left ..) u,he _ _ (le_max_right ..) v⟩, rfl⟩⟩

instance : SeparableSpace (St) := by
  have h : IsSeparable (St : Set (A→L[ℂ] A)) := by
    change TopologicalSpace.IsSeparable (closure ((slabPolynomials Y H V G j strict C).toSubalgebra.toSubmodule : Set (A→L[ℂ] A)))
    rw [poly_span]
    apply IsSeparable.closure
    apply IsSeparable.span
    exact sepMon ((boxes_separable Y H V G j strict C).union (shifts_separable Y H V G j strict C))
  exact h.separableSpace
lemma horizons : ∃ x : ℕ→St, DenseRange x := exists_dense_seq _
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.horizons
