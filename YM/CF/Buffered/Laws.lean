import YM.CF.Buffered.Mark
import YM.Push.GRID_APPROXIMATION.KernelLocal
import Mathlib.Probability.Independence.Integration

/-!
# Local dependencies **in law** as used by gaugeM.

`LoomLaw` formalizes loomloc(1), in terms of map measures to *local link
coordinates* of its actual reconstructed gauge fields (NOT auxiliary tags).
The lemma paying for this choice of reconstruction (among legal Roofs) is a
separate input to the corollary. Prove its consequence on Fock insertions.
Prove the link-density requirements taking all branch dependence into account.
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 16000
namespace YM.CF.Buffered.Advance
open Function Fock SU Lat Lattice Cube Finset Wilson RG Branch MeasureTheory ProbabilityTheory Peaks Scroll Tulip Dial Skye Scree
open Push GridApprox Push.SectorMeasure
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ENNReal
attribute [local instance] opCStarAlgebra
variable {N P : Side}
abbrev LEData (S : Support (More N)) := (actualEdges (c:=More N) (S : Set (Seat N))) → SU.E
def extract (S : Support (More N)) (V : Pane N) : LEData S := fun e=>V e.val
lemma extract_agrees (S : Support (More N)) (U V : Pane N) : extract S U = extract S V ↔ Agrees S U V := by
  constructor
  · intro h e p q; exact congr_fun h ⟨e,p,q⟩
  intro h; exact funext fun e=> h e.val (show _∧_ from e.property).1 (show _∧_ from e.property).2
lemma extract_mp (S : Support (More N)) : Measurable (extract S) := measurable_pi_lambda _ fun i=> measurable_pi_apply i.val
private def putBack (S : Support (More N)) (w : LEData S) : Pane N := fun e=> if h : e.1∈ S ∧ e.1+step e.2∈S then w ⟨e,h⟩ else 1
private lemma put_extract (S : Support (More N)) (V : Pane N) : Agrees S V (putBack S (extract S V)) := fun i p q=> by rw [putBack,dif_pos (show i.1∈ S ∧ i.1+step i.2∈ S from ⟨p,q⟩)]; rfl
private lemma put_m (S : Support (More N)) : Measurable (putBack S) := by apply measurable_pi_lambda; intro i; unfold putBack; split; exact measurable_pi_apply _; exact measurable_const
private lemma from_const {α : Type*} (S : Support (More N)) (A : Pane N → α) (p : LocalOn S A) (V : Pane N) : (A ∘ putBack S) (extract S V) = A V := (p _ _ (put_extract S V)).symm

-- strict separation in the MAXIMUM gauge metric
structure LoomLaw (l : Loom N) (w : ℕ) : Prop where
  dep (S : Support (More N)) (x y : Pane N) : Agrees (Lattice.halo w S) x y →
    (depot N).map (fun t=> extract S (l (x,t))) = (depot N).map (fun t=> extract S (l (y,t)))
  splitS (S T : Support (More N)) (p : ∀ i∈S, ∀ j∈T, w < separation i j) (x : Pane N) :
    IndepFun (fun t => extract S (l (x,t))) (fun t=> extract T (l (x,t))) (depot N)
variable {l : Loom N} {w : ℕ} (z : LoomLaw l w) (t : Measurable l)
include z t
lemma loom_integral {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X] [BorelSpace X] [SecondCountableTopology X]
    (x y : Pane N) (S : Support (More N)) (h : Agrees (Lattice.halo w S) x y) (f : Pane N→ X) (p : Measurable f) (g : LocalOn S f) :
    (∫ i, f (l (x,i)) ∂depot N)=∫ i, f (l (y,i)) ∂depot N := by
  let F := f ∘ putBack S; have hs (x : Pane N) : (∫ i, f (l (x,i)) ∂depot N)=∫ j, F j ∂(depot N).map (fun t=> extract S (l (x,t))) := by
    rw [integral_map]; swap; · exact ((extract_mp S).comp (t.comp (measurable_const.prodMk measurable_id))).aemeasurable
    swap; · exact (p.comp (put_m S)).aestronglyMeasurable
    unfold F; simp_rw [from_const S f g]
  rw [hs x,hs y,z.dep S x y h]
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma loom_mult (x : Pane N) (S T : Support (More N)) (p : ∀ i∈ S, ∀ j∈T, w < separation i j) (f g : Pane N → Op I) (e : Envelope f) (j : Envelope g) (a : LocalOn S f) (b : LocalOn T g) :
    (∫ i, (f*g) (l (x,i)) ∂depot N)= (∫ i, f (l (x,i)) ∂depot N) * ∫ i, g (l (x,i)) ∂depot N := by
  let F := f ∘ putBack S; let G:=g ∘ putBack T; let K(i : Ids N):= l (x,i); let X := extract S ∘ K; let Y:=extract T ∘ K
  have hs : F ∘ X=f ∘ K := funext fun i=> from_const S f a _
  have ht : G ∘ Y=g ∘ K := funext fun i=> from_const T g b _
  have he : IndepFun (F ∘ X) (G ∘ Y) (depot N) := (z.splitS S T p x).comp (e.meas.comp (put_m S)) (j.meas.comp (put_m T)); rw [hs,ht] at he
  have k:Measurable K:= t.comp (measurable_const.prodMk measurable_id)
  exact he.integral_bilin (Env.integrableX (Env.along e k) _) (Env.integrableX (Env.along j k) _) (ContinuousLinearMap.mul ℝ (Op I))

omit t z
-- Real kernel but generally noncentral marks on the **same** V. Use checked scalar
-- marginalization over the actual per-link laws and shared tags (`KernelLocal`).
variable (A : RG.StepData (More N) (More P)) (β : ℝ) (B : A.patch.Branches A.kernel SU.group)
def linkLaw (f : Pane N → Op I) (W : Pane P) := ∫ V : Pane N, A.density β W V • f V ∂prior SU.group (More N)
include B
lemma kernel_env : Envelope (fun X : Pane P × Pane N=> A.density β X.1 X.2) := by
  let hk := A.isKernel B β; obtain ⟨C,c⟩:=hk.bound
  exact ⟨hk.meas,C,fun x=> (Real.norm_of_nonneg (hk.positive ..)).symm ▸ c x.1 x.2⟩
lemma slice_env (W : Pane P) : Envelope (A.density (G:=SU.group) β W) := by
  change Envelope (fun V=> (fun X:Pane P×Pane N=> A.density β X.1 X.2) (W,V)); exact Env.along (g:=fun V : Pane N=>(W,V)) (kernel_env A β B) (measurable_const.prodMk measurable_id)
omit B
def coordinate (i k : I) : Op I →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (⟨⟨fun W=> W i k,fun _ _=>rfl⟩,fun _ _=>rfl⟩ : Op I →ₗ[ℝ] ℂ)
lemma coordinate_env {V : Type*} [MeasurableSpace V] (i k : I) {f : V → Op I} (p : Envelope f) : Envelope (fun v=> f v i k) := Girt.pole_w _ (coordinate i k) ((coordinate ..).continuous) p
include B
lemma coordinate_law {f : Pane N → Op I} (p : Envelope f) (W : Pane P) (i k : I) :
    linkLaw A β f W i k = back A β (fun V=> f V i k) W := by
  have ht:=Env.integrableX (Env.scale (slice_env A β B W) p) (prior SU.group (More N)); let C:= coordinate i k
  change C (∫ v, A.density β W v • f v ∂_) = _; rw [←ContinuousLinearMap.integral_comp_comm _ ht]; unfold back; simp_rw [map_smul,Complex.real_smul]; rfl
lemma link_local (S : Support (More N)) {f : Pane N → Op I} (p : LocalOn S f) (h : Envelope f) (T : Support (More P)) (k : ∀ x∈S, GridApprox.window (A.ratio.embed x) (GridApprox.reach A.patch) ⊆ (↑T : Set (Seat P))) :
    LocalOn T (linkLaw A β f) := by
  intro U V e; ext i j; rw [coordinate_law A β B h, coordinate_law A β B h]
  exact back_local B (coordinate_env i j h) (fun U V v=> congr_fun (congr_fun (p U V v) i) j) β _ k U V e
lemma link_mult (x : Pane P) (S T : Support (More N)) (p : Disjoint S T) (f g : Pane N → Op I) (e : Envelope f) (j : Envelope g) (a : LocalOn S f) (b : LocalOn T g) :
    linkLaw A β (f*g) x = linkLaw A β f x * linkLaw A β g x := by
  ext i l; rw [Matrix.mul_apply,coordinate_law A β B (f:=f*g) (env_mult e j)]; simp_rw [coordinate_law A β B e, coordinate_law A β B j]; let F (k:I)(V:Pane N):= f V i k; let G (k:I)(V:Pane N):=g V k l
  calc
    _ = ∑ k : I, back A β (F k * G k) x := by
      unfold back; simp_rw [Pi.mul_apply,Matrix.mul_apply, Finset.mul_sum]
      rw [integral_finsetSum]
      · intro k _; exact Env.integrableX (env_mult (Girt.pole_w _ Complex.ofReal Complex.continuous_ofReal (slice_env A β B x)) (env_mult (coordinate_env i k e) (coordinate_env k l j))) _
    _ = _ := sum_congr rfl fun k _=> congr_fun (back_factors B (coordinate_env i k e) (coordinate_env k l j) (fun U V p=> congr_fun (congr_fun (a U V p) i) k) (fun U V p=> congr_fun (congr_fun (b U V p) k) l) (show Disjoint (↑S : Set (Seat N)) T by simpa) β) x
end YM.CF.Buffered.Advance
