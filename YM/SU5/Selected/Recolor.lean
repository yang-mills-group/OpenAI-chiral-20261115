import YM.SU5.Selected.Countable
import YM.SU5.FiniteGaugeData.Tapestry.Cloudburst
/-!
# Level gauge on the physical refinement committed by the election.

Important gauge obligation: on ANY shape support, not just on a neutral test. Raise
the local gauge transformation with the same physical label as the D-refined mark,
prove gauge law of the assembly. Use implementation on **exactly this** tower line,
not any harmony theorem about a differently elected D.

Also ground equality upgraded to actual *slab insertion* operator equality for these
local colors (loose as well as strict). Useful for identifying selected physical algebra.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 300000
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
open Tapestry
variable {S : Finset Cover}
local notation "W" => wingspan Λ l S
local notation "Ψ" r:max F:max=> block Y H s (i (a r)) (k (b r)) S F

section paint
-- in some lemmas we omit unused section variables; do not call with others.
lemma display_eq_exhibit (t n : ℕ) (F : Family (tent Y H)) : distribute Y H t n F=exhibit Y H t n F :=
  (Tapestry.arranged _ _ (terrain Y H (Y.ir n) t) (F (momentm Y n t))).symm

lemma salt_lens {m n : ℕ} (p : legalAt Y s m n)
    (q : Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y m (s+1))))
    {f g : Family (tent Y H)} (h : InTest K true S false f) (v : InTest K true S false g)
    (x : Cover → SU.E) (e : Circular S (parentGauge Λ x) f g) :
    Circular (wingspan Λ l S) x (block Y H s m n S f) (block Y H s m n S g) := by
  let X := block Y H s m n S f; let Y' := block Y H s m n S g
  have hQ : Hosp W (Journey.side Y m (s+1)) := (show (tent Y H).c (momentm Y m (s+1))=Journey.side Y m (s+1) from terrain Y H (Y.ir m) (s+1)) ▸ q.hosp
  obtain ⟨G,hG⟩ := scoreTrace x hQ
  have hu : TraceGauge S (parentGauge Λ x) (Peaks.scaleG (Vale.apt (Y.ir m) Λ.block Λ.R.L s) G) :=
    hierarchyTrace S x Y s m G hG
  have hm : Harmony G (aboveD Y H s m n f) (aboveD Y H s m n g) :=
    ascendHarmony Y s m n p (stationed Y H s S m v) G (stationed Y H s S m h).env
      (by rw [display_eq_exhibit,display_eq_exhibit]; exact truePrinting S (parentGauge Λ x) Y H s m e hu) -- tune determine S
  have he : Harmony G (exhibit Y H (s+1) m X) (exhibit Y H (s+1) m Y') := by
    rw [← display_eq_exhibit,← display_eq_exhibit,reserved Y H s S m n p h q,reserved Y H s S m n p v q]
    exact hm
  -- now require Hosp at one upper not all: apply nativeColor
  obtain ⟨f',hx⟩ := rendered W K (booked Y H s m n S f)
  obtain ⟨g',hy⟩ := rendered W K (booked Y H s m n S g)
  rw [←hx,←hy]; apply nativeColor W x Y H (s+1) m G hQ hG
  rw [present_exhibit,present_exhibit,hx,hy]; exact he

include Q
lemma recollects {F : Family (tent Y H)} (p : InTest K true S false F) (h : Side)
    (v : Fields ((tent Y H).c h)) : Tendsto (fun t : ℕ => (Ψ t F) h v) atTop (𝓝 (D s F h v)) := by
  obtain ⟨R,u⟩ := Journey.valuation Y H p
  have ht : pay F R := u; have hR := pay_nonneg ht
  obtain ⟨C,t,f⟩ := Q.implements s S
  apply Metric.tendsto_nhds.mpr; intro ε e; have h1 : 0< ε/(R+1) := by positivity
  filter_upwards [f _ h1] with n V
  have he : pay ((Ψ n F) - D s F) ((ε/(R+1))*R) := (V F p R u).2.2.1
  rw [dist_eq_norm]; apply (show ‖(Ψ n F) h v-D s F h v‖ ≤ (ε/(R+1))*R from he h v).trans_lt
  exact (mul_lt_mul_of_pos_left (by linarith : R<R+1) h1).trans_eq (div_mul_cancel₀ _ (by positivity))
include V
lemma lens_up {f g : Family (tent Y H)} (h : InTest K true S false f) (v : InTest K true S false g)
    (x : Cover → SU.E) (e : Circular S (parentGauge Λ x) f g) :
    Circular (wingspan Λ l S) x (D s f) (D s g) := by
  intro n a' t z
  have hp : Tendsto (fun t => (Ψ t f) n (simultaneous a' z)) atTop (𝓝 (D s f n (simultaneous a' z))) :=
    recollects Y H s Q h n _
  have he := (Fock.breeze (quantU (tradew _ a'))).continuousAt.tendsto.comp (recollects Y H s Q v n z) -- tune
  apply tendsto_nhds_unique_of_eventuallyEq hp he
  filter_upwards [(V.pick.grow_i.comp Q.growsA).tendsto_atTop.eventually (Tower.turning Y H (s+1) W), Q.finance (s+1)] with r hr hx
  exact (salt_lens Y H s ⟨hx.depth,hx.enters⟩ hr h v x e) n a' t z
/-- Strengthen refinement consistency to interlevel covariance of the whole D on supported
inputs. (Use any extension of the input gauge by physical continuum labels.) NB
coordinates of Tapestry's `addressG` are in level-zero gauge units. -/
lemma lens_presentation (n : ℕ) {f g : Family (tent Y H)}
    (h : InTest K true S false f) (v : InTest K true S false g) (x : GPhysical) (e : Circular S (restrictG Λ s x) f g) :
    Circular (volumeAround Λ l n S) (restrictG Λ (s+n) x) (stream Y H D s n f) (stream Y H D s n g) := by
  induction n with
  | zero => exact e
  | succ i p =>
    rw [←Nat.add_assoc]; rw [gaugeHarmony Λ (s+i) x] at p
    exact lens_up Y H V (s+i) Q (proceeds Y H Q.circuit s i h).1 (proceeds Y H Q.circuit s i v).1 _ p
end paint

section brand
lemma flipped_pair_right {J : Calibration} {T' : Finset Cover} (f g t : Family J)
    (p : InTest J true T' false t) (e : Disjoint S T') (u : Cover → SU.E) (h : Circular S u f g) :
    ∃ v : Cover→SU.E, Circular (S∪T') v (f*t) (g*t) := by
  let v := fun x => if x∈S then u x else 1
  have hv : Circular S v f g := circle_swap h fun _ t => if_pos t
  have hx : Circular T' v t t := circle_swap (circle_still p) fun _ t => if_neg (by
    intro q; exact Finset.disjoint_left.mp e q t)
  exact ⟨v,Circular.mul v _ (largerGauge subset_union_left hv) (largerGauge subset_union_right hx)⟩

lemma detached_disjoint {T : Finset Cover} (p : Detached Λ l S T) : Disjoint S T := by
  apply Finset.disjoint_left.mpr; intro x h t; apply p x h x t; simp [Lattice.box_test]; omega

local notation "K'" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "ℛ₁" i:max => Tower.region j (meshface (Λ:=Λ) 0 i) (K).ℓ
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "A" s:max => actor Y H s Q.circuit j 0 strict C
local notation "P₁" s:max => boxOp Y H V s Q Qt j strict C
include V Q Qt

/-- Local point colors make the same insertion on a *full* H when acting on an arbitrary
loose mark at this level, owing to disjointness to its (advanced) argument. -/
lemma color_slab_here {w : ℕ} (x y : Entry Y H s j strict w)
    (p : InTest K true S false x.val.val) (h : InTest K true S false y.val.val)
    (v : Between K j 0 (ruler Λ.block*w) S) (u : Cover → SU.E) (q : Circular S u x.val.val y.val.val)
    (a : 𝔙 s) : (A s) (slabT Y H s j strict w x a) = (A s) (slabT Y H s j strict w y a) := by
  -- any far (or even immediately adjoining) later actor is UNAFFECTED by local colors
  let F := relocate K j w a.val
  obtain ⟨B,t,e⟩ := (show ∃ S' : Finset Cover, InTest K true S' false a.val ∧ (ℛ₁ s) S' from
    ((purpose_ok ..).1 a.property).1)
  let T := plow K j w B
  have hf : InTest K true T false F := flow_port K j _ t
  have ht : Tower.region j (ruler Λ.block * (w:ℤ)) (K).ℓ T := by
    rw [area0] at e; intro i p; obtain ⟨y,p',rfl⟩ := plow_stays K j w B p
    rw [moves,if_pos rfl]; change _ ≤ y j +ruler Λ.block*w; specialize e y p'; omega
  have hz := cover_between K Λ l rfl j (S:=S) (fun i m => (v i m).2) ht
  obtain ⟨u',v'⟩ := flipped_pair_right _ _ _ hf (detached_disjoint hz) u q
  apply actor_paint Y H V s Q j strict C _ _ _ _ _ u'
  · rw [slab_eq,slab_eq]; exact v'
  · rw [slab_eq]; exact (p.mono subset_union_left).mul (hf.mono subset_union_right)
  · rw [slab_eq]; exact (h.mono subset_union_left).mul (hf.mono subset_union_right)
  intro i m; rw [area0]; have hc : 0 ≤ ruler Λ.block * (w:ℤ) := mul_nonneg (ruler_gene Λ.block).le (by positivity)
  rcases Finset.mem_union.mp m with t|t
  · exact (v _ t).1
  exact (ht i t).trans' (add_le_add_left hc _) -- flipped note tune

lemma expanding_lane {w : ℕ} (v : Between K j 0 (ruler Λ.block*w) S)
    (k : ℕ) : Between K j 0 (ruler Λ.block*((L₀^k*w:ℕ):ℤ)) (volumeAround Λ l k S) := by
  have he := expands_shape Y H v k; convert he using 1; push_cast; ring
/-- Therefore insertion operators invariant on the full ellipse algebra. -/
theorem color_slab {w : ℕ} (d : 0 < w) (x y : Entry Y H s j strict w)
    (p : InTest K true S false x.val.val) (h : InTest K true S false y.val.val)
    (v : Between K j 0 (ruler Λ.block*w) S) (u : Cover → SU.E) (q : Circular S u x.val.val y.val.val) :
    entrance Y H V s Q Qt j strict C x d = entrance Y H V s Q Qt j strict C y d := by
  apply Subtype.ext
  change (P₁ s) w x d=(P₁ s) w y d
  apply test_high Y H V s Q j strict C; intro r t y'
  rw [snatch Y H V s Q Qt j strict C w x d t,snatch Y H V s Q Qt j strict C w y d t]
  obtain ⟨u₀,e⟩ := iceExtension Λ s u; rw [←e] at q
  exact color_slab_here Y H V r Q Qt j strict C _ _ (proceeds Y H Q.circuit s (r-s) p).1 (proceeds Y H Q.circuit s (r-s) h).1
    (expanding_lane Y H V Q Qt j v (r-s)) _ (lens_presentation Y H V s Q _ p h u₀ q) y'
end brand
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.lens_presentation
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.color_slab
