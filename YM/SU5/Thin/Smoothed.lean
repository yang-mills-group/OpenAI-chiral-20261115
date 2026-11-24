import SatinFixedContrastNovember4
import YM.SU5.Thin.StringLimit
import YM.SU5.Thin.Seam

/-!
# Cross-width convergence of the two smeared fields on the selected vacuum

These estimates work for EVERY smooth compact Dose with support some
positive distance from the seam. The actual canonical fine-grid regulator
formula is used for each Dose (not adjusted weights at smaller intrinsic
width). There is an L¹ estimate for the moving test at the chosen Dose.

In fact can handle ANY sufficiently late grid at each width, not even a
definite ratio to the `dew` scale. Positions stay macroscopic. Do not take
unit cells following the shrinkage of the string. Send every level budget on
the elected price before taking this limit; not asserting e.g. uniform
bounds in finite volume.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
section smears
open MacroGrid
variable (P:Spine) (F:SampleDose)

/-- Signed dose, no limiting-shape assumption on a changing smear. -/
def doseMass : ℝ := ∫ x:Vantage, F.val x
lemma preserveMass (j:Axis) : doseMass (flipDose F j)=doseMass F :=
  (show MeasurePreserving (poseMirror j).toMeasurableEquiv volume volume from opposite_money j).integral_comp' F.val

def doseGrid (t:ℕ) : ℂ := ∑ k ∈ P.usedGrid t F, P.activation t F k
def doseTotal (t:ℕ) : ℝ := ∑ k ∈ P.usedGrid t F, ‖P.activation t F k‖

private lemma scalarQuadrature (g:Vantage→ℝ)(v:Continuous g)(b:HasCompactSupport g)
    (e:Function.support g ⊆ tsupport F.val) :
    Tendsto (fun t:ℕ => ∑ k∈P.usedGrid t F, P.macroStep t^4*g (P.meshPose t k)) atTop
      (𝓝 (∫ x:Vantage, g x)) := by
  refine (rSum_limit P.macroStep P.macroStep_zero g v P.macroStep_pos b).congr fun i=> ?_
  let X:=fun k:Cover=>g (P.meshPose i k)
  have ht (k:Cover)(h:k∉P.usedGrid i F): X k=0:= by
    by_contra w
    exact h ((P.usedPose i F k).2 (e w))
  refine (room_price (P.macroStep i) (P.macroStep_pos i) X (P.usedGrid i F) ht).2.trans ?_
  rw [show Fintype.card Axis=4 by rfl]
  exact Finset.mul_sum ..

lemma sum_dose : Tendsto (fun i=>P.doseGrid F i) atTop (𝓝 (↑(doseMass F) : ℂ)) :=
  (Complex.continuous_ofReal.continuousAt.tendsto.comp
    (scalarQuadrature P F F.val F.smooth.continuous F.budget subset_closure)).congr
      (fun _=> Complex.ofReal_sum _ _)
lemma totalVariation_dose : Tendsto (fun i=>P.doseTotal F i) atTop
    (𝓝 (∫ x:Vantage, ‖F.val x‖)) := by
  let g:=fun x:Vantage=> ‖F.val x‖
  refine (scalarQuadrature P F g (F.smooth.continuous.norm) F.budget.norm ?_).congr fun i=> ?_
  · exact fun x (h:g x ≠ 0)=> subset_closure (fun p=>h (by change ‖F.val x‖=_; rw [show F.val x=0 from p,norm_zero]))
  apply Finset.sum_congr rfl; intro k _
  unfold activation; rw [Complex.norm_real, norm_mul, Real.norm_of_nonneg (show 0≤P.macroStep i^4 from by positivity)]
end smears

section pack
open ThinEstimate
variable (X:Hilbert)(S:OS.Semigroup X (3:Axis))
variable (v:ℕ→X) (z:X)
variable (U:ℕ→ Cover→X.Op)
variable (f:ℕ→ Cover→ℝ≥0)
variable (u:∀ i b x,‖U i b x‖=‖x‖)(e:∀ i k,U i k z=z) (y:∀ b,S.E b z=z)
variable (L:ℕ→Finset Cover)(a:ℕ→ Cover→ℂ)(R:ℝ≥0)(r:ℂ)
include e y u
/-- Heat majorization on the full-axis chart, exposure times also arbitrary. -/
private lemma strung (i t:ℕ)(k:Cover)(l:ℝ≥0) (q:l≤ f t k) :
    dist (U t k (S.E (f t k) (v i))) (r • z) ≤ dist (S.E l (v i)) (r • z) := by
  have ht(t:ℝ≥0)(w:X) : dist (S.E t w) (r • z)= ‖S.E t (w-r • z)‖ := by
    rw [dist_eq_norm,map_sub,map_smul,y]
  have he(t:ℕ)(k:Cover)(w:X): dist (U t k w) (r • z) = dist w (r • z) := by
    simp_rw [dist_eq_norm]; nth_rw 1 [← (show U t k (r • z)=r • z from (map_smul (U t k) r z).trans (congrArg (r • ·) (e t k)))]; rw [←map_sub,u]
  rw [he, ht, ht]; exact heat_minorizes X S _ q
/-- Uniform in the pose grid level (always the genuine price at any such `t`). -/
private lemma stageCost (i t:ℕ)(w:∀ k ∈ L t, R ≤ f t k) :
    dist (∑ k∈ L t,a t k • U t k (S.E (f t k) (v i))) ((∑ k∈ L t,a t k) • (r • z)) ≤
      (∑ k∈ L t,‖a t k‖)*dist (S.E R (v i)) (r • z) := by
  rw [Finset.sum_smul,dist_eq_norm,←Finset.sum_sub_distrib,Finset.sum_mul]
  refine (norm_sum_le ..).trans ?_
  apply Finset.sum_le_sum; intro k h
  rw [← smul_sub,norm_smul, ←dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (strung X S v z U f u e y r i t k R (w k h)) (norm_nonneg _)
omit e y u
variable (G:ℕ→ℕ→ X) (g:ℕ→ X)
-- pass to the limit: both synchronous along any grid path, and iterated fine-grid first give the same answer.
private lemma synced {Y:Type*}(W:Filter Y)(r:ℂ)(m₀:ℕ→ℂ)(u₀:ℕ→ℝ)(m:ℂ)(B:ℝ)(c:ℕ→ℝ)
    (h:Tendsto m₀ atTop (𝓝 m))(p:Tendsto c atTop (𝓝 0))(e:Tendsto u₀ atTop (𝓝 B))
    (f:∀ i t, dist (G i t) (m₀ t • (r • z)) ≤ u₀ t * c i)(b t:Y→ℕ)
    (a:Tendsto b W atTop)(x:Tendsto t W atTop) : Tendsto (fun i=> G (b i) (t i)) W (𝓝 (m • (r • z))) := by
  have hu:= (h.comp x).smul (tendsto_const_nhds (x:=r • z))
  refine (tendsto_iff_of_dist ?_).2 hu
  have hv := (e.comp x).mul (p.comp a)
  rw [mul_zero] at hv; exact squeeze_zero (fun _=>dist_nonneg) (fun k=> f (b k) (t k)) hv

private lemma passing (v:X)
    (h:∀ t:ℕ→ℕ,Tendsto t atTop atTop → Tendsto (fun i=> G i (t i)) atTop (𝓝 v))
    (p:∀ i,Tendsto (G i) atTop (𝓝 (g i))) : Tendsto g atTop (𝓝 v):=by
  apply Metric.tendsto_nhds.mpr
  intro ε e
  have e':0<ε/2:= half_pos e
  choose t p q using fun i:ℕ=> ((Metric.tendsto_nhds.mp (p i) _ e').and (eventually_ge_atTop i)).exists
  filter_upwards [Metric.tendsto_nhds.mp (h t (tendsto_atTop_mono q tendsto_id)) _ e'] with i x
  have ht:dist (g i) (G i (t i))<ε/2:=(dist_comm ..|>.trans_lt (p i))
  exact (dist_triangle (g i) (G i (t i)) v).trans_lt ((add_lt_add ht x).trans_eq (add_halves ε))
end pack

section science
variable (P:Spine) (x:P.Spectrum0 3) (Z:Lead.Clan) (F:SampleDose)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "H" => P.ColorHil 3 ξ
local notation "S" => P.physicalEnergy 3 ξ
local notation "E" => (P.physicalEnergy 3 ξ).E
local notation "π₀" => P.colorZero 3 ξ
local notation "G" => P.shard x Z
local notation "g" => (↑(purePrice Z):ℂ)

def WallSlack (B:SampleDose) (l:ℝ≥0) : Prop := ∀ x∈ tsupport B.val, (l:ℝ) ≤ x (3:Axis)
/-- Full strict slack qualification, zero seam. -/
def MatureAfter (B:SampleDose) : Prop := ∃ l:ℝ≥0, 0<l ∧ WallSlack B l
private lemma poseMeets {l:ℝ≥0} (h: WallSlack F l)(t:ℕ)(k:Cover)(v:k∈P.usedGrid t F):
    l ≤ (P.meshPose t k 3).toNNReal := by
  have he:= h (P.meshPose t k) ((P.usedPose t F k).mp v)
  apply NNReal.coe_le_coe.mp; rwa [Real.coe_toNNReal _ (l.property.trans he)]

/-- Cross-resolution error budget on the cost of a putative ground price.
`v` can come from any such Aprons. Does not assume bounds on limiting norms.
Includes the L¹ seminorm dependence on the test. -/
lemma massEstimate (v:ℕ→ H) (z:ℂ)(l:ℝ≥0)(h:WallSlack F l) (i t:ℕ) :
    dist (P.wallSignal x t F (v i)) (P.doseGrid F t • (z • π₀)) ≤
      P.doseTotal F t * dist (E l (v i)) (z • π₀) :=
  stageCost H (S) v π₀ (fun t k=> P.truck 3 ξ (P.vtile t k)) (fun t k=> (P.meshPose t k 3).toNNReal)
    (fun t k=> P.truck_norm 3 ξ (P.vtile t k)) (fun t k=> P.truck_empty 3 ξ (P.vtile t k))
    (P.sector_hot 3 ξ) (fun t=> P.usedGrid t F) (fun t=> P.activation t F) l z i t (poseMeets P F h t)

lemma smearEstimate (v:ℕ→ H) (z:ℂ)(l:ℝ≥0)(h:WallSlack F l)(p:Tendsto (fun i:ℕ=> E l (v i)) atTop (𝓝 (z • π₀)))
    {Y:Type*}(W:Filter Y)(b t:Y→ℕ)(a:Tendsto b W atTop)(u:Tendsto t W atTop):
    Tendsto (fun i=>P.wallSignal x (t i) F (v (b i))) W (𝓝 ((doseMass F:ℂ) • (z • π₀))) :=
  synced H π₀ (fun i t=>P.wallSignal x t F (v i)) W z _ _ _ _ _ (P.sum_dose F)
    (Eq.mp (congrArg (fun z₁=> Tendsto (fun i:ℕ=> dist (E l (v i)) (z • π₀)) atTop (𝓝 z₁))
      (dist_self _)) (p.dist (tendsto_const_nhds (x:= z • π₀))))
    (P.totalVariation_dose F) (P.massEstimate x F v z l h) b t a u

/-- The smoothed true Euclidean field **on this vacuum**, as a field insertion
receipt (always use `P.thinString` regulator representatives with their dressing
and normalization). The statement is for one-point, field-vacuum product and
paired-field readings ONLY, with external separation from the seam. Use the
sequence-defined fields in comparisons, not limiting operators or numbers
unaccompanied by their regulator scheme. -/
def thinField : P.ColorHil 3 (P.otherSpectrum 3 3 x) :=
  (↑(doseMass F):ℂ) • (g • π₀)
lemma thinMassOne (p:F.Normalized) : P.thinField x Z F=g • π₀ :=
  (congrArg (fun z:ℝ=>(z:ℂ) • (g • π₀)) (show doseMass F=1 from p.2)).trans
    ((congrArg (fun c:ℂ=> c • (g • π₀)) Complex.ofReal_one).trans (one_smul ℂ _))
lemma sameMass : P.thinField x Z (flipDose F 3)=P.thinField x Z F :=
  congrArg (fun z:ℝ=> (z:ℂ) • (g • π₀)) (preserveMass F 3)

variable {P x} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (R:P.Experiment K c r x J)
include R
/-- Control any sequences of meshes and width shrinkage. When interpreting as
fields always use `c(b_i) ≤ t_i`. This particular estimate doesn't even need
that inequality. `t` is not an assumed diagonal chosen from scalar prices. -/
lemma widthSignal {Y:Type*}(W:Filter Y) (v:MatureAfter F)
    (b t:Y→ℕ) (e:Tendsto b W atTop) (p:Tendsto t W atTop) :
    Tendsto (fun i=> P.wallSignal x (t i) F (G (c (b i)) (r (b i)))) W (𝓝 (P.thinField x Z F)) :=
  P.smearEstimate x F (fun i=> G (c i) (r i)) g v.choose v.choose_spec.2
    (thin_cost Z R v.choose v.choose_spec.1) W b t e p
lemma afterField (v:MatureAfter F) :
    Tendsto (fun i=> P.wallContinuum x F (G (c i) (r i))) atTop (𝓝 (P.thinField x Z F)) :=
  passing H (fun i t=> P.wallSignal x t F (G (c i) (r i))) _ (P.thinField x Z F)
    (fun t=> widthSignal Z F R atTop v (fun i=>i) t tendsto_id) (fun i=> P.at_seam x F J (G (c i) (r i)))

omit R
lemma MatureAfter.eventually (A:ℕ→P.Apron) (p:Tendsto (fun i=> (A i).realWidth P 3) atTop (𝓝 0))
    (h:MatureAfter F) : ∀ᶠ i:ℕ in atTop,P.WallAfter (A i) F 0 := by
  let a := h.choose
  filter_upwards [p.eventually (gt_mem_nhds (NNReal.coe_pos.mpr (show 0<a from h.choose_spec.1)))] with i v
  intro p u
  exact ((zero_add _).trans_lt v).trans_le (h.choose_spec.2 p u)
lemma seam_strict (l:ℝ) (v: l>0) (h:∀ i∈tsupport F.val, l ≤ i (3:Axis)) : MatureAfter F :=
  ⟨⟨l,v.le⟩, NNReal.coe_pos.mp v,h⟩
lemma mirror_strict (l:ℝ) (v:l>0)(h:∀ i∈tsupport F.val, i (3:Axis)≤ -l) : MatureAfter (flipDose F 3) := by
  apply seam_strict _ l v
  intro i u
  rw [flipBudget F 3] at u
  have hx: opposeR 3 i 3 ≤ -l:= h (opposeR 3 i) u
  rw [show opposeR 3 i 3= -i 3 from if_pos rfl] at hx
  linarith only [hx]
lemma mirrorFitsBefore (A:P.Apron) (h: P.WallAfter A (flipDose F 3) 0) :
    P.WallBefore (A.kiss P 3) F 0:= by
  intro i p
  let k:= opposeR 3 i
  have ht : k ∈ tsupport (flipDose F 3).val := by
    rw [flipBudget]; exact (show opposeR 3 (opposeR 3 i) ∈ tsupport F.val from (reflectPose_twice 3 i).symm ▸ p)
  have hx:= h k ht
  rw [show k 3= -i 3 from if_pos rfl] at hx
  change _+A.realWidth P 3 < _; linarith only [hx]

#print axioms afterField
#print axioms widthSignal
#print axioms massEstimate
end science
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
