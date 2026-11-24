import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
 
/-!
# Full-axis compact sensor quadratures
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sextet
namespace Quadrature
open Metric Function MeasureTheory Set Filter
open scoped Topology

variable {I:Type*} [Fintype I]
abbrev Grid (I:Type*) := I→ℤ
abbrev Pose (I:Type*) := I→ℝ
section Lattice
variable (h:ℝ) (q r:Grid I) (x:Pose I)

def node : Pose I := fun i=>h*(q i:ℝ)
omit [Fintype I] in
lemma node_zero : node h (0:Grid I)=0 := funext fun i=>by simp [node]
omit [Fintype I] in
lemma node_add : node h (q+r)=node h q+node h r := funext fun i=>by simp [node,mul_add]
omit [Fintype I] in
lemma node_sub : node h (q-r)=node h q-node h r := funext fun i=>by simp [node,mul_sub]

lemma stamp {S:Set (Pose I)} (ch:IsCompact S) (pos:0<h) : ((node h)⁻¹' S).Finite := by
  obtain ⟨R,hR⟩:=ch.isBounded.subset_closedBall 0
  refine ((isCompact_closedBall (0:Grid I) (max 0 R/h)).finite ⟨inferInstance⟩).subset ?_
  intro x hx
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (div_nonneg (le_max_left _ _) pos.le)]
  intro i
  rw [le_div_iff₀' pos,←Int.norm_cast_real (x i),
    ←show ‖h‖=h from Real.norm_of_nonneg pos.le,←norm_mul]
  exact ((norm_le_pi_norm (node h x) i).trans (mem_closedBall_zero_iff.mp (hR hx))).trans (le_max_right _ _)

lemma family {W:Type*} [Zero W] {f:Pose I→W} (pos:0<h) (b:HasCompactSupport f) :
    HasFiniteSupport (f ∘ node h) :=
  (stamp h b pos).subset (fun _ p => subset_closure (s:=support f) p)

private def which : Grid I := fun i=>⌊x i/h⌋
private def round : Pose I := node h (which h x)
private def tile : Set (Pose I) := Set.univ.pi fun i=>Ico (node h q i) (node h q i + h)

variable {h} (p:0<h)
private lemma tileMeas : MeasurableSet (tile h q) := MeasurableSet.univ_pi fun _=>measurableSet_Ico

private lemma tileVolume {h:ℝ} : volume (tile h q)=ENNReal.ofReal h ^ Fintype.card I := by
  rw [volume_pi,tile,Measure.pi_pi]
  simp only [Real.volume_Ico,add_sub_cancel_left,Finset.prod_const,Finset.card_univ]

include p
omit [Fintype I] in
private lemma which_tile : x∈tile h q ↔ which h x=q := by
  have g (i:I) : x i ∈ Ico (node h q i) (node h q i + h) ↔ which h x i=q i := by
    rw [which,node,mem_Ico,Int.floor_eq_iff, le_div_iff₀' p,div_lt_iff₀' p,mul_add,mul_one]
  exact ⟨fun w=>funext fun i=>(g i).mp (w i (mem_univ _)),
       fun e i _=>(g i).mpr (congrFun e i)⟩

private lemma dist_round : dist (round h x) x ≤ h := by
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg p.le]
  intro i
  have e:= (which_tile (which h x) x p).mpr rfl i (mem_univ _)
  have f:x i< round h x i+h :=e.2
  have g:round h x i≤x i :=e.1
  rw [Pi.sub_apply,Real.norm_eq_abs,abs_le]
  constructor <;> linarith
end Lattice

section Riemann
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (f:Pose I→X) {h:ℝ} (p:0<h)

private def elem (q:Grid I) := (tile h q).indicator (fun _=> f (node h q))
omit [CompleteSpace X] [NormedSpace ℝ X] in
private lemma elemIntegrable (q:Grid I) : Integrable (elem f (h:=h) q) := by
  refine (integrable_indicator_iff (tileMeas q)).mpr (integrableOn_const ?_)
  rw [tileVolume]; finiteness

include p
private lemma elemValue (q:Grid I) : ∫ x, elem f (h:=h) q x=
    (h ^ Fintype.card I) • f (node h q) := by
  unfold elem
  rw [integral_indicator (tileMeas _),setIntegral_const,Measure.real,tileVolume,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal p.le]

variable (b:HasCompactSupport f)

omit [CompleteSpace X] [NormedSpace ℝ X] in
private lemma tileSum : f ∘ round h = ∑ q ∈ (family h p b).toFinset, elem f (h:=h) q := by
  funext x
  rw [Finset.sum_apply,Finset.sum_eq_single (which h x)]
  · rw [elem,indicator_of_mem ((which_tile (which h x) x p).mpr rfl)]; rfl
  · intro y _ k
    exact indicator_of_notMem (mt (which_tile y x p).mp (Ne.symm k)) _
  · intro u
    rw [elem,indicator_of_mem ((which_tile (which h x) x p).mpr rfl)]
    by_contra e
    exact u ((family h p b).mem_toFinset.mpr e)

include b
omit [CompleteSpace X] [NormedSpace ℝ X] in
private lemma tileIntegrable : Integrable (f ∘ round h) := by
  rw [tileSum f p b]
  exact integrable_finsetSum' _ fun _ _=>elemIntegrable ..
private lemma sum_rule : (∫ x, f (round h x))=
    (h^Fintype.card I) • ∑ᶠ q, f (node h q) := by
  change (∫x, (f ∘ round h) x)=_
  rw [tileSum f p b, finsum_eq_sum_of_support_subset (fun q=>f (node h q))
    (s:=(family h p b).toFinset) (fun _ m=>(family h p b).mem_toFinset.mpr m)]
  simp_rw [Finset.sum_apply]
  rw [integral_finsetSum _ fun q _ => elemIntegrable f q,Finset.smul_sum]
  simp_rw [elemValue f p]
end Riemann

variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {f:Pose I → X} (t:Continuous f) (b:HasCompactSupport f)
variable {η:ℕ→ℝ} (p:∀i,0<η i) (h:Tendsto η atTop (𝓝 0))
include p h

private lemma round_converges (x:Pose I) : Tendsto (fun i=>round (η i) x) atTop (𝓝 x) :=
  tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _=>dist_nonneg) (fun _=>dist_round _ (p _)) h)

include t b

/-- Ordinary Riemann sum convergence for bodily sensors, including vector costs. No strong
continuity on the input family away from positions billed by sensor is needed here: `f`
describes a global extension **including** cutoffs, and takes exactly node values wherever
billed. -/
theorem ages :
    Tendsto (fun i=>η i ^ Fintype.card I • ∑ᶠ q,f (node (η i) q)) atTop (𝓝 (∫x,f x)) := by
  obtain ⟨R,r⟩:= b.isBounded.subset_closedBall (0:Pose I)
  let B:=closedBall (0:Pose I) (R+1)
  obtain ⟨C,c⟩:= b.exists_bound_of_continuous t
  let F:=B.indicator (fun _=>C)
  have g:Integrable F volume := (integrable_indicator_iff measurableSet_closedBall).mpr
    (integrableOn_const (isCompact_closedBall ..|>.measure_ne_top))
  have m(i):Integrable (fun x=>f (round (η i) x)) volume:=tileIntegrable f (p i) b
  refine (tendsto_integral_filter_of_dominated_convergence
    F (F:=fun i x=>f (round (η i) x))
    (.of_forall fun i=>(m i).aestronglyMeasurable) ?_ g
    (ae_of_all _ fun x=>(t.tendsto x).comp (round_converges p h x))).congr fun i=>sum_rule f (p i) b
  filter_upwards [h.eventually (ge_mem_nhds zero_lt_one)] with i hi
  refine ae_of_all _ fun x=>?_ 
  by_cases q:x∈B
  · rw [show F x=C from indicator_of_mem q _]; exact c _
  let y:=round (η i) x
  have e:f y=0:=by
    by_contra v
    exact q (show dist x 0≤R+1 from
      (dist_triangle x y 0).trans (by
        have g:dist y 0 ≤ R:=r (subset_closure (s:=support f) v)
        have k:dist x y ≤ 1:=(dist_comm ..).le.trans ((dist_round _ (p i)).trans hi)
        linarith))
  show ‖f y‖≤F x
  rw [e,norm_zero,show F x=0 from indicator_of_notMem q _]

omit t b
omit [CompleteSpace X] in
/-- Cost rule in compact footprint, uniform in **all** entries for sufficiently fine mesh.
Pay only the sup error times a fixed constant for a compact. `stamp` ensures finiteness
whenever asking with this hypothesis. -/
lemma eventually_bills {K:Set (Pose I)} (k:IsCompact K) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ i in atTop,∀v:Grid I→X,
      support v ⊆ (node (η i))⁻¹' K → ∀ε:ℝ,0≤ε→(∀q,‖v q‖≤ε)→
      ‖(η i)^Fintype.card I • ∑ᶠq,v q‖ ≤ C*ε := by
  obtain ⟨R,r⟩:= k.isBounded.subset_closedBall 0
  let g: Pose I→ℝ:=fun x=>max 0 (R+1-‖x‖)
  have hg : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (R+1)) ?_
    intro x q
    rw [mem_closedBall_zero_iff,not_le] at q
    exact max_eq_left (sub_nonpos_of_le q.le)
  have gt : Continuous g := by unfold g;fun_prop
  let d : ℝ:=∫ x,g x
  let C:=max 0 d+1
  have : d<C:=(le_max_right ..).trans_lt (lt_add_one _)
  refine ⟨C,(le_max_left ..).trans_lt (lt_add_one _),?_⟩
  filter_upwards [(ages gt hg p h).eventually (ge_mem_nhds this)] with i hi v u ε e b
  have gF:=family _ (p i) hg
  rw [smul_eq_mul,finsum_eq_sum_of_support_subset (s:=gF.toFinset) (fun q=>g (node (η i) q)) (fun _ m=>gF.mem_toFinset.mpr m)] at hi
  rw [finsum_eq_sum_of_support_subset (s:=gF.toFinset) _ ?_,norm_smul,Real.norm_of_nonneg (pow_nonneg (p i).le _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hi e)
    rw [mul_assoc,Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum ?_)) (pow_nonneg (p i).le _)
    intro q _
    have c:0≤ g (node (η i) q) := le_max_left ..
    by_cases a:v q=0
    · rw [a,norm_zero];exact mul_nonneg c e
    refine (b _).trans (le_mul_of_one_le_left e ?_)
    have l:= mem_closedBall_zero_iff.mp (r (u a))
    exact (show 1≤ R+1-‖node (η i) q‖ by linarith).trans (le_max_right ..)
  intro q b
  have l:= mem_closedBall_zero_iff.mp (r (u b))
  exact gF.mem_toFinset.mpr (show Function.comp _ _ q ≠ 0 from
    ((show 0<R+1-‖node (η i) q‖ by linarith).trans_le (le_max_right ..)).ne')
end Quadrature
end YM.Sextet
