import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import YM.SU5.FiniteGaugeData.Tower.Accord
/-!
# Sampling cube
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Set Filter MeasureTheory Metric Function
open Vacancy
open scoped Classical Topology NNReal ENNReal
section dimension
variable {I : Type*} [Fintype I]
local notation "S"=> I→ℝ
variable (n:ℕ) (h:0<n)
abbrev UBox (I:Type*) := Set.Icc (0:I→ℝ) 1
abbrev OBox (I:Type*): Set (I→ℝ):= pi Set.univ fun _=> Set.Ico 0 1
lemma halfBox : OBox I ⊆ UBox I:=fun _ hx=>⟨fun i=> (hx i (Set.mem_univ _)).1,fun i=> (hx i (Set.mem_univ _)).2.le⟩
def smallCorner (i:I→ Fin n) : I→ℝ :=fun a=> ((i a).val:ℝ)/n
def bigCorner (i:I→ Fin n) : I→ℝ:=fun a=> (((i a).val:ℝ)+1)/n
def nearBox (i:I→Fin n): Set (I→ℝ):= pi Set.univ (fun a=> Ico (smallCorner n i a) (bigCorner n i a))
include h
lemma walls (i:I→Fin n) : smallCorner n i ≤ bigCorner n i ∧ bigCorner n i≤ (1:I→ℝ) ∧ 0 ≤ smallCorner n i:= by
 have e:0<(n:ℝ):=by exact_mod_cast h
 refine ⟨fun a=> ?_,fun a=> ?_, fun a=>?_⟩
 · unfold smallCorner bigCorner; gcongr; simp
 · unfold bigCorner; change _≤1; rw [div_le_one e]; exact_mod_cast (i a).isLt
 unfold smallCorner; change 0≤_; positivity
lemma corner_in_box (i:I→Fin n): smallCorner n i∈ nearBox n i:= by
 intro a _ ; change _ ≤ _ ∧ smallCorner n i a < bigCorner n i a; refine ⟨le_refl _,?_⟩; unfold smallCorner bigCorner; gcongr; norm_cast; omega
lemma nearBox_inside (i:I→ Fin n): nearBox n i⊆OBox I := by
 intro x hx a w; exact ⟨((walls n h i).2.2 a).trans (hx a w).1,lt_of_lt_of_le (hx a w).2 ((walls n h i).2.1 a)⟩
lemma nearBox_union : ⋃ i:I→ Fin n,nearBox n i=OBox I:=by
 refine Set.Subset.antisymm (iUnion_subset fun i=>nearBox_inside n h i) ?_
 intro x hx
 let f(i:I):= (x i)*(n:ℝ)
 have e:0<(n:ℝ):=by exact_mod_cast h
 have h0(i:I):0 ≤ f i:=mul_nonneg (hx i (Set.mem_univ _)).1 (by positivity)
 have h1(i:I):f i < n:= lt_of_lt_of_le (mul_lt_mul_of_pos_right (hx i (Set.mem_univ _)).2 e) (by rw [one_mul])
 have hy(i:I) := Nat.floor_le (h0 i)
 let v(i:I):Fin n:=⟨⌊ f i⌋₊,by exact_mod_cast lt_of_le_of_lt (hy i) (h1 i)⟩
 apply mem_iUnion.mpr; exact ⟨v,fun i _=> ⟨(div_le_iff₀ e).mpr (hy i),(lt_div_iff₀ e).mpr (Nat.lt_floor_add_one (f i))⟩⟩
lemma nearBox_ind (i:I→Fin n) (j:I→Fin n) (h' : i ≠ j): Disjoint (nearBox n i) (nearBox n j) := by
 apply Set.disjoint_left.mpr; intro x a b
 apply h'; funext k
 have a(k): (i k).val≤ (j k).val:=by
    by_contra! t
    have h0: ((j k).val:ℝ)+1 ≤ ((i k).val:ℝ) := by exact_mod_cast t
    exact lt_irrefl (x k) (((b k (Set.mem_univ _)).2).trans_le (le_trans (div_le_div_of_nonneg_right h0 (by positivity)) ((a k (Set.mem_univ _)).1)))
 apply Fin.ext; apply le_antisymm (a k)
 -- shadow rename
 by_contra! t
 have h0: ((i k).val:ℝ)+1 ≤ ((j k).val:ℝ) := by exact_mod_cast t
 exact lt_irrefl (x k) (((by assumption : x ∈ nearBox n i) k (Set.mem_univ _)).2|>.trans_le (le_trans (div_le_div_of_nonneg_right h0 (by positivity)) ((b k (Set.mem_univ _)).1)))
lemma spans (i:I→Fin n) (a:I) : bigCorner n i a - smallCorner n i a = (n:ℝ)⁻¹:=by unfold bigCorner smallCorner; ring
lemma nearBox_amount (i:I→Fin n): volume.real (nearBox n i)=(Fintype.card (I→Fin n):ℝ)⁻¹:=by
 unfold Measure.real nearBox; rw [Real.volume_pi_Ico_toReal (walls n h i).1]; simp [spans n h] -- includes DecidableEq needed? open Classical
lemma nearBox_measurable (i:I→Fin n): MeasurableSet (nearBox n i):=by
 apply MeasurableSet.univ_pi; exact fun _=> measurableSet_Ico
lemma nearBox_cap (i:I→Fin n): volume (nearBox n i) < ⊤:= (measure_mono ((nearBox_inside n h i).trans halfBox)).trans_lt isCompact_Icc.measure_lt_top
lemma nearBox_small (i:I→Fin n){x:I→ℝ}(hx:x∈ nearBox n i): dist (smallCorner n i) x ≤ (n:ℝ)⁻¹:= by
 refine (dist_pi_le_iff (by positivity)).mpr fun k=> ?_
 rw [dist_comm,Real.dist_eq]; have hv:=hx k (Set.mem_univ _); rw [abs_of_nonneg (sub_nonneg.mpr hv.1),←spans n h i k]; exact sub_le_sub_right hv.2.le _
end dimension

section calculus
variable {I : Type*}[Fintype I]{X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
    [NormedSpace ℝ X][IsScalarTower ℝ ℂ X]
variable (F:(I→ℝ) →X) (p:ContinuousOn F (UBox I))
local notation "ν"=> volume.restrict (OBox I)
include p
lemma desk_price {δ ε:ℝ} (a:0 ≤ε) (g':∀ x∈ UBox I,∀ y∈ UBox I, dist x y ≤δ→ dist (F x) (F y) ≤ ε) (n:ℕ)(h:0<n)(hp:(n:ℝ)⁻¹≤δ):
    ‖Average.center (fun i:I→Fin n=> F (smallCorner n i))-(∫ x,F x ∂ν)‖ ≤ ε:=by
 let C (i:I→Fin n):=nearBox n i; let m:=Fintype.card (I→Fin n)
 let W(i:I→Fin n):=F (smallCorner n i)
 have hf(i):IntegrableOn F (C i):=(p.integrableOn_compact isCompact_Icc).mono_set ((nearBox_inside n h i).trans halfBox)
 have hv(i:I→Fin n): IntegrableOn (fun _=> W i) (C i):=integrableOn_const (μ:=volume) (nearBox_cap n h i).ne
 have hm:0 < m:=by
    have hx : Nonempty (I→Fin n):= ⟨fun _=> ⟨0,h⟩⟩; exact Fintype.card_pos
 have hC : Average.center W= ∑ i:I→ Fin n, ∫ x in (C i),(fun _=> W i) x :=by
    unfold Average.center; rw [Finset.smul_sum]; refine Finset.sum_congr rfl (fun i _=>?_)
    rw [setIntegral_const,show volume.real (C i)=(m:ℝ)⁻¹ from nearBox_amount n h i, ← IsScalarTower.algebraMap_smul ℂ (m:ℝ)⁻¹, map_inv₀, map_natCast]
 have hJ : (∫ x, F x ∂ν)=∑ i:I→ Fin n, ∫ x in (C i), F x:= by rw [←nearBox_union n h]; exact integral_iUnion_fintype (nearBox_measurable n h) (fun i j=> nearBox_ind n h i j) hf
 change ‖Average.center W-_‖≤_
 rw [hC,hJ,← Finset.sum_sub_distrib]; apply le_trans (norm_sum_le ..)
 calc
 _ ≤ ∑ _ : I→ Fin n, ε*(m:ℝ)⁻¹:= by
    apply Finset.sum_le_sum; intro i w
    rw [← integral_sub (hv i) (hf i), show ε*(m:ℝ)⁻¹= ε*volume.real (C i) by rw [show volume.real (C i)=_ from nearBox_amount n h i]]
    refine norm_setIntegral_le_of_norm_le_const (nearBox_cap n h i) fun x a=> ?_
    rw [←dist_eq_norm]; exact g' _ (halfBox (nearBox_inside n h i (corner_in_box n h i))) _ (halfBox (nearBox_inside n h i a)) ((nearBox_small n h i a).trans hp)
 _= ε:= by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change (m:ℝ)*_=ε; field_simp
lemma center_tends : Tendsto (fun n:ℕ => Average.center (fun i:I→Fin n=> F (smallCorner n i))) atTop (𝓝 (∫ x,F x ∂ν)):=by
 apply Metric.tendsto_nhds.mpr
 intro ε e; obtain ⟨d,hd,h⟩:= Metric.uniformContinuousOn_iff.mp (IsCompact.uniformContinuousOn_of_continuous isCompact_Icc p) (ε/2) (half_pos e)
 have he:Tendsto (fun n:ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
 filter_upwards [he.eventually (gt_mem_nhds hd),eventually_gt_atTop (0:ℕ)] with s (v:(s:ℝ)⁻¹<d) t
 rw [dist_eq_norm]; exact lt_of_le_of_lt (desk_price F p (half_pos e).le (fun _ hx _ hy H=> (h _ hx _ hy (H.trans_lt v)).le) s t (le_refl _)) (half_lt_self e)
end calculus
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.center_tends
