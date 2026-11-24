import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Quantitative covering and sphere-avoidance prices. Used to implement the manuscript's
uniform Lipschitz extension steps without importing topological homotopy axioms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension
open MeasureTheory Measure Filter Metric Set Module
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace
section Balls
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

lemma mesh (S : Set X) {r K : ℝ} (hr : 0 < r) (hk : 0 < K) (hs : S ⊆ closedBall 0 K) (h : r≤K) :
    ∃ i : Finset X, (i:Set X) ⊆ S ∧ (i.card:ℝ) ≤ (4*K/r)^finrank ℝ X ∧
      ∀ x∈S,∃ y∈i,dist x y ≤ r := by
 classical
 letI := FiniteDimensional.proper ℝ X; letI := borel X; letI : BorelSpace X:=⟨rfl⟩; let μ : Measure X := Measure.addHaar
 haveI : IsAddHaarMeasure μ:=by unfold μ; infer_instance
 let b:=μ.real (ball 0 1); have hb : 0<b := ENNReal.toReal_pos (IsOpen.measure_pos μ isOpen_ball (nonempty_ball.mpr zero_lt_one)).ne' measure_ball_lt_top.ne -- tune
 let Z(i:Finset X) := (i:Set X).Pairwise (fun x y=> r < dist x y)
 have ht(i:Finset X)(hp : (i:Set X)⊆S)(hv:Z i): (i.card:ℝ) ≤ (4*K/r)^finrank ℝ X := by
   let T(x:X):=closedBall x (r/2)
   have hw : ⋃ x∈ i,T x ⊆ closedBall 0 (2*K):=by
     refine iUnion₂_subset fun x hx y hy => ?_; rw [mem_closedBall]; have hl := (dist_triangle y x 0).trans (add_le_add hy (hs (hp hx))); linarith -- tune
   have hu:(i:Set X).PairwiseDisjoint T := fun x hx y hy g => by
     apply Set.disjoint_left.mpr; intro z za zb; have h0:= hv hx hy g; have he:= (dist_triangle_left x y z).trans (add_le_add za zb); linarith
   have hx:= measureReal_mono (μ:=μ) hw measure_closedBall_lt_top.ne; rw [measureReal_biUnion_finset hu (fun i _=>isClosed_closedBall.measurableSet) (fun i _=>measure_closedBall_lt_top.ne),addHaar_real_closedBall μ _ (by positivity)] at hx
   unfold T at hx; simp_rw [addHaar_real_closedBall μ _ (by positivity : 0≤r/2)] at hx; simp only [Finset.sum_const,nsmul_eq_mul] at hx
   apply le_of_mul_le_mul_right (a:=(r/2)^finrank ℝ X*b) _ (by positivity)
   refine hx.trans (le_of_eq ?_); rw [←mul_assoc,←mul_pow,show 4*K/r*(r/2)=2*K by field_simp; ring]
 by_contra h0; push Not at h0
 have H (n : ℕ) : ∃ i : Finset X, (i:Set X) ⊆ S ∧ Z i ∧ i.card=n := by
   induction n with | zero=> exact ⟨∅,by simp,by unfold Z; simp,rfl⟩|succ n ih=>
    obtain ⟨i,a,d,e⟩:=ih; obtain ⟨j,jh,hh⟩:=h0 i a (ht i a d)
    have hu : j∉i:=fun p=> by have := hh j p; rw [dist_self] at this; linarith
    refine ⟨insert j i,by rw [Finset.coe_insert,insert_subset_iff]; exact ⟨jh,a⟩,?_,by simp [hu,e]⟩
    intro x hx y hy hz; rcases Finset.mem_insert.mp hx with rfl|g <;> rcases Finset.mem_insert.mp hy with rfl|l
    · exact False.elim (hz rfl)
    · exact hh y l
    · rw [dist_comm]; exact hh x g
    exact d g l hz
 obtain ⟨n,hn⟩:= exists_nat_gt ((4*K/r)^finrank ℝ X); obtain ⟨i,a,w,v⟩:= H n; exact hn.not_ge (v ▸ ht i a w)
end Balls

section Avoid
open Submodule
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

lemma affineTube [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsAddHaarMeasure μ] (V : Submodule ℝ Y) (y : Y) {r : ℝ} (hr : 0<r) (hu : r≤1) :
    μ.real {x | ‖x‖≤1 ∧ ‖V.starProjection x-y‖≤r} ≤ 8^finrank ℝ Y * r^finrank ℝ V * μ.real (ball 0 1) := by
 classical
 obtain ⟨T,hT,H,pT⟩:= mesh (closedBall (0: ↥(Vᗮ)) 1) hr zero_lt_one (Subset.refl _) hu
 let f (x : ↥(Vᗮ)) : Set Y:=closedBall ((x:Y)+y) (2*r)
 let b:= μ.real (ball 0 1)
 letI := FiniteDimensional.proper ℝ Y
 have hb :0≤b:= ENNReal.toReal_nonneg
 have he : {x| ‖x‖≤1 ∧ ‖V.starProjection x-y‖≤r} ⊆ ⋃ i∈T, f i := by
   rintro x ⟨hx,hw⟩; let v:= Vᗮ.orthogonalProjectionOnto x
   obtain ⟨i,hi,h⟩:=pT v (by rw [mem_closedBall,dist_zero_right]; exact (Vᗮ.norm_orthogonalProjectionOnto_apply_le x).trans hx)
   have hz : (v:Y)+V.starProjection x=x := by rw [add_comm]; exact V.starProjection_add_starProjection_orthogonal x
   refine mem_iUnion₂.mpr ⟨_,hi,mem_closedBall.mpr ((hz ▸ dist_add_add_le ((v:Y)) _ i.val y).trans ?_)⟩ -- tune
   rw [dist_eq_norm (V.starProjection x)]; have hv : dist (v:Y) i.val≤r:=h; linarith
 have hX:= measureReal_mono (μ:=μ) he ((T.isCompact_biUnion (fun i _=> isCompact_closedBall ..)).measure_lt_top).ne -- tune
 refine le_trans (hX.trans (measureReal_biUnion_finset_le (μ:=μ) T f)) ?_
 unfold f; simp only [Measure.addHaar_real_closedBall μ _ (by positivity : 0 ≤ 2*r), Finset.sum_const,nsmul_eq_mul]
 apply le_trans (mul_le_mul_of_nonneg_right H (by positivity))
 let a:= finrank ℝ V; let k:= finrank ℝ (Vᗮ)
 have he : finrank ℝ Y=a+k:= V.finrank_add_finrank_orthogonal.symm
 simp only [mul_one] -- tune
 rw [he]; change (4/r)^k*((2*r)^(a+k)*b)≤8^(a+k)*r^a*b
 calc
   _ = 2^a*8^k*r^a*b:=by rw [pow_add,mul_pow,mul_pow,div_pow,show (8:ℝ)=4*2 by norm_num,mul_pow]; field_simp
   _ ≤ _:= by rw [pow_add]; gcongr; norm_num
end Avoid
end YM.CF.BProof.Extension
