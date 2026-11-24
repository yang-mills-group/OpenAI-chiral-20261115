import YM.CF.BProof.Face

/-! Finite cover reading on the gauge faces and its margin estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Face
open Function SU Lattice Mag Filter Metric Set MeasureTheory
open scoped Matrix.Norms.Frobenius Topology Classical
local notation "G" => SU.group
variable {s : Side} (K : Chart G) (y : ℝ)

lemma separates : ∃ c : ℝ, 0<c ∧ ∀ i j, i≠j → c≤cd G (center i) (center j) := by
 classical
 let f (i : Fin 5 × Fin 5) := if i.1=i.2 then 1 else cd G (center i.1) (center i.2)
 obtain ⟨i,-,H⟩:= Finset.exists_min_image Finset.univ f Finset.univ_nonempty
 have he (j : Fin 5 × Fin 5) : 0<f j:= by unfold f; split; exact zero_lt_one; next hh=> exact (cd_pos ..).mpr (center_inj.ne hh)
 refine ⟨f i,he _,fun i j h=>?_⟩; simpa only [f,if_neg h] using H (i,j) (Finset.mem_univ _)

def labelSet (U : Sheet s) := Finset.univ.filter (fun F : Space s→Fin 5 => Lift K y U (labels K y U F))
@[simp] lemma test_label {U : Sheet s} {F} : F∈labelSet K y U ↔ Lift K y U (labels K y U F) := by simp [labelSet]

lemma propagates {P : Space s→Prop} (h : ∀ i j,P i ↔ P (i+tstep j)) (hv : P 0) (x : Space s) : P x := by
 have H (y : Site s) (v : Walk) : P (space y) ↔ P (space (stop y v)) := by
   induction v generalizing y with | nil=>rfl|cons i l ih=>
     obtain ⟨i,hb⟩:=i; rw [stop,← ih]
     refine Fin.cases ?_ (fun i=> ?_) i
     · cases hb
       · change P _ ↔ P (space (y+step 0)); rw [space_add,space_step0,add_zero]
       change P _ ↔ P (space (y+ -step 0)); rw [space_add,show space (-step 0 : Site s)=-(space (step 0)) from rfl,space_step0,neg_zero,add_zero]
     cases hb
     · exact (h (space y) i).trans (by rw [space_add]; rfl)
     rw [show (@Step.vec _ _ _ ⟨i.succ,true⟩ : Site s)=-step i.succ from rfl,space_add, show space (-step i.succ : Site s)= -(tstep i) from rfl]
     exact ((h (space y+ -tstep i) i).trans (by rw [neg_add_cancel_right])).symm -- tune
 let W:= route 0 (lift (join (0:Per s) x)) 1; have hx:= (H (wrap s 0) W).mp (show P (space (wrap s 0)) from by rw [map_zero]; exact hv)
 rw [← wrap_stop_cover, show stop 0 W=_ from route_end .., wrap_lift,space_join] at hx; exact hx

lemma fare : ∀ᶠ y:ℝ in atTop,∀ (s:Side)(U:Sheet s),(labelSet K y U).card ≤ 5 := by
 obtain ⟨c,hc,H⟩:= separates
 filter_upwards [(coin_purchases (a:=0) (b:= -1/8) (c:=0) (by norm_num)).eventually (gt_mem_nhds (show 0<c/2 from half_pos hc))] with y hy
 intro s U
 let D:=label K y U
 let S:=labelSet K y U; let x : Space s:=0
 have he : Set.InjOn (fun F : Space s→Fin 5=> F x) S := by
   intro a ha b hb h
   have hp:Lift K y U (labels K y U a):= (test_label ..).mp ha
   have hq:Lift K y U (labels K y U b):= (test_label ..).mp hb
   have hV : 2*allowance y<c := by change allowance y<_ at hy; linarith
   funext i; apply propagates (P:=fun i=> a i=b i) _ h i
   intro i j; let k:= i+tstep j
   let z := U (i,j); have ht: cd G (D k (a k)) (D i (a i)*z) ≤ allowance y:= hp.2 i j; have hz:cd G (D k (b k)) (D i (b i)*z) ≤ allowance y:= hq.2 i j
   have hh (i) : cd G (D i (a i)) (D i (b i)) < c → a i=b i := by
     intro g; by_contra h; exact (by rw [← cd_mul_right G (lead (tilt K y U i))]; exact g : cd G (center (a i)) (center (b i))<c).not_ge (H _ _ h)
   change a i=b i ↔ a k=b k
   constructor <;> intro h
   · rw [h] at ht; apply hh; apply lt_of_le_of_lt (cd_triangle G _ (D i (b i)*z) _); rw [cd_symm G (D i _ * _)]; linarith
   rw [h] at ht; apply hh; rw [← cd_mul_right G z]; apply lt_of_le_of_lt (cd_triangle G _ (D k (b k)) _); rw [cd_symm G (D i _ * _)]; linarith
 simpa using Finset.card_le_card_of_injOn (s:=S) (t:=Finset.univ) _ (by simp [Set.MapsTo]) he

/-- Default frame among the fit: closest to identity. Borel tie breaking. -/
abbrev nearest (U : Sheet s) (p : Space s) (i : Fin 5) := ∀ j,cd G (label K y U p i) 1 ≤ cd G (label K y U p j) 1
private def bestIndex (U : Sheet s) (p : Space s) : Finset (Fin 5):= Finset.univ.filter fun i => nearest K y U p i
lemma best_v (U : Sheet s) (p : Space s) : (bestIndex K y U p).Nonempty:= by
 obtain ⟨i,h,H⟩:= Finset.exists_min_image Finset.univ (fun i => cd G (label K y U p i) 1) Finset.univ_nonempty
 exact ⟨i,Finset.mem_filter.mpr ⟨h,fun i=> H i (Finset.mem_univ _)⟩⟩

def nearIndex (U : Sheet s) (p : Space s) := (bestIndex K y U p).min' (best_v ..)
lemma near_p (U : Sheet s) (p : Space s) : nearest K y U p (nearIndex K y U p) := (Finset.mem_filter.mp (Finset.min'_mem (bestIndex ..) _)).2
def orient (U : Sheet s) (p : Space s) (i : Fin 5) := center i * label K y U p (nearIndex K y U p)
lemma orient_orbit (U : Sheet s) (p : Space s) (i : Fin 5) : orbit (orient K y U p i) = orbit (lead (tilt K y U p)):= (orbit_center ..).trans (aisle ..)
lemma near_c (p : Space s) : Measurable (fun U : Sheet s=> nearIndex K y U p) := by
 have ht (i : Fin 5): Measurable (fun U : Sheet s=>cd G (label K y U p i) 1) := (show Continuous (fun v : E=>cd G v 1) by unfold cd; fun_prop).measurable.comp (label_c K y p i)
 have he (i : Fin 5) : MeasurableSet {U : Sheet s|i∈ bestIndex K y U p}:= by
    simp only [bestIndex,Finset.mem_filter,nearest,Finset.mem_univ,true_and,setOf_forall]; exact .iInter fun j=>measurableSet_le (ht i) (ht j)
 apply measurable_to_countable'
 intro i
 convert (he i).inter (MeasurableSet.iInter fun j : {j // j < i}=> (he j.val).compl) using 1
 ext x; change nearIndex K y x p∈ ({i}:Set (Fin 5)) ↔ _; simp only [mem_singleton_iff,mem_inter_iff, mem_iInter, mem_setOf_eq,mem_compl_iff]
 constructor
 · rintro rfl; refine ⟨Finset.min'_mem ..,fun j hj=>?_⟩; exact j.property.not_ge (Finset.min'_le _ _ hj)
 rintro ⟨hx,hk⟩; refine le_antisymm (Finset.min'_le _ _ hx) (le_of_not_gt fun ht=>?_); exact hk ⟨_,ht⟩ (Finset.min'_mem _ (best_v K y x p))
end YM.CF.BProof.Face
