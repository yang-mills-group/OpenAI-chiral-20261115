import YM.CF.Lattice.Tenant

/-! Establish the explicit row rates for the input kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Finset Function Fock Filter NormedSpace SU Lat Lattice Branch Cube
attribute [local instance] opCStarAlgebra
variable {N : Side}
lemma detour (x : Site N) (i : Axis) : separation (node x) (node (x+step i)) ≤ 2 := by
  rw [after]; exact (separation_triangle _ (node x+step i) _).trans (Nat.add_le_add (oneTouch _ _) (oneTouch _ _))
variable (c : Site N)
lemma hopper (S : Seal (Site (More N))) (x y : Input N) {i : Edges (More N)} (h : i∈leaks S) : ‖color matter (x.1 i)-color matter (y.1 i)‖≤ vacancy S x y := (single_le_sum (f:=fun i=>‖color matter (x.1 i)-color matter (y.1 i)‖) (fun _ _=>norm_nonneg _) h).trans (le_add_of_nonneg_right (sum_nonneg (fun _ _ => sum_nonneg (fun _ _=>norm_nonneg _))))
lemma blade (S : Seal (Site (More N))) (x y : Input N) (j : Bool) {i : Site N} (h : i∈news S) : ‖localPair (x.2 j i)-localPair (y.2 j i)‖≤ vacancy S x y := by
  unfold vacancy
  calc _ ≤ _ := single_le_sum (f:=fun i=> ‖localPair (x.2 j i)-localPair (y.2 j i)‖) (fun _ _=>norm_nonneg _) h
       _ ≤ _ := single_le_sum (f:=fun j=> ∑ i∈news S, ‖localPair (x.2 j i)-localPair (y.2 j i)‖) (fun _ _=>sum_nonneg fun _ _=>norm_nonneg _) (mem_univ j)
       _ ≤ _ := le_add_of_nonneg_left (sum_nonneg fun _ _=> norm_nonneg _)
lemma hop_rate (x y : Own N) (i : Axis) (a : Site N) :
    let S := bay (terr _) (node a) 2
    ‖hop matter (rough N x) c i a - hop matter (rough N y) c i a‖ ≤ 2*vacancy S x.val y.val := by
  intro S; let b := (node a,i); let d : Edges (More N) := (node a+step i,i)
  let A := fun (x:Own N) z=> color matter (x.val.1 z)
  have he (x:Own N) : hop matter (rough N x) c i a=seam c a i • (A x b*A x d) := by rw [hop,show rough N x (a,i)=x.val.1 b*x.val.1 d from rfl,color_mul]
  rw [he,he,←smul_sub, norm_smul,seam_norm, one_mul];
  have hB : b∈leaks S := by
    unfold b leaks; rw [mem_filter]; refine ⟨mem_univ _,(bay_mem _).mpr ?_,(bay_mem _).mpr ?_⟩
    · simp [terr]
    exact (oneTouch ..).trans (by omega)
  have hT : d∈leaks S := by
    apply mem_filter.mpr; refine ⟨mem_univ _,(mem_filter.mp hB).2.2,?_⟩
    apply (bay_mem _).mpr; change separation (node a) (node a+step i+step i) ≤ _; rw [←after]; exact detour a i
  rw [show A x b * A x d-A y b*A y d=(A x b-A y b)*A x d+A y b*(A x d-A y d) by rw [mul_sub,sub_mul]; abel]
  have hp (x:Own N) i : ‖A x i‖=1 := CStarRing.norm_of_mem_unitary (color_mem ..)
  rw [two_mul]; apply (norm_add_le ..).trans; apply add_le_add <;> apply (norm_mul_le ..).trans
  · rw [hp,mul_one]; exact hopper _ _ _ hB
  rw [hp,one_mul]; exact hopper _ _ _ hT
abbrev fee (a K : ℝ) (b : ℕ) := quota*((b:ℝ)+1)^4*Real.exp (a*(quota*((b:ℝ)+1)^4))*K
lemma shift_fee (a : ℝ) (p : 0≤a) (i : Axis) : RootedK (sigK N) (sigK N) a (fee a 2 2) (fun x:Own N=>shift matter (rough N x) c i) := by
  let S := fun x:Own N=>shift matter (rough N x) c i
  have H : Inter (sigK N) (sigK N) S := by
    intro g x; let t := g ∘ node (N:=N)
    change shift _ (links (gauge g x.val.1)) _ _ * _=_; rw [links_g,twist_shift]; exact twist_product ..
  have he : Continuous (fun x:Own N=> rough N x) := (links_cont (N:=N)).comp (continuous_fst.comp continuous_subtype_val)
  have hs : Continuous S := (shift_cont matter _ matter_cont i).comp he
  refine row_earn (ample_slots N) ((show (0:ℝ)≤16 by norm_num).trans quota_bound) p H hs (show (0:ℝ)≤2 by norm_num) 2 ?_ ?_ ?_
  · rintro x ⟨u,j⟩ ⟨v,k⟩ l; have he : advance i u ≠ v := by
      change 2<separation (node u) (node v) at l; intro h; subst v; exact not_lt_of_ge (detour u i) l
    simp [S,shift,jump_apply,he]
  · intro q r k; apply (norm_entry ..).trans; rw [show ‖S k‖=1 from CStarRing.norm_of_mem_unitary ((frame matter (rough N k) c).shiftU _)]; norm_num
  rintro ⟨u,i₁⟩ ⟨v,i₂⟩ x y
  unfold S shift; by_cases l:advance i u=v
  · simp only [jump_apply,l,ite_true]; exact (norm_entry (hop matter (rough N x) c i u-hop matter (rough N y) c i u) i₁ i₂).trans (hop_rate c x y i u)
  simp only [jump_apply,if_neg l,sub_self,norm_zero]; exact mul_nonneg (by norm_num) (vacancy_pos ..)
lemma static_fee (a : ℝ) (N : Side) (A : Op SpinIdx) (p : 0≤a) : RootedK (sigK N) (sigK N) a (fee a ‖A ⊗ₖ (1:Op Slot)‖ 0) (fun _:Own N=>spin N Slot A) := by
  let S : Own N → Op (Model N) := fun _=>spin N Slot A
  have H : Inter (sigK N) (sigK N) S := by intro g x; let U := conjG matter (g ∘ node (N:=N)); change S x * U.val= _; exact (congrArg (· * U.val) (twist_spin (N:=N) matter (g ∘ node) A)).symm.trans (twist_product ..) -- tune
  refine row_earn (ample_slots N) ((show (0:ℝ)≤16 by norm_num).trans quota_bound) p H continuous_const (norm_nonneg _) 0 ?_ ?_ ?_
  · intro x i j h; have he : i.1≠j.1 := by
      change 0<separation (node i.1) (node j.1) at h; intro hx; rw [hx,separation_self] at h; omega
    simp [S,spin,jump_apply,he]
  · intro i j x; exact (norm_entry ..).trans (jump_bound _ _ (norm_nonneg _) (fun _=>le_rfl))
  intro i j x y; simp only [S,sub_self,norm_zero]; exact mul_nonneg (norm_nonneg _) (vacancy_pos ..)
lemma C_fee (a : ℝ) (p : 0≤a) (j : Bool) (N : Side) : RootedK (sigK N) (sigK N).reverseV a (fee a 1 0) (fun x:Own N=> snow N x j) := by
  let F : Own N→Op (Model N) := fun x=>snow N x j
  have H : Inter (sigK N) (sigK N).reverseV F := by
    intro g x; let U := conjG matter (g ∘ node (N:=N))
    have he : F ((slotK N).drive g x)=congrC U (F x) := C_gauge ..
    rw [he]; exact congr_product ..
  have h₁ : Continuous F := C_cont.comp ((continuous_apply j).comp (continuous_snd.comp continuous_subtype_val))
  refine row_earn (ample_slots N) ((show (0:ℝ)≤16 by norm_num).trans quota_bound) p H h₁ zero_le_one 0 ?_ ?_ ?_
  · intro x i k h; have he : i.1≠k.1 := by
      change 0<separation (node i.1) (node k.1) at h; intro e; rw [e,separation_self] at h; omega
    simp [F,snow,Cfield,jump_apply,he]
  · intro i k x; exact (norm_entry ..).trans (le_of_eq (CStarRing.norm_of_mem_unitary (C_unit _ (x.property.unit j))))
  intro i k x y; unfold F snow Cfield; rw [one_mul]; simp only [jump_apply,Equiv.refl_apply]; split
  · exact (norm_entry (localPair (x.val.2 j i.1)-localPair (y.val.2 j i.1)) ..).trans (blade _ x.val y.val j (show i.1∈news (bay (terr _) (node i.1) 0) by simp [news,terr]))
  rw [sub_self,norm_zero]; exact vacancy_pos ..
end YM.CF.Tenant
