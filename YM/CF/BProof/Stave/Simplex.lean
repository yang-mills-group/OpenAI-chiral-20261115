import YM.CF.BProof.Stave.Iso
/-! Affordability, actual finite-color simplex in barycentric coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Filter Topology Finset Metric -- avoid `Set.univ`
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators -- Classical?
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
abbrev Pool (I:Type*):= I→ℝ
def supp (x:Pool I):Finset I:= by classical exact univ.filter fun i=> x i≠0
variable {S T:Finset I}{x y:Pool I}{i j k:I}
omit [DecidableEq I] in
@[simp] lemma mem_supp : i∈ supp x ↔ x i ≠ 0:=by classical simp [supp]
structure Sim (S:Finset I)(x:Pool I) : Prop where
  pos (i:I) : 0≤x i
  box : supp x ⊆ S
  mass : ∑ i,x i = 1
def Sim.Park(S:Finset I):_root_.Set (Pool I):={x|Sim S x}
namespace Sim
omit [DecidableEq I] in
lemma nonempty(h:Sim S x) : S.Nonempty:= by
 classical
 by_contra q; have h0:x=0:=funext fun i=>by by_contra hm; exact q ⟨i,h.box (mem_supp.mpr hm)⟩
 have z:=h.mass; rw [h0] at z; simp at z
omit [DecidableEq I] in
lemma bounded(h:Sim S x)(i:I) : x i ≤ 1:= h.mass ▸ single_le_sum (fun i _=>h.pos i) (mem_univ i)
omit [DecidableEq I] in
lemma bound(h:Sim S x): x∈closedBall 0 1:= by rw [mem_closedBall,dist_zero_right]; exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=> by rw [Real.norm_of_nonneg (h.pos i)]; exact h.bounded _
omit [DecidableEq I] in
lemma mono(h:Sim S x)(g:S ⊆ T):Sim T x:=⟨h.pos,h.box.trans g,h.mass⟩
omit [DecidableEq I] in
lemma hall(h:Sim S x):Sim (supp x) x := ⟨h.pos,Subset.refl _,h.mass⟩
omit [DecidableEq I] in
lemma across_iff: IsCompact (Park S):=by
 classical
 refine (isCompact_closedBall 0 1).of_isClosed_subset ?_ (fun x hx=>bound (show Sim S x from hx))
 have he: Park S={x|∀ i,0≤x i} ∩ {x|∀ i,i∉S→x i=0} ∩ {x|∑ i,x i=1} := by
    ext x; change Sim S x↔(_ ∧ _) ∧ _; constructor; exact fun u=> ⟨⟨u.pos,fun i hi=> of_not_not (fun q=> hi (u.box (mem_supp.mpr q)))⟩,u.mass⟩; rintro ⟨⟨p,g⟩,U⟩; exact ⟨p,fun j hj=> of_not_not (fun q=> mem_supp.mp hj (g j q)),U⟩
 rw [he]; simp_rw [Set.setOf_forall]; exact ((isClosed_iInter (fun i=> isClosed_le continuous_const (continuous_apply i))).inter (isClosed_iInter fun i=> isClosed_iInter fun _=>isClosed_eq (continuous_apply i) continuous_const)).inter (isClosed_eq (by fun_prop) continuous_const)
-- tune
omit [DecidableEq I] in
lemma vanish(h:Sim S x)(g:i∉S): x i=0:= of_not_not (fun q=>g (h.box (mem_supp.mpr q)))
lemma shrinks(h:Sim S x)(g:x i=0):Sim (S.erase i) x:= ⟨h.pos,fun _ hj=>mem_erase.mpr ⟨fun e=>mem_supp.mp hj (e ▸ g),h.box hj⟩,h.mass⟩
lemma pure(h:i∈ S):Sim S (Pi.single i 1):=by
 refine ⟨fun j=>?_,fun j hj=>?_,?_⟩
 · by_cases g:i=j <;> simp [g,Ne.symm]
 · by_contra z; have H:j≠i:=fun e=>z (e ▸ h); exact mem_supp.mp hj (Pi.single_eq_of_ne H _)
 rw [sum_eq_single i] <;> simp <;> exact fun _ hb=>Pi.single_eq_of_ne hb _
lemma equal (h:Sim {i} x): x=Pi.single i 1:=by
 ext j; by_cases z:i=j
 · subst j; have g:=h.mass; rw [sum_eq_single i (fun j _ hj=>h.vanish (notMem_singleton.mpr hj)) (by simp)] at g; simpa using g
 rw [h.vanish (notMem_singleton.mpr (Ne.symm z)),Pi.single_eq_of_ne (Ne.symm z)]
/-- moves *all* mass at `i` to `j` -/
def gift (i j:I)(x:Pool I): Pool I:= x-Pi.single i (x i)+Pi.single j (x i)
omit [Fintype I] in
lemma coin (h:i≠ j): gift i j x i=0:=by simp [gift,Pi.single_eq_of_ne h]
omit [Fintype I] in
lemma note (h:i≠ j): gift i j x j=x j + x i:=by simp [gift,Pi.single_eq_of_ne h.symm]
omit [Fintype I] in
lemma attic (h:k≠i)(g:k≠j): gift i j x k=x k:=by simp [gift,Pi.single_eq_of_ne h,Pi.single_eq_of_ne g]
lemma gift_sim (p:Sim S x)(h:i≠j)(g:j∈ S): Sim S (gift i j x):=by
 refine ⟨fun k=>?_, fun k hk=>?_, ?_⟩
 · by_cases a:k=i; subst k; rw [coin h]; by_cases b:k=j; subst k; rw [note h]; exact add_nonneg (p.pos j) (p.pos i); rw [attic a b]; exact p.pos k
 · by_contra a; apply mem_supp.mp hk; by_cases e:k=i; subst k; exact coin h; rw [attic e (by rintro rfl; contradiction)]; exact p.vanish a
 simp only [gift,Pi.add_apply,Pi.sub_apply,sum_add_distrib,sum_sub_distrib,p.mass]; rw [sum_eq_single i (f:= Pi.single i (x i)),sum_eq_single j (f:=Pi.single j (x i))] <;> simp <;> exact fun _ hb=>Pi.single_eq_of_ne hb _
lemma gift_price (p:Sim S x)(h:i≠j) : dist x (gift i j x)= x i:=by
 rw [dist_eq_norm]; apply le_antisymm ((pi_norm_le_iff_of_nonneg (p.pos i)).mpr (fun k=>?_))
 · refine Eq.trans_le ?_ (norm_le_pi_norm _ i); change x i= ‖x i-gift i j x i‖; rw [coin h,sub_zero,Real.norm_of_nonneg (p.pos _)]
 change ‖x k-gift i j x k‖≤ x i; by_cases a:k=i
 · subst k; rw [coin h,sub_zero,Real.norm_of_nonneg (p.pos i)]
 by_cases e:k=j; subst k; rw [note h,show x j-(x j+x i)= -x i by ring]; simp [Real.norm_of_nonneg (p.pos i)]
 rw [attic a e,sub_self,norm_zero]; exact p.pos i

end Sim
end YM.CF.BProof.Mesh.Stave
