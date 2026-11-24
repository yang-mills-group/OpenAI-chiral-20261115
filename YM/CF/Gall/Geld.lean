import YM.CF.Gall.Faun
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gall
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{A:Op n}{p q:Wave n}{k v C d b w:ℝ}
def dialZ(x:Ket n):=∑ i,‖x.ofLp i‖
lemma Pays.url(x:Ket n)(g:Bool)(p:0≤k): Pays k (creed g x) (dialZ x*k):=by
 unfold dialZ; rw [sum_mul]; cases g
 · change Pays k (create x) _; rw [create_def]; exact Pays.sumT _ _ _ fun i _=> (Pays.linear (show Pays k (put i) k by simpa [Gall.pack,artW,ton,creed] using Pays.tone (false,i) p) _)
 change Pays k (remove x) _; rw [remove_def]; refine Pays.sumT _ _ _ fun i _=> ?_; nth_rw 1 [←norm_star (x.ofLp i)]; exact Pays.linear (show Pays k (takeF i) k by simpa [Gall.pack,artW,ton,creed] using Pays.tone (true,i) p) _ -- tune
lemma Pays.rollP {I:Type*}(A:I→FC n)(u:List I)(g:∀ i,Pays k (A i) b): Pays k (rollC A u) (b^u.length):=by induction u with | nil=> simp only [rollC,List.map_nil,List.prod_nil,List.length_nil,pow_zero]; exact Pays.uno| cons i u ih=> rw [rollC,List.map_cons,List.prod_cons,List.length_cons,pow_succ']; exact (g i).mul ih
lemma Yep.low(g:Yep k p q b): ‖inner ℂ p q‖ ≤ b:=by simpa [rollC,costs] using g []
lemma Yep.jetF(g:Yep k p q b)(e:0≤k)(u:0≤b)(U:UNI n)(h:∀ i:n,dialZ (acts (star U.val) (basisKet i)) ≤ C):Yep (C*k) (Pic.Fone U p) (Pic.Fone U q) b:=by
 intro i; let B(t:WordX n):= Pic.whisk (star U) (artW t); let X:= i.map B; have he:X.map (Pic.whisk U)=i.map artW:=by unfold X; rw [List.map_map,show Pic.whisk U ∘ B=artW from funext fun i=>Prod.ext rfl (act_starUnit U _)]
 rw [show rollC Gall.pack i=rollC ton (i.map artW) by simp only [rollC,List.map_map]; rfl, ←he, Pic.kgreen]; rw [show inner ℂ (Pic.Fone U p) (Pic.Fone U _)= _ from act_unit_inner (quantU U) _ _]; unfold X; rw [show rollC ton (i.map B)=rollC (ton∘B) i by simp only [rollC,List.map_map]]; unfold costs; rw [mul_comm b]; refine ((Pays.rollP (ton∘B) i ?_).2 _ _ b u g).low; intro i; exact (Pays.url _ i.1 e).weigh (mul_le_mul_of_nonneg_right (h i.2) e) e
variable {N:Side}
lemma lurk_n(g:Site (More N)→E)(i:Single N): dialZ (acts (star (tradew N g).val) (basisKet i)) ≤ 45 :=by
 unfold dialZ; rw [Fintype.sum_prod_type]; let U:= tradew N g; have ht : ∀ j:Single N, ‖(acts (star U.val) (basisKet i)).ofLp j‖ ≤ 1:=fun j=>by rw [basis_act]; exact (norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary ((star U).property)) -- tune
 rw [sum_eq_single i.1]; · refine le_trans (sum_le_sum (g:=fun _=>1) (fun j _=>ht (i.1,j))) ?_; rw [sum_const,card_univ,slots]; norm_num
 · intro z hz w; refine sum_eq_zero fun x _=>?_ ; rw [basis_act,Matrix.star_apply]; change ‖star (jump _ _ _ _)‖=_; rw [jump_apply,Equiv.refl_apply,if_neg (show i.1≠ (z,x).1 from Ne.symm w),star_zero,norm_zero] -- orientation
 simp
end YM.CF.Gall
