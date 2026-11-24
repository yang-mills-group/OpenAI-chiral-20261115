import YM.SU5.FiniteGaugeData.ArchiveK.Tumble
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open MeasureTheory.Measure
namespace Violas
open LinearMap Submodule Module
variable {X Y Z J:Type*}[Fintype X][Fintype Y][Fintype Z][Fintype J][DecidableEq X][DecidableEq Y][DecidableEq Z][DecidableEq J]{u:ℕ}
lemma xy_price (x:Ket X) (i:X) : ‖x i‖ ≤ ‖x‖:= by rw [←basis_inner]; simpa using norm_inner_le_norm (𝕜:=ℂ) (basisKet i) x
lemma mTouch (M:Ruler X Y)(i j): ‖M i j‖ ≤ ‖M‖:= le_trans (R_basis i j M ▸ xy_price _ i) (by simpa using (R_cost M (basisKet j))) -- tune
lemma jungle(x:Ket X) (c:ℝ)(p:∀ i:X, ‖x i‖ ≤ c): ‖x‖ ≤ (page X:ℝ)*c:= by nth_rw 1 [←basis_expand x]; exact le_trans (norm_sum_le ..) ((sum_le_sum (g:=fun _=>c) (fun i _=> (by simpa [norm_smul] using p i))).trans_eq (by simp [page]))
lemma jingle (M:Ruler X Y)(c:ℝ)(p:0≤c)(h:∀ (i:X)(j:Y), ‖M i j‖≤c) : ‖M‖≤(page X:ℝ)*page Y * c:= by
 rw [←R_pay]; apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro z
 refine (jungle _ ((page Y:ℝ)*c*‖z‖) (fun i=>?_)).trans_eq (by ring); rw [R_at]; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun j:Y=> c * ‖z‖) (fun j _=>?_)).trans_eq ?_; · rw [norm_mul]; exact mul_le_mul (h i j) (xy_price z j) (norm_nonneg _) p
 simp [page]; ring
section transfer
def blue (f:X≃Y): Ket X ≃ₗ[ℂ] Ket Y where
 toFun x:= toLp 2 fun i=> x (f.symm i)
 invFun x:= toLp 2 fun i=> x (f i)
 left_inv x:=by apply PiLp.ext; intro; simp
 right_inv x:=by apply PiLp.ext; intro; simp
 map_add' x y:= rfl
 map_smul' c x:= rfl
lemma blue_at (x:Ket X)(i:X)(f:X≃Y) : (blue f x).ofLp (f i)=x i:=by unfold blue; simp
lemma blue_flick(f:X≃Y)(A:Op X)(x:Ket X) : gas A x=gas (Matrix.reindex f f A) (blue f x):= by
 unfold gas; simp_rw [Midway.GramK.grow]; apply congrArg Complex.re; have hp(i j:X): Matrix.reindex f f A (f i) (f j)=A i j:=by simp; -- `eq` simp
 rw [← Equiv.sum_comp f (fun i:Y=>∑ j:Y, _)] -- placeholder inference. tune
 refine sum_congr rfl fun i _=>?_ ; rw [← Equiv.sum_comp f]; apply sum_congr rfl; intro j _; rw [blue_at,blue_at,hp]
lemma blue_size(f:X≃Y) (x:Ket X) : ‖blue f x‖= ‖x‖:= by rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]; rw [←Equiv.sum_comp f]; simp_rw [blue_at]
lemma blue_cost(f:X≃Y)(A:Op X)(K:Op Y)(S:PlansM X)(g:ℝ)(h:∀ i∈ S,g*‖i‖^2 ≤ gas A i)(p:∀ i j:X,K (f i) (f j)=A i j) : dim (S.map (blue f).toLinearMap)=dim S ∧ ∀ i∈ S.map (blue f).toLinearMap,g*‖i‖^2 ≤ gas K i := by
 refine ⟨LinearEquiv.finrank_map_eq ..,fun i v=>?_⟩; obtain ⟨j,v,rfl⟩:= v; change g*‖blue f j‖^2 ≤ _; have he(y:Ket Y) : gas K y=gas (Matrix.reindex f f A) y:=by rw [show K= _ from ?_]; apply Matrix.ext; intro a b; obtain ⟨a,rfl⟩:= f.surjective a; obtain ⟨b,rfl⟩:= f.surjective b; rw [p]; simp; -- tune implicit p.
 change _≤ gas K (blue f j); rw [blue_size,he,← blue_flick]; exact h j v
end transfer
section kernelBills
-- approx rank budget using block product J. codimension modules.Q. want dim ≥ X*K with `page J≥something`: Q rational cost at any. lemma expresses `page(J×X)≤ 2*(u + dim U)` u budget rank dims high.L later simplify.
local notation "Υ"=> J×X
def play(P: J→Op X) : Op (J×X):= jump (Equiv.refl J) P
local notation "ℙ"=> PlansM (J× X)
abbrev brake (x:Ket (J×X))(j:J): Ket X:= WithLp.toLp 2 fun i=> x (j,i)
lemma jumps(P:J→Op X)(x:Ket (J×X)): gas (play P) x=∑ j:J,gas (P j) (brake x j):=by
 unfold gas; simp_rw [Midway.GramK.grow,Complex.re_sum]; simp_rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [Finset.sum_eq_single i]; unfold play; simp_rw [jump_apply,Equiv.refl_apply,if_true] -- tune
 · intro x hx v; -- don't shadow
   unfold play; simp_rw [jump_apply,Equiv.refl_apply,if_neg (Ne.symm v),zero_mul]; simp
 simp
lemma range_golem (A:J→PlansM X) : ∃ P: PlansM (J×X), dim P=∑ j,dim (A j) ∧ ∀ x∈ P,∀ i,brake x i∈ A i:=by
 let f: ((i:J)→ A i) →ₗ[ℂ] Ket (J×X):={ toFun:=fun x=>toLp 2 fun i=> ((x i.1).val).ofLp i.2,map_add':=by intros;rfl,map_smul':=by intros;rfl }
 have he(x: (i:J)→ A i) (i:J) : brake (f x) i=(x i).val:=rfl
 refine ⟨LinearMap.range f,(LinearEquiv.finrank_eq (LinearEquiv.ofInjective f (fun i j v=> funext (fun a=>Subtype.ext (congrArg (fun z=>brake z a) v))))).symm.trans (Module.finrank_pi_fintype _),fun x h i=>?_⟩
 obtain ⟨z,rfl⟩:= h; rw [he]; exact (z i).property
lemma brakeP (x:Ket (J×X)) : ‖x‖^2= ∑ i,‖brake x i‖^2:=by simp_rw [EuclideanSpace.norm_sq_eq]; rw [Fintype.sum_prod_type]
lemma golem (A:J→Op X)(a:ℝ)(h:∀ i:J,∃ U:PlansM X,page X ≤ 2*dim U ∧ ∀ z∈ U,a*‖z‖^2 ≤ gas (A i) z) : ∃ V:PlansM (J×X),page (J×X) ≤2*dim V∧ ∀ z∈ V,a*‖z‖^2 ≤ gas (play A) z:=by
 choose U t T using h; obtain ⟨V,v,P⟩:= range_golem U; refine ⟨V,?_,fun z e=>?_⟩; · rw [v,Finset.mul_sum]; exact (le_of_eq (b:=∑ i:J,page X) (by simp [page])).trans (sum_le_sum fun i _=>t i)
 rw [jumps,brakeP,Finset.mul_sum]; apply sum_le_sum (fun i _=>T i _ (P z e i))
structure Cast (Z:Type*) [Fintype Z] [DecidableEq Z] (A:Ruler X Y)(c:ℝ) :Prop where
 sales: ∃ X :Ruler X Z,∃ Y:Ruler Z Y,∀ i j, ‖A i j - (X*Y) i j‖ ≤ c -- Shadow issue
abbrev farm(j:J)(A:Op (J × X)):Op X:= A.submatrix (fun i:X=>(j,i)) (fun i:X=>(j,i))
abbrev parch(i j:J)(A: Op (J× X)) :Op X := A.submatrix (fun u=>(i,u)) (fun u=>(j,u))
-- craft.PICK codim loss.Norm_cost S. all pairs i ≠. bound residual per engine matrix not needing factor J² since errors in disjoint blocks to sup entry.Right.
lemma crawl (A : Op (J×X))(Z:Type*) [Fintype Z][DecidableEq Z] (x c:ℝ)(t:0≤ c)(H:∀ i j : J,i≠ j→ Cast Z (parch i j A) c) (D:∀ i:J,∃ U:PlansM X,page X ≤2*dim U∧∀ z∈U,x*‖z‖^2 ≤ gas (farm i A) z) :
 ∃ U: PlansM (J× X),page (J×X) ≤ 2*(dim U+page J^2 *page Z)∧ ∀ v∈U,(x-(page (J×X):ℝ)^2*c)*‖v‖^2 ≤ gas A v:=by
 classical -- avoid
 choose! F G v using fun i j u=> (H i j u).sales
 let T:= @univ (J×J) _; let L:J×J→Ruler (J×X) Z:= fun ⟨i,j⟩=> Matrix.of fun x a => if x.1=i ∧ i≠j then F i j x.2 a else 0; let R:J×J→ Ruler Z (J×X):= fun ⟨i,j⟩=>Matrix.of fun a x => if x.1=j ∧ i≠j then G i j a x.2 else 0
 let B(z):Op (J× X):= L z*R z; let P:=play (fun i:J=> farm i A); let M:= (∑ i∈ T, B i); let K:= A-P-M
 have hB(x y:J×X): ‖K x y‖ ≤ c:= by
    have he (i j:J) : B (i,j) x y=if x.1=i ∧ y.1=j ∧ i≠j then ((F i j)*(G i j)) x.2 y.2 else 0:=by unfold B L R; rw [Matrix.mul_apply]; by_cases h:x.1=i <;> by_cases l:y.1=j <;> by_cases b:i=j <;> simp [h,l,b, Matrix.mul_apply] -- tune
    unfold K M; rw [Matrix.sub_apply,Matrix.sub_apply,Matrix.sum_apply]; let f:= (x.1,y.1); rw [sum_eq_single f]; swap; · rintro ⟨i,j⟩ _ v; rw [he]; exact if_neg fun g=> v (Prod.ext g.1.symm g.2.1.symm)
    swap; · simp [T]
    unfold f; rw [he, show P x y= if x.1=y.1 then A (x.1,x.2) (x.1,y.2) else 0 from rfl]; by_cases k:x.1=y.1 <;> first| (obtain ⟨i,j⟩:=x; obtain ⟨u,w⟩:=y; change i=u at k; subst u; simp [t])| (simpa [k] using v x.1 y.1 k x.2 y.2)
 have hm:‖K‖ ≤ (page (J×X):ℝ)^2*c:= (by rw [sq]; exact jingle K c t hB);
 obtain ⟨U,Hx,Dν⟩:= golem _ _ D; obtain ⟨S,Y,cS,T'⟩:= combine T U (fun i=> ker (ract (R i)).toLinearMap) (fun _=>page Z) (fun i t=> ker_size _)
 have hx: dim U ≤ dim S+page J^2*page Z:= by simpa [T,page,Fintype.card_prod,sq,nsmul_eq_mul] using Y
 refine ⟨S, le_trans Hx (Nat.mul_le_mul_left _ hx), fun i t=> ?_⟩;
 have he: ract M i=0:= by unfold M; rw [_root_.map_sum, ContinuousLinearMap.sum_apply]; exact sum_eq_zero fun j u=> by change ract (L j* R j) _ =_; rw [Largo.R_mul, show ract (R j) i=0 from T' j u t,map_zero]
 let a:= ract A i; let e:=(page (J×X):ℝ)^2*c; have hg: |gas K i| ≤ e*‖i‖^2:= le_trans (Complex.abs_re_le_norm _) ((norm_inner_le_norm i (ract K i)).trans ((mul_le_mul_of_nonneg_left (le_trans (R_cost ..) (mul_le_mul_of_nonneg_right hm (norm_nonneg _))) (norm_nonneg _)).trans_eq (by unfold e; ring))) -- tune
 have ht: gas K i=gas A i-gas P i:= by unfold gas K; rw [map_sub,map_sub,ContinuousLinearMap.sub_apply,ContinuousLinearMap.sub_apply,he,sub_zero,inner_sub_right,Complex.sub_re]; -- others
 have hz:=Dν i (cS t); change x*_ ≤ gas P i at hz; change (x-e)* ‖i‖^2 ≤ _; nlinarith only [ht,(abs_le.mp hg).1,hz]
#print axioms crawl
end kernelBills
end Violas
end YM.CF.Window.ArchiveK
