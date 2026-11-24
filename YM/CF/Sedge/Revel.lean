import YM.CF.Sedge.Path
/-! Literal injection of single-particle slots. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m: Type*} [LinearOrder n][LinearOrder m][Fintype n][Fintype m]
def coat (f:m↪n): Ket m →ₗ[ℂ] Ket n where
  toFun v:=∑ i, v.ofLp i • basisKet (f i)
  map_add' := fun x y=>by simp [add_smul,sum_add_distrib]
  map_smul':= fun c x=>by simp [mul_smul,smul_sum]
def trailK (f:m↪n): Ket n →ₗ[ℂ] Ket m where
  toFun v:= WithLp.toLp 2 (v.ofLp ∘ f)
  map_add' :=fun x y=>rfl
  map_smul':=fun c x=>rfl
lemma basis_shell (f:m↪n)(i:m): coat f (basisKet i)=basisKet (f i):=by change ∑ j, _= _; simp [ite_smul]
lemma interK (f:m↪n)(x:Ket m)(y:Ket n): inner ℂ (coat f x) y=inner ℂ x (trailK f y):=by
  nth_rw 1 2 [←basis_expand x]; rw [map_sum,sum_inner,sum_inner]
  refine sum_congr rfl ?_; intro i _; rw [map_smul,basis_shell,inner_smul_left,inner_smul_left,basis_inner,basis_inner]; rfl
lemma seamK (f:m↪n)(v:Ket n)(i:m): (trailK f v).ofLp i=v.ofLp (f i):=rfl
lemma trails (f:m↪n)(v:Ket m):trailK f (coat f v)=v:=by
  nth_rw 1 [←basis_expand v]; simp_rw [map_sum,map_smul,basis_shell];
  have he (i:m): trailK f (basisKet (f i))=basisKet i:=by apply PiLp.ext; intro j; simp only [seamK,basis_apply, EmbeddingLike.apply_eq_iff_eq]
  simp_rw [he,basis_expand]
def lows (f:m↪n):Finset n:= univ.map f
lemma coil_hit (f:m↪n)(i:m): f i∈lows f:=mem_map.mpr ⟨i,mem_univ _,rfl⟩
lemma basin (f:m↪n)(x:Ket m)(i:n)(h:i∉lows f): (coat f x).ofLp i=0:=by
  nth_rw 1 [←basis_expand x]; rw [map_sum, WithLp.ofLp_sum,Finset.sum_apply]; apply sum_eq_zero; intro j _; rw [map_smul,basis_shell,WithLp.ofLp_smul,Pi.smul_apply,basis_apply,if_neg (fun (l : i=f j)=>h (l.symm ▸ coil_hit f j)),smul_zero]
lemma stance (f:m↪n)(v:Ket n):coat f (trailK f v)=acts (cutM (lows f)) v:=by
  apply PiLp.ext; intro i; rw [cut_apply]; by_cases h:i∈lows f
  · obtain ⟨j,-,rfl⟩:= mem_map.mp h; rw [←seamK,trails,seamK,if_pos (coil_hit ..)]
  rw [if_neg h, basin _ _ _ h]
lemma trail_cut (f:m↪n)(v:Ket n): trailK f (acts (cutM (lows f)) v)=trailK f v:=by rw [←stance,trails]
lemma coat_ret (f:m↪n)(v:Ket m):acts (cutM (lows f)) (coat f v)=coat f v:=by rw [←stance,trails]

def desk (f:m↪n)(B:Op m): Op n:=Matrix.of fun i j=> (coat f (acts B (trailK f (basisKet j)))).ofLp i
lemma economy (f:m↪n)(B:Op m)(x:Ket n): acts (desk f B) x=coat f (acts B (trailK f x)):=by
  nth_rw 1 2 [←basis_expand x]; rw [map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; intro i _
  rw [map_smul,map_smul,map_smul,map_smul]; congr 1; apply PiLp.ext; intro k; rw [basis_act]; rfl
lemma desk_p (f:m↪n)(A B:Op m): desk f A * desk f B=desk f (A*B):=by apply op_columns; intro i; rw [act_mul,economy,economy,trails,economy,act_mul]
lemma twin_inner (A:Op m)(x y):inner ℂ (acts A x) y=inner ℂ x (acts (star A) y):=by nth_rw 1 [←star_star A]; rw [act_inner]
lemma pull_inner (f:m↪n)(x:Ket n)(y: Ket m):inner ℂ (trailK f x) y=inner ℂ x (coat f y):=by
  rw [←inner_conj_symm,←interK,inner_conj_symm] -- tune
lemma desk_sh (f:m↪n)(A:Op m):star (desk f A)=desk f (star A):=by
  apply op_columns; intro i; apply PiLp.ext; intro j; rw [←basis_inner,←basis_inner,economy,←pull_inner]; -- direction
  rw [←twin_inner,economy,interK,twin_inner]
lemma desk_plus (f:m↪n)(A B:Op m):desk f (A+B)=desk f A+desk f B:=by apply op_columns; intro i; rw [act_add,economy,act_add,map_add,economy,economy]
lemma shelf_right (f:m↪n)(A:Op m): desk f A*cutM (lows f)=desk f A:=by apply op_columns; intro i; rw [act_mul,economy,trail_cut,economy]
lemma level (f:m↪n): desk f 1=cutM (lows f):=by apply op_columns; intro i; rw [economy,act_one,stance]
lemma desk_at (f:m↪n)(A:Op m)(i j:m):desk f A (f i) (f j)=A i j:=by rw [←basis_act (desk f A),economy,←basis_shell,trails,←seamK,trails,basis_act]
lemma desk_out (f:m↪n)(A: Op m)(i j:n)(h:i∉lows f): desk f A i j=0:=by rw [←basis_act (desk f A),economy,basin f _ _ h]
structure Deck (f:m↪n) (s:Finset n):Prop where
  splitL: Disjoint (lows f) s
variable (f:m↪n)(s:Finset n)(h:Deck f s)
def addS(B:Op m): Op n:=cutM s+ desk f B
include h
lemma siding (A:Op m): cutM s*desk f A=0:=by
  ext i j; rw [cutM, Matrix.diagonal_mul]; by_cases g:i∈s
  · rw [desk_out f A _ _ (fun k=>Finset.disjoint_left.mp h.splitL k g),mul_zero]; rfl
  rw [if_neg g,zero_mul]; rfl
lemma wingK (A:Op m): desk f A * cutM s=0:=by have he:=congrArg star (siding f s h (star A)); rw [star_mul,(cutM_idp s).isSelfAdjoint,desk_sh,star_star,star_zero] at he; exact he
lemma addS_mul(A B:Op m):addS f s A* addS f s B= addS f s (A*B):=by rw [addS,addS,addS,add_mul,mul_add,mul_add,wingK _ _ h,siding _ _ h,desk_p,(cutM_idp s).isIdempotentElem]; abel
omit h
lemma addS_star(A:Op m):star (addS f s A)= addS f s (star A):=by rw [addS,addS,star_add, desk_sh,(cutM_idp s).isSelfAdjoint]
lemma projectorD {A:Op m}(g:IsStarProjection A)(h:Deck f s):IsStarProjection (addS f s A):=⟨(by unfold IsIdempotentElem; rw [addS_mul _ _ h,g.isIdempotentElem.eq]),(by rw [isSelfAdjoint_iff,addS_star,g.isSelfAdjoint.star_eq])⟩
lemma desk_trace(A:Op m): (desk f A).trace=A.trace:=by
  rw [Matrix.trace]; rw [←sum_subset (subset_univ (lows f))]; swap; exact fun i _ h=>desk_out _ _ _ _ h
  unfold lows; rw [sum_map]; exact sum_congr rfl fun i _=>desk_at _ _ _ _
include h
lemma wing_cut(x:Ket m): acts (cutM s) (coat f x)=0:=by
  nth_rw 1 [←coat_ret]; rw [←act_mul,←level,siding _ _ h _,act_zero]
lemma origin (x:Ket m)(A: Op m):acts (addS f s A) (coat f x)=coat f (acts A x):=by rw [addS,act_add,wing_cut _ _ h,economy,trails,zero_add];
def summit (A:Op n) : Op m:= A.submatrix f f
omit s h in
lemma summit_rule (A:Op n)(x:Ket m): acts (summit f A) x=trailK f (acts A (coat f x)):=by
  nth_rw 1 2 [←basis_expand x]; simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro i _; rw [basis_shell]; congr 1; apply PiLp.ext; intro j; rw [seamK,basis_act,basis_act]; rfl
end YM.CF.Fock
