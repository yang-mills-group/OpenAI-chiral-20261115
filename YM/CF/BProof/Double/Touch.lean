import YM.CF.BProof.Double.Oblong
import YM.CF.BProof.Wick.Dyke
/-! Left/right doubled symbols in Wick calculation. Coordinates ON ACTUAL modes,
without replacing chiral Weyl `spar` columns; C acts skew full. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]
abbrev cell (i:Tree I): FC I:= Sum.elim put takeF i
def printT : Book I→ₗ[ℂ] FC I where
 toFun := fun x=> ∑ i,x.ofLp i • cell i
 map_add' x y:= by simp [add_smul,sum_add_distrib]
 map_smul' c x:= by simp [smul_smul,smul_sum]
lemma printed (x:Book I): printT x= create (rows x)+remove (pend (cols x)):=by
 rw [remove_def,create_def]; change ∑ i,x.ofLp i • cell i=_; unfold Tree; rw [Fintype.sum_sum_type]; simp [pend,rows,cols,cell] -- tune
lemma printedT (i:Tree I): printT (basisKet i)=cell i:=by change ∑ _,_=_; simp only [basis_apply,ite_smul]; simp
lemma inner_pend (x y: Ket I): inner ℂ (pend x) y=inner ℂ (pend y) x:= by rw [EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct]; simp [pend,dotProduct,mul_comm]
lemma inner_bill (x y: Book I): inner ℂ x y=inner ℂ (rows x) (rows y)+inner ℂ (cols x) (cols y):=by
 simp_rw [EuclideanSpace.inner_eq_star_dotProduct]; unfold dotProduct Tree; rw [Fintype.sum_sum_type]; rfl
@[simp] lemma pend_row(x:Book I): rows (pend x)=pend (rows x):=rfl
@[simp] lemma pend_col(x:Book I): cols (pend x)=pend (cols x):=rfl
-- tau form defined coordinate-free by slip (swap). Useful transformer pricing
abbrev tau (x y: Book I):= inner ℂ (pend x) (acts (slip I) y)
lemma taus (x y: Book I): tau x y= inner ℂ (pend (cols x)) (rows y) + inner ℂ (pend (cols y)) (rows x):=by
 rw [tau,inner_bill,pend_row,pend_col,slip,bio, mead]; simp only [act_zero,zero_add,add_zero,act_one]; rw [inner_pend (rows _),add_comm]
lemma add_A (F G H:FC I): antiB (F+G) H=antiB F H+antiB G H:=by unfold antiB; noncomm_ring
lemma add_B (F G H:FC I): antiB F (G+H)=antiB F G+antiB F H:=by unfold antiB; noncomm_ring
lemma ant (x y:Book I): antiB (printT x) (printT y)=tau x y • 1:=by
 rw [printed,printed,add_A,add_B,add_B]; rw [car_rem]; unfold antiB; rw [car_create,add_comm (create _* _),car ..,car ..,taus]; module -- tune
variable {A P Q C:Op I}{c r:ℝ}{x:Book I}
lemma rightErase (p:Enter x A){U:Wave I}(t:Task A U): acts (printT x) U=0:=by
 rw [printed,act_add,tarp t.home t.wage p.1,tars t.home t.wage,zero_add]; rw [← show cc (cc A)=A from cc_cc _, ←pend_move,p.2,pend_zero]
lemma pushRow (g:Cᵀ= -C)(i:I) : acts (star (printT (join (basisKet i) (acts (cc C) (basisKet i))))) (pairWave C)=0:= by
 rw [printed,star_add, act_add]; simp only [row_join,col_join,create_put,remove,star_star]; rw [show star (put i)=takeF i from rfl,pull g]; simp only [coupleRow,create_def,act_sum]; simp_rw [act_smul]; -- combine
 simp only [pend,basis_act,cc_apply, star_star]; have he(j:I): C j i= -C i j:=Matrix.ext_iff.mpr g i j; simp_rw [he, neg_smul]; simp -- tune
lemma pushVector(g:Cᵀ= -C)(x: Ket I): acts (star (printT (join x (acts (cc C) x)))) (pairWave C)=0:=by
 let F : Ket I→ₗ[ℂ] Book I:=
   { toFun := fun z=> join z (acts (cc C) z)
     map_add' := fun x y=> book_ext (by simp) (by simp)
     map_smul' := fun c x=> book_ext (by simp) (by simp) }
 change acts (star (printT (F x))) _=_; rw [← basis_expand x,map_sum, map_sum,star_sum, act_sum]; apply sum_eq_zero; intro i _; rw [map_smul,map_smul,star_smul, act_smul,show acts (star (printT (F (basisKet i)))) (pairWave C)=0 from pushRow g i,smul_zero]
end YM.CF.BProof.Double
