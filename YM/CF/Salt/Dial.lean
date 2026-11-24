import YM.CF.Hive.Fan
import YM.CF.Scion.Facet
import YM.CF.Levier.Wake
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre
variable {ι n m u: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder u][Fintype u]
variable (Z:n≃ m)(P: Ax m u)(Q:Oak m)(h:KindX (soar Q)) (H: Ax m u)(W:Oak m)(p:KindX (soar W)) (b r:Bool)(V:UNI m)(U:UNI n)(T:UNI u)
def cool(P:Ax m u): Ax n u:= fun b v=> (P b v).submatrix Z id
def cap(P:Oak m): Oak n:= fun i j b v=>(P i j b v).submatrix Z Z
include h p
omit p in
lemma adult : KindX (soar (cap Z Q)):=by
 let C:=Scion.portX Z ⟨Urn.mount (0: Ax m n),soar Q,h⟩; -- Ax 0 with u issue unused section. use n
 exact C.ward -- defeq?
omit p in
lemma car : (Scion.portX Z ⟨Urn.mount P,soar Q,h⟩)=⟨Urn.mount (cool Z P),soar (cap Z Q),adult Z Q h⟩:=by
 unfold Scion.portX; congr 1
 · funext i j; cases i<;> rfl
 · funext i j; cases i <;> cases j <;> rfl
lemma cloakK (S: FC (LeanV n))(e:spanP (LeanV n) S)(K:FC n)(g:U.val=V.val.submatrix Z Z)(hp:tendA b r V T P H)(hf:Urn.playX b r V Q W) : let A:Weave n u:=Scion.portX Z ⟨mount P,soar Q,h⟩; let B:Weave n u:= Scion.portX Z ⟨mount H,soar W,p⟩; lotY b r T (issue A S K)= issue B (lotY b r U S) (lotB b r U K):=by
 intro A B; unfold A B; rw [car,car]; refine caprice b r U T _ _ _ _ (adult Z Q h) (adult Z W p) ?_ ?_ S e K
 · intro i j; unfold suburban cool; rw [hp,g]; unfold suburban; rw [show windV b ((P i j).submatrix Z id)=(windV b (P i j)).submatrix Z id from (by cases b<;> rfl), Matrix.submatrix_mul_equiv]
   exact (Matrix.submatrix_mul_equiv (V.val * windV b (P i j)) (star T.val) Z (Equiv.refl u) id).symm
 intro i j v s l; unfold cap; rw [hf i j v s l]; rw [singT,singT,twist_formula,twist_formula,g]; rw [show windX b ((Q i j v s).submatrix Z Z)=(windX b (Q i j v s)).submatrix Z Z from (by cases b<;>rfl),show star (V.val.submatrix Z Z)=(star V.val).submatrix Z Z from rfl, Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
omit h p
lemma ruler (P:FC n→+*FC n)(Q:FC n→+*FC n)(z:ℂ)(w:z^2=1)(g:∀ i:n,P (put i)=z • Q (put i))(f:ℂ→ℂ)(h:∀ y x,P (y • x)= f y • P x)(k:∀ y x,Q (y • x)= f y • Q x)(X:FC n)(p:Pitch put (Set.univ:Set n) 0 X):P X=Q X:=by
 induction p with
 | null=> simp
 | add _ _ h k=> rw [map_add,map_add,h,k]
 | stam v _ t=>rw [h,k,t]
 | term i v j=>
    have hx(i:List n): P (rollC put i)= z^i.length • Q (rollC put i):=by
       induction i with
       | nil=> simp [rollC]
       | cons i l ih=>
           change P (put i*rollC put l)=z^(l.length+1) • Q (put i*rollC put l)
           rw [map_mul,map_mul,g,ih,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,pow_succ]
    rw [hx,show z^i.length=1 from ?_,one_smul]; unfold Nat.ModEq at v; nth_rw 1 [show i.length=2*(i.length/2) from (by omega)]; rw [pow_mul,w,one_pow]
lemma spin_k{z:ℂ}{K:UNI n}(g:U.val=z • K.val)(p:z^2=1)(h:star z=z)(A:ribbon n):paintR b r U A= paintR b r K A:=by
 apply Subtype.ext; let P:=lotY b r U; let Q:=lotY b r K; have hu:Pitch put Set.univ 0 A.val:= (fresh_p (fineShape A)).rise (Set.subset_univ _)
 change P A.val=Q A.val; refine ruler P Q z p ?_ (cSignX (b.xor r)) (fun i v=> Urn.lonY ..) (fun i v=> Urn.lonY ..) _ hu
 intro i; rw [show P (put i)=_ from Urn.mold ..,show Q (put i)=_ from Urn.mold ..]; unfold roseB; rw [smul_sum]; apply sum_congr rfl; intro j _; rw [smul_smul]; obtain ⟨b,i⟩:=i; obtain ⟨t,j⟩:=j; unfold sewV; rw [Urn.cream, Urn.cream]; split_ifs; swap; · rw [mul_zero]
 rw [show (Urn.crib U r b).val=z • (Urn.crib K r b).val from ?_]; rfl; cases b <;> cases r <;> simp only [Urn.crib, Pastry.thread]<;> simp [filmG,ccU,g,cc_smul,h,smul_comm z]
end YM.CF.Salt
