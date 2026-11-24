import YM.CF.Proa.Wings
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
set_option synthInstance.maxSize 8000
open Acorn
variable {n:Type}[LinearOrder n][Fintype n]
lemma hems (C:Op n)(h:C*C=0)(i:n) : Commute (dg C) ((dg C)* pen (false,i)-pen (false,i)*(dg C)):=by
 change Commute _ (dg C*put i-put i*_); rw [shelve]; apply sub_eq_zero.mp; rw [lever,←act_mul,h,act_zero,map_zero]
lemma held (C:Op n)(h:C*C=0):UnitR (dg C):=by
 let T:=dg C
 refine ⟨fun i p=>?_,fun v=>?_⟩
 · have he(s:Finset n)(i:ℕ)(p:s.card < i): acts (T^i) (basisKet s)=0:=by
     induction s using Finset.induction_on generalizing i with
     | empty=> cases i
               · omega
               rw [pow_succ]; change acts _ (vacuum n)=0; rw [act_mul,dg_veil,map_zero]
     | @insert a s e ih=>
       rw [card_insert_of_notMem e] at p; cases i; omega
       next i=>
        rw [create_basis_is a s e,map_smul,←act_mul]; have ht:= hems C h a; rw [show T^(i+1)*put a=(i+1:ℂ) • ((T*put a-put a*T)*T^i)+put a*T^(i+1) from eq_add_of_sub_eq (tact rfl ht i)]
        rw [act_add,act_smul,act_mul, act_mul,ih (i+1) (by omega),ih i (by omega),map_zero,map_zero,smul_zero,add_zero,smul_zero]
   apply op_columns; intro s; rw [show acts _ _=0 from he s i ((s.card_le_univ).trans_lt p),act_zero]
 rcases v with ⟨b,i⟩; cases b; exact hems C h i
 have he:= hems (star C) (by rw [←star_mul,h,star_zero]) i; have ht:= congrArg star he.eq
 change star (dg _ * (dg _*put i-put i*dg _))=_ at ht
 have hy: star (dg (star C)*put i-put i*dg (star C)) = -(dg C * takeF i-takeF i * dg C):=by rw [star_sub,star_mul,star_mul,dg_star,star_star]; simp [takeF]; -- tune
 have hk:=he.eq; change star (dg _*_) = star ((_ - _)*dg _) at ht; rw [star_mul,star_mul] at ht; change star (dg _*put i-put i*dg _) *star (dg _)=star (dg _)*star (dg _*put i-put i*dg _) at ht; rw [hy,dg_star,star_star,neg_mul,mul_neg] at ht; exact (neg_inj.mp ht).symm
lemma brass_X(C:Op n):dg C=mix (cue false true C):=by unfold dg dyad mix; simp [Fintype.sum_prod_type,cue,Acorn.pen]
end YM.CF.Proa
