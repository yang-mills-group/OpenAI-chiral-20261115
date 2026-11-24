import YM.CF.Scroll.Kent
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {A B:Type*}[Fintype A][Fintype B][DecidableEq A][DecidableEq B]
-- block transforms; simplify many formulae
abbrev portX (p:Equiv.Perm A)(F:A→UNI B): UNI (A×B):=⟨jump p (fun i=>(F i).val),jump_unitary _ _ (fun i=>(F i).property)⟩
abbrev tap (x:Op (A×B)) (i j:A): Op B:= x.submatrix (fun l=>(i,l)) (fun l=>(j,l))
lemma tap_sum (F:A→Op B)(e:Equiv.Perm A)(Y:Op (A×B))(i j:A): tap (jump e F*Y) i j= F i*tap Y (e i) j:=by
 ext a b; change (_*Y) _ _=(F i*tap Y (e i) j) a b; simp only [Matrix.mul_apply, jump_apply,Fintype.sum_prod_type,ite_mul]; rw [sum_eq_single (e i)]; simp; intro p _ h; simp [Ne.symm h]; simp
lemma tap_s (Y:Op (A×B))(i j:A): tap (star Y) i j=star (tap Y j i):=rfl
lemma tap_w (b:Bool)(x:Op (A×B))(i j:A):tap (windX b x) i j= windX b (tap x i j):=by cases b <;> rfl
lemma tap_sg(b:Bool)(x:Op (A×B))(p:Equiv.Perm A)(F:A→UNI B)(i j:A): tap (sings b (portX p F) x) i j=(F i).val*windX b (tap x (p i) (p j))*star (F j).val:=by
 let L:= jump p fun i=>(F i).val; rw [sings, twist_formula]; change tap (L*windX b x *star L) i j=_; let Z:=L*windX b x
 change tap (Z*star L) i j=_; rw [← star_star Z] -- oh
 rw [← star_mul,tap_s,tap_sum,tap_s (Y:=Z)]; rw [star_mul,star_star]; unfold Z; rw [tap_sum,tap_w] -- tune
variable (s:Signed)(L:Side)(ho:Odd L.val)(p:Momentum)(hp:p∈baseCube)(j:ℕ)
-- explicit tap form iff etc
lemma tapeB (i k:Site L)(h:physical p): tap (brix j L p) i k= (if k=0 then ∑ l:Site L,((L.val:ℂ)^2)⁻¹*mode (aliasAt p l) (lift i)*money j L l p else if i=k then (1:ℂ) else 0) • 1:=by
 rw [brix_scale j L h]; ext x y
 change (trident L p*sprig j L p+(1-peb L)) _ _=((_ : ℂ) • (1:Op SpinIdx)) x y
 let T:=trident L p; let V:=money j L; have ht (i k:Site L) (x z):T (i,x) (k,z)= ((L.val:ℂ)^2)⁻¹*(mode (aliasAt p k) (lift i)*(1:Op SpinIdx) x z) :=by by_cases e:x=z<;>simp [e,Matrix.one_apply,T,trident,aliasBlock]
 change (T*sprig j L p+(1-peb L)) _ _=_; simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.sub_apply,Matrix.smul_apply,ht, St,Fintype.sum_prod_type,sprig,c_app]
 by_cases g:k=0
 · simp only [g,if_true]; simp only [peb,spike,s_app]
   by_cases e:i=0 <;> by_cases f:x=y <;> simp [e,f,g,Matrix.one_apply,sum_mul] -- tune sums
 by_cases e:i=k <;> simp [g,e,peb,spike,s_app,Matrix.one_apply]
def pinBlock (L:Side)(s:Signed)(U:UNI SpinIdx): UNI (St L):=portX (s.actEquiv (R:=Per L)).toEquiv (fun _=> U)
variable (b:Bool)(U:UNI SpinIdx)
include ho hp
lemma BX: sings b (pinBlock L s U) (brix j L (cadence s b p))=brix j L p:=by
 ext ⟨i,x⟩ ⟨k,y⟩
 suffices hx: tap (sings b (pinBlock L s U) (brix j L (cadence s b p))) i k=tap (brix j L p) i k from congr_fun (congr_fun hx _) _
 unfold pinBlock; rw [tap_sg]; change U.val*windX b (tap _ (s.act i) (s.act k))* star _= _
 rw [tapeB L (cadence s b p) j _ _ ((cadence_base p hp s b).1),tapeB L p j i k hp.1,win_c,win_i]
 by_cases h:k=0; swap
 · have hx:= s.act_injective.ne h; rw [Signed.act_zero] at hx
   rw [if_neg h,if_neg hx]; by_cases h:i=k
   · rw [h]; cases b<;>simp [cSignX]
   rw [if_neg h,if_neg (s.act_injective.ne h)]; cases b <;> simp [cSignX]
 rw [if_pos h,if_pos (show s.act k=0 by rw [h,Signed.act_zero])]; rw [Matrix.mul_smul,Matrix.smul_mul,mul_one,show U.val*star U.val=1 from U.property.2]; congr 1
 have hx(i k:Site L): aliasAt (cadence s b p) ((CadSite L s b).toEquiv k)=cadence s b (aliasAt p k):= alias_s L ho p s b k -- implicit
 rw [← Equiv.sum_comp (CadSite L s b).toEquiv] -- tune
 have ht(I:Finset (Site L))(f:Site L→ℂ): cSignX b (∑ i∈I,f i)=∑ i∈I,cSignX b (f i):=by cases b<;>simp [cSignX,star_sum]
 rw [ht]; refine sum_congr rfl fun l _=>?_
 have hl:=alias_s L ho p s b l; have hV: money j L ((CadSite L s b).toEquiv l) (cadence s b p)=money j L l p:=by unfold money; rw [hx i,muff_s L ho]; -- tune
 rw [hV,hx i, Ratio.lift_signed_of_odd ho,form (aliasAt p l) s b (alias_real hp.1 _)]
 cases b<;>simp [cSignX,money_real j L ho l hp.1]
omit hp
lemma BV(x:Cover):sings b (pinBlock L s U) (tub (brix j L) (s.act x))= tub (brix j L) x:= morphX b s _ _ _ _ _ (cBrix j L ho) (cBrix j L ho) (fun p hp=>BX s L ho p hp j b U) _
end YM.CF.Scroll
