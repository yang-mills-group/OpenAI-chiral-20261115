import YM.CF.BProof.Garden.Green
import YM.CF.BProof.Double.Touch
/-! eq:B-Jrep site change-of-creator basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Double Pastry
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] {S T:Finset I}
def unitScale:ℂ:=(↑(Real.sqrt 2):ℂ)⁻¹
lemma scale_two : unitScale*unitScale=(1/2:ℂ):=by
 unfold unitScale; rw [← mul_inv,←pow_two,←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; push_cast; ring
@[simp] lemma scale_star : star unitScale=unitScale:=by simp [unitScale]
def spear (C:Op I)(i:I):Book I:=unitScale • join (acts C (basisKet i)) (basisKet i)
def thorn (C:Op I)(i:I):=star (printT (spear C i))
def spearen (C:Op I)(i:I):Book I:=join (basisKet i) (acts (cc C) (basisKet i))
lemma pend_basis (i:I): pend (basisKet i)=basisKet i:= by apply PiLp.ext; intro j; simp [pend]
lemma speartip(C:Op I)(i:I): thorn C i=unitScale • printT (spearen C i):=by
 unfold spearen thorn spear; rw [map_smul,star_smul,printed,printed]; simp only [star_add,star_star, pend_move, cc_cc,pend_basis,row_join,col_join,scale_star,remove,star_star]; rw [add_comm] -- tune
@[fun_prop] lemma thorn_cont(i:I):Continuous (fun C:Op I=>thorn C i):=by
 unfold thorn spear; have he:Continuous (printT (I:=I)):= printT.continuous_of_finiteDimensional
 have hx:Continuous (fun C:Op I=>join (acts C (basisKet i)) (basisKet i)):=by -- define map
    let F:Op I→ₗ[ℂ] Book I:={toFun:=fun C=>join (acts C (basisKet i)) 0,map_add':=fun x y=> book_ext (by simp [act_add]) (by simp),map_smul':=fun c x=>book_ext (by simp [act_smul]) (by simp)}; have ht:Continuous (F):= F.continuous_of_finiteDimensional
    exact (by have h': (fun C=>join (acts C (basisKet i)) (basisKet i))=(fun C=>F C+join 0 (basisKet i)):=funext fun i=>book_ext (by simp [F]) (by simp [F]); rw [h']; exact ht.add continuous_const)
 exact continuous_star.comp (he.comp (hx.const_smul unitScale)) -- tune
variable {C:Op I}
lemma annihilate (x:Cᵀ= -C)(i:I): acts (star (thorn C i)) (pairWave C)=0:=by rw [speartip,star_smul,act_smul,spearen,pushRow x,smul_zero]
lemma wave_lower (C:Op I):1≤ ‖pairWave C‖:=by
 have he:‖inner ℂ (vacuum I) (pairWave C)‖≤_:= norm_inner_le_norm (𝕜:=ℂ) _ _; simpa only [vacuum,basis_inner,paired_vac,norm_one,basisKet, EuclideanSpace.norm_single, one_mul] using he
lemma thorn_anti(x:Cᵀ= -C)(i j:I):antiB (thorn C i) (thorn C j)=0:=by
 let X:=printT (spear C i); let Y:=printT (spear C j); let c:= tau (spear C j) (spear C i); have hp(i):acts (printT (spear C i)) (pairWave C)=0:=by simpa only [thorn,star_star] using annihilate x i
 have he:c=0:=by
   have hh:c • pairWave C=0:=by rw [← show acts (c • 1) (pairWave C)= c • pairWave C from (by rw [act_smul,act_one])]; rw [← ant]; rw [antiB,act_add,act_mul,act_mul,hp,hp,map_zero,map_zero,zero_add]
   exact (smul_eq_zero.mp hh).resolve_right (norm_pos_iff.mp (zero_lt_one.trans_le (wave_lower _)))
 unfold thorn antiB; rw [←star_mul,←star_mul,← star_add, show printT (spear C j) * _ + printT (spear C i)*_=c • 1 from ant _ _]; change star (c • 1)=_; rw [he,zero_smul,star_zero]
lemma pend_inner(x y:Ket I): inner ℂ (pend x) (pend y)=inner ℂ y x:=by rw [EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct]; simp [pend,dotProduct,mul_comm]
lemma thorn_mixed (m:C∈ unitary _)(i j:I): antiB (star (thorn C i)) (thorn C j)=if i=j then 1 else 0:=by
 let X:=join (acts C (basisKet i)) (basisKet i); let Z:=spearen C j; nth_rw 1 [thorn]; rw [star_star,speartip,spear,map_smul,antiB_smul,antiB_smul',ant,smul_smul,scale_two,taus]; simp only [spearen,row_join,col_join,pend_move, pend_basis,cc_cc]; have ht:inner ℂ (acts C (basisKet j)) (acts C (basisKet i))=inner ℂ (basisKet j) (basisKet i):=act_unit_inner ⟨_,m⟩ ..; rw [ht]; by_cases h:i=j; subst j; simp only [basis_inner,basis_apply,ite_true,smul_smul]; norm_num; simp [Ne.symm h,h]
lemma square_outlet{S:Finset I}(h:Commute C (cutM S))(i:I)(g:i∈ S): acts (cutM S) (acts C (basisKet i))=acts C (basisKet i):=by rw [←act_mul,h.symm.eq,act_mul,cut_basis,if_pos g]
lemma thorn_occupy(h:Commute C (cutM S)){i:I}(g:i∈S) : Sector S true (thorn C i):=by unfold thorn spear; rw [map_smul,printed]; simp only [row_join,col_join,pend_basis,remove_take]; exact (((Sector.makeP _ (square_outlet h _ g)).add (Sector.down i g)).scale _).contr
lemma thorn_power(h:Commute C (cutM S)){i:I}(g:i∈S): thorn C i= thorn (square S C) i:=by
 unfold thorn spear; unfold square; rw [act_mul,cut_basis,if_pos g,act_mul,square_outlet h i g]
lemma outlet (h:Commute C (cutM S))(x:Cᵀ= -C){i:I}(g:i∈S): acts (star (thorn C i)) (pairWave (square S C))=0:=by rw [thorn_power h g]; exact annihilate (square_tr _ x) i
def crown(C:Op I)(t:Finset I): FC I:= ((t.sort (· ≤ ·)).map (thorn C)).prod
def roofW {I:Type*}[Fintype I][LinearOrder I](C:Op I)(x:Cᵀ= -C):Poly I I:=⟨thorn C,thorn_anti x⟩
lemma roofW_eq(x:Cᵀ= -C)(t:Finset I): (roofW C x).tag t=crown C t:=rfl
@[fun_prop] lemma crown_cont (t:Finset I):Continuous (fun C:Op I=>crown C t):=by
 unfold crown; generalize t.sort (· ≤ ·)=l; induction l with| nil=> simp only [List.map_nil,List.prod_nil]; exact continuous_const| cons i l ih=> simp only [List.map_cons,List.prod_cons]; exact (thorn_cont i).mul ih
end YM.CF.BProof.Garden
