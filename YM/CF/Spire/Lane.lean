import YM.CF.Scroll.Mug
import YM.CF.Fock.Reap
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Scroll
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[Fintype I][DecidableEq I][LinearOrder n][Fintype n]
-- charge conjugation in our fixed frames
def dove (p:Bool)(x:Ket I): Ket I:= WithLp.toLp 2 (fun i=> cSignX p (x.ofLp i))
lemma dove_nil(x:Ket I): dove false x=x:=rfl
lemma dove_acts(p:Bool)(M:Op I)(q:Ket I): dove p (acts M q)=acts (windX p M) (dove p q):=by
 cases p; rfl
 apply PiLp.ext; intro i; change star ((acts M q).ofLp i)=_; rw [act_at,act_at]; simp only [Matrix.mulVec,dotProduct,star_sum,dove,WithLp.ofLp_toLp,star_mul', windX,cSignX, ite_true, cc_apply]
lemma dove_base(p:Bool)(i:I):dove p (basisKet i)=basisKet i:=by apply PiLp.ext; intro; cases p <;>simp [dove,cSignX, apply_ite star]
lemma dove_dot(p:Bool)(x y:Ket I): inner ℂ (dove p x) (dove p y)= cSignX p (inner ℂ x y):=by
 cases p; rfl
 simp only [cSignX,dove, PiLp.inner_apply, dite_true,ite_true,WithLp.ofLp_toLp,star_sum]; apply sum_congr rfl; intro i _; change star _*star (star _)=star (_*star _); rw [star_mul'] -- tune
lemma dove_scale(p:Bool)(x:Ket I)(c:ℂ):dove p (c•x)= cSignX p c • dove p x:=by apply PiLp.ext; intro i; cases p; rfl; change star (c*_) = star c * star _; rw [star_mul']; rfl
lemma win_up(p:Bool)(i:n):windX p (put i)=put i:=by cases p; rfl; exact put_clear i
lemma stove(p:Bool)(x:Ket n): windX p (create x)=create (dove p x):=by
 rw [create_def,win_sum, create_def]; refine sum_congr rfl fun i _=> ?_; rw [win_c,win_up]; rfl
lemma swish(p:Bool)(M:Op n): windX p (quant M)=quant (windX p M):=by
 apply quant_unique; swap; intro i; have he:=congr_arg (windX p) (quant_put M i); rw [win_m,win_m,win_up,stove,dove_acts,dove_base] at he; exact he
 have he:= congr_arg (dove p) (quant_vac M); rw [dove_acts] at he; unfold vacuum at *; rwa [dove_base] at he
lemma whisper(p:Bool)(X:Op I): windX p (exp X)=exp (windX p X):=by
 letI : NormedAlgebra ℚ (Op I) := NormedAlgebra.restrictScalars ℚ ℂ (Op I); let F : Op I→+* Op I:= ⟨⟨⟨windX p,win_i p⟩,win_m p⟩,win_z p,win_a p⟩; exact map_exp F (typ_l p) X -- tune
lemma win_duo(p:Bool)(C: Op n):dove p (pairWave C)=pairWave (windX p C):=by
 have he : windX p (coupl C)=coupl (windX p C):=by
   unfold coupl squareP
   rw [win_c, win_sum, show cSignX p (2:ℂ)⁻¹=(2:ℂ)⁻¹ from (by cases p; rfl; norm_num [cSignX])]; congr 1; refine sum_congr rfl fun i _=>?_ ; rw [win_sum]; refine sum_congr rfl fun j _=> ?_; rw [win_c,win_m,win_up,win_up]; cases p <;> rfl
 rw [←stored, dove_acts,vacuum, dove_base,whisper,he]; exact stored _
lemma twist_left {A: Op n}(h:IsStarProjection A): lineOp (1-cc A)=twist (autumn n) (lineOp A):=by
 obtain ⟨U,S,h⟩:= spot_projection A h; subst A; let V:= autumn n
 have he:= carried_inv (ccU U)
 change twist (star V) (quant (cc U.val))= (cc U.val).det • quant (cc (cc U.val)) at he; rw [cc_cc] at he
 rw [show cc (twist U (cutM S))=twist (ccU U) (cutM S) from (by rw [twist_formula,twist_formula,cc_mul,cc_mul,cc_star,cut_real]; rfl), show 1-twist (ccU U) (cutM S)=twist (ccU U) (cutM Sᶜ) by rw [dim_cut,map_sub,map_one], line_twist,line_twist,cutLine,cutLine]; apply (twist (star V)).injective
 change twist (star V) ((twist (quantU (ccU U))) (cutM {Sᶜ}))=twist (star V) ((twist (autumn n)) ((twist (quantU U)) (cutM {S})))
 rw [show twist (star V) ((twist (autumn n)) _)=_ from twist_inv _ _,← leaves]
 rw [twist_formula (quantU (ccU U)),map_mul,map_mul,map_star,show twist (star V) (quantU (ccU U)).val=_ from he,show twist (star V) ((twist (autumn n)) _)=_ from twist_inv _ _]; rw [Matrix.smul_mul, star_smul,Matrix.mul_smul, Matrix.smul_mul, smul_smul, scale_unit_self ((show ‖(cc U.val).det‖=1 from mat_det_norm (ccU U))),one_smul]; exact (twist_formula (quantU U) (cutM {S})).symm
lemma win_cut(p:Bool)(S:Finset I):windX p (cutM S)=cutM S:=by cases p; rfl; ext; simp [cutM,windX,Matrix.diagonal_apply,apply_ite (starRingEnd ℂ)] -- tune
lemma win_lace(p:Bool){A:Op n}(h:IsStarProjection A): windX p (lineOp A)=lineOp (windX p A):=by
 cases p; rfl
 change cc (lineOp A)=lineOp (cc A); obtain ⟨U,S,h⟩:=spot_projection A h; subst A
 rw [show cc (twist U (cutM S))=twist (ccU U) (cutM S) from (by rw [twist_formula,twist_formula,cc_mul,cc_mul,cc_star,cut_real]; rfl),line_twist,line_twist,cutLine,twist_formula,twist_formula,cc_mul,cc_mul,cc_star,show cc (cutM {S})=cutM {S} from win_cut true _]
 rw [show cc (quantU U).val=(quantU (ccU U)).val from swish true U.val]
end YM.CF.Spire
