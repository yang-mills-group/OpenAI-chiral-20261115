import YM.CF.Thera.Warp
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
section core
variable {n:Type*}[LinearOrder n][Fintype n]{P B K W Z C:Op n}
lemma starbeam(A:Op n)(x y:Wave n): star (skyGlow x A y)=skyGlow y (star A) x:=by
 unfold skyGlow; rw [quant_star,←act_inner]; exact inner_conj_symm .. -- tune
lemma meadow(h:IsStarProjection B)(p:Wave n)(t: Sea B p)(X: Op n): skyGlow p X p=det (B*X*B+(1-B)):=by
 obtain ⟨U,f,h⟩:=spot_projection B h; subst B; let L:=wedge U.val f; let T:=quantU U
 let c:= inner ℂ L p
 have hp:p=c • L:=t.1.symm.trans (act_twistLine ..); have hn:= t.2; rw [hp,norm_smul,show ‖L‖=1 from wedge_norm ..,mul_one] at hn
 have hL :L=acts T.val (basisKet f):=(quant_column ..).symm
 unfold skyGlow; rw [hp,map_smul,inner_smul_left,inner_smul_right,←mul_assoc,show (starRingEnd ℂ) c*c=1 from scale_unit_self hn,one_mul,hL]
 let V:=star U; let Q:= twist V X
 have he : twist U Q=X:= (congrArg (fun u:UNI n=>twist u Q) (star_star U).symm).trans (twist_inv _ _)
 have hh:twist U (cutM f)* X* twist U (cutM f)+(1-twist U (cutM f))= twist U (padded f Q):=by rw [padded,map_add,map_sub,map_one,map_mul,map_mul, he]
 rw [hh,det_twist]; nth_rw 1 [←he]; rw [quant_twist, show acts _ (acts T.val (basisKet f))=_ from (Fock.swivel T (quant Q) _).symm, act_unit_inner,basis_inner,basis_act, Fock.principal] -- tune
variable (H:Clad P B W Z K)(Y:TagG P C)
lemma close_c (u:‖bentT K B W C‖<1):IsUnit (1+bentT K B W C):=nearOne (by rwa [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg])
include H Y
lemma teakC(p:Wave n)(t:Sea P p) : let A:=1+bentT K B W C; acts (quant A) p=det A • p:=by
 intro A
 have he:A*P=P*A:=(Commute.add_right (Commute.one_right P) (storms H Y)).symm.eq
 have hx: P*A*P+(1-P)=A:=by
   have hy:P*bentT K B W C=bentT K B W C:=by unfold bentT; simp only [←mul_assoc,H.tray] -- tune
   unfold A; rw [←he, mul_assoc, H.proj.isIdempotentElem.eq, add_mul,one_mul,←(storms H Y).eq,hy]; abel -- tune unfolds A he
 have hk:det A=inner ℂ p (acts (quant A) p):=by nth_rw 1 [←hx]; exact (meadow H.proj p t A).symm
 rw [hk, ←Sea.scalar H.proj t]; nth_rw 1 [←t.1]; rw [←act_mul,line_quant_comm he,act_mul]
lemma whittle(p q:Wave n)(s:Sea P p)(t:Sea B q)(u:‖bentT K B W C‖<1): skyGlow q (W*(1+C)) p= Complex.exp (invoice (bentT K B W C))*skyGlow q W p:=by
 have hp:=beam_plan (rideK H Y (close_c u)) p q s t
 let A:=bentT K B W C; let f:=quant (1+A); have hg:acts f p=det (1+A) • p:=teakC H Y p s
 apply smul_left_injective ℂ (show q≠0 from norm_pos_iff.mp (t.2.symm ▸ zero_lt_one)); dsimp only; rw [← hp, show throat P B (W*(1+C))=throat P B W*(1+A) by unfold throat; rw [←mul_assoc B]; exact brace_r H Y,quant_mul,act_mul, show acts _ p= _ from teakC H Y p s,map_smul,beam_plan H p q s t,factor _ u,mul_smul]
lemma taillight {m:Type*}[LinearOrder m][Fintype m] (f:m↪n)(j:Finset n)(g:Deck f j)(F:Op m)(e:IsStarProjection F)(p q)(L:Sea P p)(u:Sea F q)(l:B=addS f j F)(w:‖bentT K B W C‖<1) : pailL f j (acts (quant W) (acts (exp (dg C)) p))=(Complex.exp (invoice (bentT K B W C))*skyGlow (hoist f j q) W p) • acts (exp (dg (summit f (traitP B K W C)))) q:=by
 subst B; rw [tallied C Y.nil, ←act_mul,←quant_mul]; have he:= stageUp f j g e u; have hx:= rideK H Y (close_c w); rw [broomstick hx _ _ L he,map_smul,tides f j g e hx.bare hx.chest,pourL _ _ g,whittle H Y p _ L he w];
-- anchor/line lemma for physical determinant, no Clad needed on measured sector
omit H Y
lemma line_near (h:IsStarProjection B)(p:IsStarProjection P)(e:B.trace=P.trace)(T:Op n): lineOp B * quant (B*T*P)=quant (B*T*P)*lineOp P :=by
 let f(k:ℕ):=chooseK (Fintype.card n) k B.trace • selector n k; let M:= B*T*P; let Y:=quant M; let A:=range (Fintype.card n+1); have hp:B*M=M:=by unfold M; rw [←mul_assoc,←mul_assoc,h.isIdempotentElem.eq]
 have ht: M*P=M:=by unfold M; rw [mul_assoc,p.isIdempotentElem.eq]
 have hu:Y*∑ i∈A,f i=(∑ i∈A,f i)*Y:=by unfold Y f; simp_rw [sum_mul,mul_sum,Matrix.mul_smul,Matrix.smul_mul, selector_quant]
 rw [lineOp,lineOp,←e]; change (quant B*(∑ i∈A,f i))*Y=Y*(quant P*(∑ i∈A,f i)); rw [mul_assoc, ←hu,←mul_assoc,←mul_assoc Y, show quant B*Y=Y by unfold Y; rw [←quant_mul,hp],show Y*quant P=Y by unfold Y; rw [←quant_mul,ht]]
lemma beamV (h:IsStarProjection P)(s:IsStarProjection B)(e: Matrix.trace B= Matrix.trace P)(T:Op n)(x:Wave n) (p:Sea P x)(y:Wave n)(t:Sea B y): acts (quant (B*T*P)) x=skyGlow y T x • y:=by
 have he:= congrArg (fun a: FC n=>acts a x) (line_near s h e T); rw [act_mul,act_mul,p.1] at he
 conv_lhs=> rw [←he]; simp only [quant_mul,act_mul]; -- tune
 have hh:acts (quant P) x=x:=by nth_rw 1 [←p.1]; rw [←act_mul,line_quant h,p.1];
 rw [hh, ←act_mul,quant_line s,Sea.scalar s t]; rfl
lemma prismK (h:IsStarProjection P)(s:IsStarProjection B)(e: Matrix.trace B= Matrix.trace P)(T:Op n)(x:Wave n) (p:Sea P x)(y:Wave n)(t:Sea B y): let A:= B*T*P; (↑(‖skyGlow y T x‖ ^ 2):ℂ)= det (A*star A+(1-B)):=by
 intro A; let c:= skyGlow y T x
 have hP: star A=P * star T * B :=by unfold A; rw [star_mul,star_mul,s.isSelfAdjoint,h.isSelfAdjoint,mul_assoc] -- tune
 have hv:=beamV s h e.symm (star T) y t x p; rw [←hP,←starbeam] at hv
 have he:= beamV h s e T x p y t
 have hB:B*A=B*T*P:=by unfold A; rw [←mul_assoc,←mul_assoc,s.isIdempotentElem.eq];
 have hj:star A*B=star A:=by rw [←show star B=B from s.isSelfAdjoint,←star_mul,hB]
 have hp:B*(A*star A)*B=A*star A:=by rw [←mul_assoc B,show B*A=A from hB,mul_assoc,hj]
 rw [show det (A*star A+(1-B))=skyGlow y (A*star A) y from Eq.trans (congrArg Matrix.det (congrArg (fun x:Op n=>x+(1-B)) hp.symm)) (meadow s y t (A*star A)).symm]; change (↑(‖c‖^2):ℂ)=inner ℂ y (acts (quant (A*star A)) y); rw [quant_mul,quant_star] -- maybe hv needs quant star back
 rw [act_mul, ←quant_star,hv,map_smul,show acts (quant A) x=c • y from he,inner_smul_right,inner_smul_right, inner_self_eq_norm_sq_to_K,t.2]; change (↑(‖c‖^2):ℂ)=star c*(c*(↑(1:ℝ))^2); rw [Complex.ofReal_one,one_pow,mul_one,mul_comm (star c),Complex.ofReal_pow]; exact (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (x:=c)).symm -- tune
end core
end YM.CF.Thera
