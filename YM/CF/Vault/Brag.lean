import YM.CF.Scroll.Verge
import YM.CF.Dial.Beet
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
lemma bend_sq (s : Finset n) : ∃ c : ℂ,c^2=1 ∧ acts (autumn n).val (basisKet s)=c • basisKet sᶜ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by simp,by simp [show acts (autumn n).val (basisKet ∅)=basisKet univ from flake_vac univ]⟩
  | @insert i s e ih =>
    obtain ⟨c,hp,h⟩ := ih
    let A := parity i s*(c*parity i sᶜ)
    have he : acts (autumn n).val (basisKet (insert i s))=A • basisKet (insert i s)ᶜ := by
      rw [create_basis_is i s e,map_smul,Fock.swivel (autumn n),top_swap,h,map_smul,take_act,if_pos (by simp [e]), show sᶜ.erase i=(insert i s)ᶜ by ext j; simp, smul_smul,smul_smul,mul_assoc]
    exact ⟨A,by unfold A; rw [mul_pow,mul_pow,hp,sq,sq,parity_sq,parity_sq]; simp,he⟩
variable {P Q W V K:Op n}
lemma sheath (h: star V*W=1): twist (star (autumn n)) (quant V)= V.det • quant (cc W):=by
 let L:= autumn n; let A:= quant V; let B:= quant (cc W); let F:= twist (star L) A
 have he(i:n): twist L (create (acts (cc W) (basisKet i)))=remove (acts W (basisKet i)):=by
    rw [create_def,remove_def]; simp_rw [map_sum,twist_scalar,show ∀ i:n, twist L (put i)=takeF i from top_swap,basis_act]; rfl
 have hf i: F*put i=create (acts (cc W) (basisKet i))*F:=by
   apply (twist L).injective; have hk: twist L F=A:=by simpa only [star_star] using (twist_inv (star L) A)
   change twist L _=twist L _; rw [map_mul,map_mul,hk,he,(top_swap i : twist L _=_)]
   unfold A; rw [quant_ann]; rw [←act_mul, h,act_one, remove_take] -- tune A
 apply op_columns; intro s
 change acts F _=acts (_ • B) _; rw [act_smul]
 induction s using Finset.induction_on with
 | empty =>
    change acts F (vacuum _) = _ • acts (quant _) (vacuum _); unfold F; rw [twist_formula]; change acts (star L.val*A*star (star L.val)) _=_
    have hm : acts L.val (vacuum n)=basisKet univ := flake_vac univ
    rw [act_mul,star_star,hm,act_mul, show acts A (basisKet univ)=V.det • basisKet univ from full_map _,map_smul,←hm,act_unit,quant_vac]
 | @insert i s e ih =>
    rw [create_basis_is i s e,map_smul,map_smul,←act_mul,hf,act_mul, ih,map_smul, ←act_mul B, show B*put i=create _ *B from quant_put (cc W) i,act_mul,smul_comm]
lemma cc_quant (V:Op n): quant (cc V)=cc (quant V):=by
 symm; refine quant_unique _ _ ?_ (fun i=>?_)
 · apply PiLp.ext; intro i; rw [vacuum, basis_act,cc_apply,← basis_act (quant V), show acts _ _=_ from quant_vac V]; by_cases p:i=∅ <;>simp [p,basisKet,vacuum]
 have hx (t:n): cc (put t)=put t := by ext i j; rw [cc_apply]; simp only [put_entry]; split_ifs <;> simp
 rw [← hx i,← cc_mul,quant_put, cc_mul]; congr 1
 rw [create_def,create_def, (show ∀ Y:n→FC n,cc (∑ i,Y i)=∑ i,cc (Y i) from fun Y=> win_sum true _ _)]; simp only [cc_smul,hx, basis_act, cc_apply]
lemma annex (h:star V* W=1)(s t:Finset n): quant V sᶜ tᶜ ^2= V.det^2*star (quant W s t)^2:=by
 let G:= quant V; let A:=autumn n; let Q:= twist (star A) G
 have ht : inner ℂ (basisKet s) (acts Q (basisKet t))= inner ℂ (acts A.val (basisKet s)) (acts G (acts A.val (basisKet t))):=by
    unfold Q; rw [twist_formula]; change inner ℂ _ (acts (star A.val*G*star (star A.val)) _)=_; rw [act_mul,star_star,act_mul, ←act_inner (star A.val),star_star]
 obtain ⟨c,hc,H⟩:= bend_sq s; obtain ⟨b,k,P⟩:=bend_sq t
 rw [H,P,map_smul,inner_smul_right,inner_smul_left] at ht
 have hk: V.det*star (quant W s t)= b*(star c*quant V sᶜ tᶜ):=by unfold Q G at ht; rw [sheath h,cc_quant] at ht; simp at ht; exact ht
 rw [←mul_pow,hk,mul_pow,mul_pow,k,←star_pow,hc,star_one,one_mul,one_mul]
def matrix(W:Op n)(X Y:UNI n):Op n:= star X.val*W*Y.val
lemma perched (X:UNI n) (p:Finset n) : Sea (twist X (cutM p)) (wedge X.val p):=by
 refine ⟨?_,wedge_norm ..⟩; rw [act_twistLine,inner_self_eq_norm_sq_to_K,wedge_norm]; simp
lemma corner (X Y:UNI n) (p q:Finset n) (B:Op n) : inner ℂ (wedge X.val p) (acts (quant B) (wedge Y.val q))=quant (matrix B X Y) p q:=by
 rw [← basis_act (quant (matrix B X Y)) p q]; nth_rw 1 [←quant_column]; rw [←quant_column Y.val]; unfold Vault.matrix; rw [quant_mul,quant_mul,quant_star,act_mul,act_mul,← basis_inner, ← act_inner (star _), star_star] -- tune
variable (S:Clad P Q W V K)
include S
lemma deed {C D:Op n}(X Y:UNI n)(s t:Finset n)(p:P=twist Y (cutM t))(q:Q=twist X (cutM s))(u:ℂ)(h: acts (quant (throat P Q W)) (filled P C)=u • filled Q D): stratum Y t C*quant (matrix W X Y) s t=u * stratum X s D:=by
 have ht:= beam_plan S (wedge Y.val t) (wedge X.val s) (p.symm ▸ perched Y t) (q.symm ▸ perched X s); rw [show skyGlow _ _ _=_ from corner X Y s t W] at ht -- tune
 rw [show filled P C=stratum Y t C • wedge Y.val t from p.symm ▸ (Fock.placed ..),show filled Q D=stratum X s D • wedge X.val s from q.symm ▸ (Fock.placed ..),map_smul,ht,smul_smul,smul_smul] at h
 exact smul_left_injective ℂ (norm_pos_iff.mp (by rw [wedge_norm]; exact one_pos)) h
omit S in
lemma seal_det(X:UNI n):det (star X.val)*det X.val=1:=by rw [← Matrix.det_mul,X.property.1,Matrix.det_one]
theorem burnt {R:Op n} {c d:ℂ}(C D:UNI n)(h:Clad (1-P) (1-Q) V W R)(hC:C.valᵀ= -C.val)(hD:D.valᵀ= -D.val)(v: acts (quant (throat P Q W)) (filled P C.val)=c • filled Q D.val)(e: acts (quant (throat (1-P) (1-Q) V)) (filled (1-P) C.val)=d • filled (1-Q) D.val)(k: filled Q D.val≠0)(hp:C.val.det=D.val.det) : d^2= (star c)^2*V.det^2:=by
 obtain ⟨X,s,hx⟩:= spot_projection Q S.helm; obtain ⟨Y,t,hy⟩:=spot_projection P S.proj
 have he:=deed S X Y s t hy hx c v; have hz:1-Q=twist X (cutM sᶜ):=by rw [hx,dim_cut,map_sub,map_one]
 have hv:1-P=twist Y (cutM tᶜ):=by rw [hy,dim_cut,map_sub,map_one];
 have hl:=(deed h X Y sᶜ tᶜ hv hz d e); have hb:= congr_arg (·^2) hl
 have hh: star (matrix V X Y)*matrix W X Y=1:=by
    unfold Vault.matrix
    simp only [star_mul,star_star]; rw [←mul_assoc, ←mul_assoc, ←mul_assoc,mul_assoc _ X.val, X.property.2,mul_one,mul_assoc _ (star V),S.balance,mul_one,Y.property.1] -- tune
 rw [mul_pow,mul_pow, compStratum _ _ _ hC,compStratum _ _ _ hD,annex hh] at hb
 let Z:=star X.val; let Z':=star Y.val
 have ht(A:UNI n)(B:Op n):det (congrC A B)=det A.val*det B*det A.val := by rw [congrC, Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
 rw [ht,ht,Vault.matrix,Matrix.det_mul,Matrix.det_mul,hp] at hb
 let L:=stratum X s D.val; let M:=stratum Y t C.val; let f:= (matrix W X Y); -- hb unfold nested
 let g:= star L; let A:=quant f s t;
 change Z'.det*_*Z'.det*star (M^2)*((Z.det*_*Y.val.det)^2*star A^2)=d^2*(Z.det*_*Z.det*star (L^2)) at hb
 have hr:star (L^2)≠0:=star_ne_zero.mpr (pow_ne_zero _ (strata_gap X s D.val (hx ▸ k)))
 have hy': det Z≠0:=left_ne_zero_of_mul ( (seal_det X).trans_ne one_ne_zero); have hv': D.val.det≠0:=right_ne_zero_of_mul ((seal_det D).trans_ne one_ne_zero)
 apply mul_right_cancel₀ (show Z.det*D.val.det*Z.det*star (L^2)≠0 from mul_ne_zero (mul_ne_zero (mul_ne_zero hy' hv') hy') hr)
 rw [←hb]
 calc
    Z'.det*_ * Z'.det * _ * _= Z.det*D.val.det*Z.det*(V.det^2*star ((M*A)^2)) := by
       rw [mul_pow M A,star_mul,star_pow A]
       have hk:= seal_det Y; change Z'.det*Y.val.det=1 at hk; nth_rw 2 [← one_mul (star A ^ 2)]; rw [show (1:ℂ)= (Z'.det*Y.val.det)^2 from (by simp [hk])]; ring
    _ = _:=by rw [show M*A=c*L from he,mul_pow c,star_mul,star_pow c]; ring
end YM.CF.Vault
