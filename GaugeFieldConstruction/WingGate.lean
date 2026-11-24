import GaugeFieldConstruction.Scepter
-- S tilt basis change and excitation grader
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000
noncomputable section
namespace YM.CF.Fock.Flux
open Function NormedSpace Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B T L: Op I}

lemma quant_pure (h:IsStarProjection P)(x:Wave I)(t: Sea P x): acts (quant P) x=x:=by nth_rw 1 [←t.1]; rw [←act_mul,line_quant h,t.1]
lemma Sea.push (U:UNI I)(x:Wave I)(t: Sea P x): Sea (twist U P) (acts (quantU U).val x):=by rw [Sea,line_twist, ← Fock.swivel,t.1,act_unit_norm]; exact ⟨rfl,t.2⟩
lemma twist_mem (U: UNI I)(h:IsStarProjection P): IsStarProjection (twist U P):= ⟨by unfold IsIdempotentElem; rw [←map_mul,h.isIdempotentElem.eq],by unfold IsSelfAdjoint; rw [←map_star,h.isSelfAdjoint.star_eq]⟩
lemma shore_valve (V:Valve P E A B)(h:IsStarProjection P)(u:IsStarProjection E)
 (e: E.trace=P.trace)(x y:Wave I)(f: Sea P x)(t:Sea E y): acts (star (quant B)) y=(inner ℂ x y) • x:=by
 rw [← quant_star]; let c:= quant E
 calc
    acts (quant (star B)) y= acts (quant (star B)) (acts c y):= by rw [show acts c y=y from quant_pure u y t]
    _=acts (quant (P*star B*E)) y:=by rw [←act_mul,V.home,quant_mul]
    _= _:= (Thera.beamV u h e.symm (star B) y t x f).trans (congrArg (fun L:ℂ=> L • x) ?_)
 unfold skyGlow; rw [quant_star,← act_inner,star_star]; have he: acts (quant B) x=x:=by nth_rw 1 [←quant_pure h x f]; rw [←act_mul,←quant_mul,V.bring,quant_pure h x f]
 rw [he]

-- transformation with possible gauge factor. Pin shutter once; Ward tilt profiles can use ψ of second Pane.
def wall (P A:Op I) (U:UNI I)(b:ℝ) := knight P b * quant A * (quantU U).val
def seek (P B:Op I)(U:UNI I)(b:ℝ):= star (quantU U).val * quant B* knight P (-b)
lemma wall_couple (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ) : wall P A U b * seek P B U b =1:=by
 let X:= (quantU U).val; let K:=knight P b; let W:=quant A; let Y:=quant B
 calc
 _=(K*(W*(X*star X)*Y))*knight P (-b):=by unfold wall seek X K W Y; simp only [mul_assoc]
 _=1:=by rw [show X*star X=1 from (quantU U).property.2,mul_one,show W*Y=1 by unfold W Y; rw [←quant_mul,V.live,quant_one],mul_one,show K*knight P (-b) = knight P _ from knight_seg h ..,add_neg_cancel,knight_start]
lemma couple_wall (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ) : seek P B U b * wall P A U b =1:= mul_eq_one_comm.mp (wall_couple V h ..)
lemma near_anchor (V:Valve P E A B)(h:IsStarProjection P)(u:IsStarProjection E)
 (e: E.trace=P.trace)(U:UNI I)(hc: twist U E=E)(x y:Wave I)(f: Sea P x)(t:Sea E y):
 ∃ z:ℂ, ‖z‖=‖inner ℂ y x‖ ∧ ∀ b:ℝ, acts (star (seek P B U b)) y=z • x:=by
 let y':=acts (quantU U).val y; have hp:Sea E y':=hc ▸ Sea.push U y t
 let w:=inner ℂ y y'
 have he:y'=w • y:= hp.1.symm.trans (Sea.scalar u t y')
 have hw: ‖w‖=1:= by have hh:=hp.2; change ‖y'‖=1 at hh; rw [he,norm_smul,t.2,mul_one] at hh; exact hh
 refine ⟨inner ℂ x y',?_ ,fun b=>?_⟩
 · rw [he,inner_smul_right,norm_mul,hw,one_mul,← inner_conj_symm y x]; exact (norm_star _).symm -- direction
 rw [seek,star_mul,star_mul,star_star,knight_star h,act_mul,act_mul,shore_valve V h u e x y' f hp,map_smul, knight_hold h _ _ f]

lemma cremate (h:IsStarProjection P)(x:Wave I)(p:Sea P x)(b:ℝ)(A:Op I):
 acts (quant ((Real.exp b) • A)) x= Real.exp (b*rband P) • acts (quant A) x:=by
 have he : ‖x‖=1:=p.2
 let c:= Real.exp b; let X:=c • (1:Op I); have hh:X*P=c • P:=by rw [show X=c • (1:Op I) from rfl, Matrix.smul_mul,one_mul];
 let d:= rband P; have hg: acts (quant X) x=Real.exp (b*d) • x:=by
    obtain ⟨U,s,rfl⟩:= spot_projection P h
    let W:=acts (quantU U).val (basisKet s)
    let z:=inner ℂ W x; have hk:x=z • W:=by unfold z; rw [show W=wedge U.val s from quant_column ..]; exact p.1.symm.trans (act_twistLine ..)
    let C:ℂ:=c
    have hv: X= Matrix.diagonal fun _=>C:=by unfold X; rw [show (1:Op I)=Matrix.diagonal (fun _=> (1:ℂ)) from rfl,←Matrix.diagonal_smul]; congr 1; funext x; change c • (1:ℂ)=_; simp [C]
    have hl: c^s.card=Real.exp (b*d):=by change _=Real.exp (b*rband _); rw [rband_count, mul_comm,Real.exp_nat_mul]
    have hz: acts (quant X) (basisKet s)= (C^s.card) • basisKet s :=by rw [hv,quant_diag,diag_basis]; rw [prod_const]
    have hx:X*U.val=U.val*X:=by unfold X; simp
    have hp:quant X*(quantU U).val=(quantU U).val*quant X:=by change quant X*quant _=quant _*quant _; rw [←quant_mul,hx,quant_mul]
    have ht:acts (quant X) W= (Real.exp (b*d):ℂ) • W:=by unfold W; rw [←act_mul,hp,act_mul,hz,map_smul]; congr 1; rw [← hl]; push_cast; rfl
    change _= Real.exp (b*d) • x; rw [hk,map_smul,ht,smul_comm z,Complex.coe_smul] -- danger hk d uses x? let d depends on P not x
 rw [show (Real.exp b) • A=A*X from (by unfold X c; simp),quant_mul,act_mul,hg,←Complex.coe_smul,map_smul]; simp only [Complex.coe_smul]; rfl

-- Seaport determinant after tilt. Does NOT impose volume-stationary estimates.
abbrev crownD (P A:Op I)(b:ℝ):Op I:= Real.exp b • (chips P b * A)
lemma dp_base (V:Valve P E A B)(h:IsStarProjection P)(b:ℝ): (crownD P A b)*P=P:=by unfold crownD; rw [Matrix.smul_mul, mul_assoc,V.carry,chips_act b h,smul_smul, ← Real.exp_add, add_neg_cancel,Real.exp_zero,one_smul]
lemma cp_base (V:Valve P E A B)(h:IsStarProjection P)(b:ℝ): P*star (crownD P A b)=P:=by nth_rw 1 [← h.2]; rw [←star_mul, dp_base V h,h.isSelfAdjoint.star_eq]
lemma dp_live (V:Valve P E A B)(h:IsStarProjection P)(b:ℝ) : ∃ W:Op I,W*crownD P A b=1:=by
 let v:=Real.exp b; let W:=v⁻¹ • (B*chips P (-b)); refine ⟨W,?_⟩
 unfold W crownD; rw [Matrix.smul_mul,Matrix.mul_smul]; change v⁻¹ • v • ((B* _)*(_*A)) =1; rw [inv_smul_smul₀ (Real.exp_pos _).ne',mul_assoc,←mul_assoc _ _ A,chips_ps (-b) b h,neg_add_cancel,chips_zero,one_mul,V.rest] -- replace knight

open scoped ComplexOrder
private lemma ceiling_c (h:A.PosSemidef)(e:A.det ≠ 0): Real.log ‖A.det‖ ≤ (A-1).trace.re:=by
 let P:= h.isHermitian; let f:=P.eigenvalues
 have ht:A.PosDef:= h.posDef_iff_det_ne_zero.mpr e; have hv (i:I): 0 < f i:= ht.eigenvalues_pos _; have hP : 0 < ∏ i,f i:= prod_pos fun i _=> hv i
 have hh : A.trace= ↑(∑ i,f i):=by rw [P.trace_eq_sum_eigenvalues,Complex.ofReal_sum]; rfl
 have he : ‖A.det‖=∏ i,f i:=by rw [P.det_eq_prod_eigenvalues]; change ‖∏ i,(↑(f i):ℂ)‖=_; rw [← Complex.ofReal_prod,Complex.norm_real, Real.norm_of_nonneg hP.le]
 rw [he,Real.log_prod (fun i _=> (hv i).ne'),Matrix.trace_sub, hh, Complex.sub_re, Complex.ofReal_re]
 refine le_trans (sum_le_sum (s:=univ) (fun i _=> Real.log_le_sub_one_of_pos (hv i))) (le_of_eq ?_); rw [sum_sub_distrib, sum_const,card_univ]; simp

variable {D:Op I}
lemma wall_log (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(x:Wave I)(p:IsStarProjection D)(q:Sea D x) :
 let R := wall P A U b
 let C := crownD P A b
 let X := twist U D-P
 ‖acts R x‖ ≤ Real.exp (-b * X.trace.re) * Real.exp (((star C*C-1)* X).trace.re / 2):=by -- rewrite (type)
 intro R C X
 let F:= twist U D; let d:=rband F; let T:= star C*C; let Z:=F*T*F+(1-F); have hp:= twist_mem U p
 let y:=acts (quantU U).val x; have ht:Sea F y:=Sea.push U x q
 let z:=acts (quant C) y; have hZ:z≠0:=by
    obtain ⟨W,v⟩:=dp_live V h b; intro e
    have hh := congrArg (acts (quant W)) e; rw [map_zero] at hh; unfold z at hh; rw [←act_mul,←quant_mul,show W*C=1 from v,quant_one,act_one] at hh; exact (norm_ne_zero_iff.mp (by rw [ht.2]; norm_num)) hh
 let M:= acts (quant (chips P b * A)) y; have hk:z=Real.exp (b*d) • M:=cremate hp y ht b _
 have he:R=Real.exp (b*rband P) • (quant (chips P b * A) * (quantU U).val):=by simp only [knight,R,wall,Matrix.smul_mul,← quant_mul]
 have hV: ‖acts R x‖=Real.exp (-b*X.trace.re) * ‖z‖:=by
    have hs: X.trace.re=d-rband P:=by unfold X; rw [Matrix.trace_sub,Complex.sub_re]
    rw [hk,norm_smul,he,←Complex.coe_smul,act_smul,norm_smul,act_mul];
    change ‖(↑(Real.exp _):ℂ)‖*‖M‖=Real.exp _*(‖(_ :ℝ)‖* _) ; rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le, ←mul_assoc,←Real.exp_add,hs]; ring_nf -- tune lhs dot real
 have hz:(↑(‖z‖^2):ℂ) = Z.det:=by
    rw [show (Z:Op I).det= _ from (Thera.meadow hp y ht T).symm]; change _=inner ℂ y (acts (quant _) _); unfold T; rw [quant_mul, quant_star,act_mul, ←act_inner,star_star,inner_self_eq_norm_sq_to_K]; push_cast; rfl
 have hv:Z.PosSemidef:=by
    have hT:T.PosSemidef:= Matrix.posSemidef_conjTranspose_mul_self _
    have he: F * T * F= Fᴴ * T * F:= congrArg (fun x:Op I=> x*T*F) hp.2.symm
    unfold Z; rw [he]; apply Matrix.PosSemidef.add (hT.conjTranspose_mul_mul_same F); exact Matrix.nonneg_iff_posSemidef.mp (hp.one_sub.nonneg)
 have hW: (Z-1).trace= ((T-1)*X).trace:=by
    have hg: (T*P).trace=P.trace:=by rw [Matrix.trace_mul_comm]; unfold T; rw [←mul_assoc, cp_base V h]; -- have tr(P*C)=tr C*P
                                        rw [Matrix.trace_mul_comm,dp_base V h]
    have hh: (F*T*F).trace=(T*F).trace:=by rw [mul_assoc F,Matrix.trace_mul_comm F, mul_assoc T, hp.isIdempotentElem.eq]
    change (Z-1).trace=((T-1)*(F-P)).trace; unfold Z; rw [Matrix.trace_sub,mul_sub,sub_mul,sub_mul,one_mul,one_mul,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_sub,hg, Matrix.trace_add, Matrix.trace_sub,hh]; abel
 have hd: ‖Z.det‖= ‖z‖^2:=by rw [← hz,Complex.norm_real, Real.norm_of_nonneg (by positivity)]
 have hy:0<‖z‖:= norm_pos_iff.mpr hZ
 have ho:= ceiling_c hv (norm_pos_iff.mp (hd.symm ▸ pow_pos hy 2))
 rw [hd, Real.log_pow,hW] at ho; push_cast at ho
 rw [hV]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply le_trans (le_of_eq (Real.exp_log hy).symm) (Real.exp_monotone ?_); linarith only [ho]
end YM.CF.Fock.Flux
end
