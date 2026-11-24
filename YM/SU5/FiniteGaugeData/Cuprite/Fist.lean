import YM.SU5.FiniteGaugeData.Cuprite.Hutch
import YM.SU5.FiniteGaugeData.Brique.Chair
/-! # Uniform tilted Sea invoices (ALL configuration ranks).
Use actual tilted sea and prices, accounting for any penalty to global HS comparison.
There is just one piece of paper reusing label costs across a **term** of the HEADER,
including sectors ahead of exponential bill. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*} [LinearOrder n][Fintype n]{A B P Q Y D X U W:Op n}{a r μ h:ℝ}
namespace Fist
lemma red_quant(x:Wave n)(p:‖A‖≤1): ‖acts (quant A) x‖ ≤ ‖x‖:=by
 have hh:‖star A*A‖ ≤ 1:=by rw [CStarRing.norm_star_mul_self]; exact mul_le_one₀ p (norm_nonneg _) p
 obtain ⟨U,d,H⟩:= spectral_exists (star A*A) (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg A)); have hz : ‖star (quant A)*(quant A)‖ ≤1:=by
    rw [←quant_star,←quant_mul,H,spectral,quant_twist,quant_diag,twist_norm,Matrix.l2_opNorm_diagonal] -- tune
    rw [H,spectral,twist_norm,Matrix.l2_opNorm_diagonal] at hh; apply (pi_norm_le_iff_of_nonneg (show (0:ℝ)≤1 from zero_le_one)).mpr; intro i
    change ‖∏ j∈i,(d j:ℂ)‖ ≤ _; rw [norm_prod]; exact prod_le_one (fun _ _=>norm_nonneg _) (fun j _=>(pi_norm_le_iff_of_nonneg zero_le_one|>.mp hh) j)
 have h: ‖quant A‖ ≤ 1:= by rw [CStarRing.norm_star_mul_self] at hz; nlinarith [norm_nonneg (quant A)]
 exact (wing_opy _ _).trans (mul_le_of_le_one_left (norm_nonneg _) h)
lemma sea_idke {x:Wave n}(h:IsStarProjection P)(g:Sea P x): acts (quant P) x=x:=by nth_rw 1 [←g.1]; rw [←act_mul,line_quant h,g.1]
variable {x p f: Wave n}
-- denominator shading total. x any sector! no grade assumption.
lemma shadow(q:lit A)(g:IsStarProjection Q)(w:Q*A*Q+(1-Q)=A)(t:Sea Q p)(x:Wave n): ‖inner ℂ p x‖ ≤ Real.exp (rueD A /2) *‖acts (quant (tangle A * Q)) x‖:=by
 let T:=tangle A; let Y:= T⁻¹; let y:=acts (quant Y) p; have h:lit T:= refl_live (lit_inv q); have hc:lit Y:=lit_inv h; have hp: A= Y*Y:= by
    apply h.2.mul_right_injective; apply h.2.mul_left_injective -- tune second left multiplies right
    change (T*A)*T=(T*(Y*Y))*T; rw [←mul_assoc T Y, show T*Y=1 from lit_mulin h,one_mul, show Y*T=1 from lit_inmul h]; exact tangle_n q
 have ha:star (quant Y)=quant Y:=by rw [←quant_star,IsSelfAdjoint.of_nonneg hc.1]
 have he: ‖y‖^2 = ‖A.det‖:=by
    have hr:= Thera.meadow g p t A
    rw [w,skyGlow] at hr
    nth_rw 1 [hp] at hr
    rw [quant_mul,act_mul, ←act_inner,ha,inner_self_eq_norm_sq_to_K] at hr; rw [def_norm q.1, ←hr]; change _=(((‖y‖:ℝ):ℂ)^2).re; rw [←Complex.ofReal_pow]; rfl
    -- tune
 have hv:‖y‖=Real.exp (rueD A/2):=by
    have hz:(Real.exp (rueD A/2))^2=‖A.det‖:=by rw [sq, ←Real.exp_add, add_halves]; exact Real.exp_log (norm_pos_iff.mpr (def_beam q).ne')
    nlinarith only [Real.exp_pos (rueD A/2),hz,norm_nonneg y,he]
 have hx: inner ℂ y (acts (quant (tangle A*Q)) x)=inner ℂ p x:=by
    unfold y; change inner ℂ _ (acts (quant (T*Q)) x)=inner ℂ _ _; nth_rw 1 [←ha]; rw [act_inner,←act_mul,←quant_mul,←mul_assoc, show Y*T=1 from lit_inmul h,one_mul,←act_inner, ←quant_star,g.2.star_eq]; rw [sea_idke g t]
 rw [←hx]; exact (norm_inner_le_norm ..).trans (by rw [hv])
variable (d:0<μ)(b:μ≤1)(g:IsStarProjection Q)(c:IsStarProjection P)
local notation "𝓐"=> Q*W*X*P
-- note h already height (full) etc. logos B maps.
abbrev shade(Y:Op n)(p f:Wave n)(R:FC n)(X:Op n):= inner ℂ p (acts (quant Y) (acts R (acts (quant X) f)))
abbrev TwistReceipt(W:Op n):LeanV n→ℝ:= fun i=> if i.1 then ‖acts W (basisKet i.2)‖ else 1
include c in
private lemma antiset(L:List (LeanV n))(i:LeanV n): ∃ x:FC n, (drawT P i*(L.map (drawT P)).prod=x ∨ drawT P i*(L.map (drawT P)).prod= -x) ∧ x=(L.map (drawT P)).prod *drawT P i:=by
 -- commute actual words
 refine ⟨_,?_,rfl⟩
 induction L with
 | nil=> simp
 | cons j s ih=>
    simp_rw [List.map_cons,List.prod_cons,←mul_assoc (drawT P i)]; rw [show drawT P i*drawT P j= -(drawT P j*drawT P i) from eq_neg_of_add_eq_zero_left (rind P c i j),neg_mul,mul_assoc, mul_assoc]
    rcases ih with l|l <;> simp [l]
-- keep rfl for Label.Price.G.
section
variable [Nonempty n]
include d b c g
-- pairing locks for ALL appear columns. works D=1+ actF via PX=P. cost ph. Distinct not initially required. Need paid_corr to $exp B$ independent label count. 
lemma list_pay (t:P*X=P) (p:List (LeanV n))(x:Wave n) (f:acts (quant P) x=x): let T:=bloom Q (Q*W*X*P) μ; let U:= tangle T * Q * W; ‖acts (quant U) (acts ((p.map (drawT P)).prod) (acts (quant X) x))‖ ≤ ((p.map (TwistReceipt (U*(1-P)))).prod) * ‖x‖:=by
 let B:= Q*W*X*P; let T:= bloom Q B μ; let U:= tangle T * Q * W; let F:= U*(1-P); let C:=TwistReceipt F
 let J(x:Wave n):=acts (quant X) x; let K(x:Wave n):=acts (quant U) x; change ‖K _‖≤(p.map C).prod*‖x‖
 induction p generalizing x with
 | nil=>
   change ‖acts (quant U) (acts (1:FC n) (J x))‖≤ 1 * ‖x‖; rw [act_one,one_mul]; unfold J; rw [←act_mul,←quant_mul]; nth_rw 1 [←f]; rw [←act_mul,←quant_mul]; apply red_quant; rw [show U*X*P=tangle T*B from by unfold U B; simp only [mul_assoc]]; exact Hutch.petaline g d b B
 | cons i s ih=>
   cases i with | mk a i =>
   cases a
   · let v:=acts P (basisKet i); let Z:=remove v; have hp:drawT P (false,i)=Z:=by change hideF P i=Z; unfold hideF; rw [prong_t] -- implicit
     have he: ‖v‖≤1:=(Flare.opy _ _).trans (by rw [show ‖basisKet i‖=(1:ℝ) from by simp [basisKet],mul_one]; exact c.norm_le _)
     have hu:acts (star X) v=v:=by unfold v; rw [←act_mul, show star X*P=P from ?_]; nth_rw 1 [←c.2.star_eq]; rw [← star_mul,t,c.2.star_eq]
     have hh:acts (quant P) (acts Z x)=acts Z x:=by nth_rw 2 [← f]; rw [←act_mul,←act_mul,show Z*quant P=quant P* Z from ?_]; unfold Z; rw [quant_ann,c.2.star_eq,show acts P v=v from by unfold v; rw [←act_mul,c.1]] -- tune let
     rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,show C (false,i)=1 from rfl,one_mul]; let S:= (s.map (drawT P)).prod
     have hx: ‖K (acts (S*drawT P (false,i)) (J x))‖≤ (s.map C).prod * ‖x‖:=by
         rw [hp,act_mul]; unfold J; rw [←act_mul Z,show Z*quant X=quant X*Z from ?_,act_mul]; swap; · unfold Z; rw [quant_ann,hu]
         apply le_trans (ih (acts Z x) hh); apply mul_le_mul_of_nonneg_left ((wing_opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((Flare.cost_pe true v).trans he))); apply List.prod_nonneg; intro y hy; obtain ⟨z,-,rfl⟩:= List.mem_map.mp hy; unfold C TwistReceipt; split; exact norm_nonneg _; norm_num -- tune
     obtain ⟨Y,hY,hy⟩:= antiset c s (false,i); rcases hY with hY|hY <;> rw [hY,hy]; exact hx; rw [act_neg]; unfold K; rw [map_neg,norm_neg]; exact hx
   · rw [List.map_cons,List.prod_cons, List.map_cons,List.prod_cons,act_mul]; unfold K; rw [show drawT P (true,i) = create (acts (1-P) (basisKet i)) from ?_, ←act_mul, quant_create,act_mul]; swap; · unfold drawT seekF; rw [if_pos rfl,prong_p]
     apply le_trans (wing_opy _ _); rw [←act_mul U,show U*_ = F from rfl]; rw [mul_assoc]; exact mul_le_mul (Flare.cost_pe false (acts F (basisKet i))) (ih x f) (norm_nonneg _) (norm_nonneg _)
variable {C:LeanV n→ℝ}{r:ℝ}
local notation "𝓚"=> bloom Q (Q*W*X*P) μ
local notation "Δ"=> tangle (bloom Q (Q*W*X*P) μ) * Q * W
omit d b g c [Nonempty n] in
private lemma rowR {m:Type*}[LinearOrder m][Fintype m](S:Finset m)(F:m→FC n)(C:m→ℝ):∃ L:List m, column F S=(L.map F).prod ∧ (L.map C).prod=∏ z∈S,C z:=by refine ⟨S.sort (· ≤ ·),rfl,?_⟩; rw [← List.prod_toFinset C (sort_nodup ..), sort_toFinset] -- tune
omit d b g c [Nonempty n] in
private lemma rowPrice {m:Type*}[LinearOrder m][Fintype m](Y:FC m)(W:FC n)(x:Wave n)(o:m→FC n)(C:ℝ)(hp:∀S:Finset m, ‖acts W (acts (column o S) x)‖ ≤ h^S.card*C): ‖acts W (acts (∑ s:Finset m, crumb Y s • column o s) x)‖ ≤ tier h Y * C:=by
 rw [act_sum,map_sum]; unfold tier; rw [sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum (fun (i:Finset m) _=>?_)); rw [act_smul,map_smul,norm_smul,mul_comm (h^_),mul_assoc]; exact mul_le_mul_of_nonneg_left (hp i) (norm_nonneg (crumb Y i))
lemma settle (t:P*X=P)(u:Sea P x)(A:ribbon n)(y:0≤h)(e:∀z,0≤C z)(o:∀ z: LeanV n,TwistReceipt (Δ*(1-P)) z≤ h*Real.exp (C z)) : ‖acts (quant Δ) (acts (tank P A) (acts (quant X) x))‖ ≤ tier h A.val * Real.exp (∑ z:LeanV n,C z):=by
 let V:= Δ; let H:=Real.exp (∑ z,C z); let F:=TwistReceipt (V*(1-P))
 have hp (S:Finset (LeanV n)): ‖acts (quant V) (acts (column (drawT P) S) (acts (quant X) x))‖ ≤ h^S.card*H:=by
    obtain ⟨L,hL,hk⟩:= rowR S (drawT P) F; have hz:=list_pay (W:=W) d b g c t L x (sea_idke c u); change ‖acts (quant V) _‖≤(L.map F).prod * ‖x‖ at hz; rw [u.2,mul_one,hk] at hz; rw [hL]; apply hz.trans
    calc
       _ ≤ ∏ z∈S,h*Real.exp (C z) := prod_le_prod (fun i _=> by change 0 ≤ F i; unfold F TwistReceipt; split; exact norm_nonneg _; norm_num) (fun i _=>o i)
       _ ≤ _ := by rw [prod_mul_distrib,prod_const, ← Real.exp_sum]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>e i))) (pow_nonneg y _)
 exact rowPrice (m:=LeanV n) A.val (quant V) (acts (quant X) x) (drawT P) H hp
lemma aimed (t:P*X=P)(u:Sea P x)(v:Sea Q p)(A:ribbon n)(y:0≤h)(e:∀z,0≤C z)(o:∀ z:LeanV n,TwistReceipt (Δ*(1-P)) z≤ h*Real.exp (C z)) : ‖shade W p x (tank P A) X‖ ≤ tier h A.val * Real.exp (rueD (bloom Q (Q*W*X*P) μ)/2 +∑ z: LeanV n,C z) :=by
 have hh:Q*(Q*W*X*P)=Q*W*X*P:=by simp only [←mul_assoc,show Q*Q=Q from g.1]; -- tune
 let V:= Δ; let T:=bloom Q (Q*W*X*P) μ; unfold shade; apply le_trans (shadow (Hutch.cosy g d b _) g (Hutch.worth_f g d b hh) v _); rw [←act_mul (quant _),←quant_mul,Real.exp_add, mul_left_comm (tier _ _)]; exact mul_le_mul_of_nonneg_left (settle d b g c t u A y e o) (Real.exp_pos _).le
end
lemma cheer(A:Dough n)(p:0≤h): tier h (exp A).val ≤ Real.exp (tier h A.val):=by
 let R:= tier h A.val; let w(k:ℕ):=(Nat.factorial k:ℝ)⁻¹; have he(k:ℕ): tier h (A^k).val≤ R^k:=by
    induction k with
    | zero=> rw [pow_zero,pow_zero]; exact (white1 _).le
    | succ i ih=> rw [pow_succ',pow_succ',Subalgebra.coe_mul]; exact (tier_mul p _ _).trans (mul_le_mul_of_nonneg_left ih (Pastry.pitch p _))
 have hp:= exp_series_hasSum_exp' (𝕂:=ℝ) A; have hu:= exp_series_hasSum_exp' (𝕂:=ℝ) R; rw [Real.exp_eq_exp_ℝ]; refine le_of_tendsto_of_tendsto' ( (Bellprep (n:=n) h).continuousAt.tendsto.comp hp.tendsto_sum_nat) hu.tendsto_sum_nat (fun k=>?_)
 change tier _ ((∑ i ∈range k,w i • A^i : Dough n).val)≤ ∑ i∈range k,w i • R^i; rw [show ((∑ i∈range k,w i • A^i : Dough n).val)=∑ i∈range k,(w i • A^i : Dough n).val from map_sum (Dough n).val _ _]; -- tune
 apply (tier_sum p _ _).trans; refine sum_le_sum fun i _=>?_ ; rw [Subalgebra.coe_smul,whiteℝ,Real.norm_of_nonneg (by unfold w; positivity)]; exact mul_le_mul_of_nonneg_left (he i) (by unfold w; positivity)
end Fist
end YM.CF.Fock.Reduction
