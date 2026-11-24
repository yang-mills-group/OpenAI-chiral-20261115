import YM.SU5.FiniteGaugeData.Jadot.Dijon
/-! # Beam price with upper and lower triangle, tissue blow-up suppression.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims Dijon Currency Fist
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Ziz
variable {n:Type*} [LinearOrder n][Fintype n]{A B K P Q Y D L X M N W U:Op n}{a b d e μ ν h k s v w z r x:ℝ}
section
variable (c:IsStarProjection P){x:Wave n}
-- generalize from Fist:
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
include c
lemma list_fist (t:P*X=P)(j:‖quant (U*X*P)‖≤a) (p:List (LeanV n))(x:Wave n)(f:acts (quant P) x=x): ‖acts (quant U) (acts ((p.map (drawT P)).prod) (acts (quant X) x))‖≤ ((p.map (TwistReceipt (U*(1-P)))).prod)*(a*‖x‖):=by
 let F:=U*(1-P); let C:=TwistReceipt F; have hx:0≤a:=(norm_nonneg _).trans j
 let J(x:Wave n):=acts (quant X) x; let K(x:Wave n):=acts (quant U) x; change ‖K _‖≤(p.map C).prod*(a*‖x‖)
 induction p generalizing x with
 | nil=>
   change ‖acts (quant U) (acts (1:FC n) (J x))‖≤ 1 * (a*‖x‖); rw [act_one,one_mul]; unfold J; rw [←act_mul,←quant_mul]; nth_rw 1 [←f]; rw [←act_mul,←quant_mul]; exact (wing_opy ..).trans (mul_le_mul_of_nonneg_right j (norm_nonneg _))
 | cons i s ih=>
   cases i with | mk q i =>
   cases q
   · let v:=acts P (basisKet i); let Z:=remove v; have hp:drawT P (false,i)=Z:=by change hideF P i=Z; unfold hideF; rw [prong_t] -- implicit
     have he: ‖v‖≤1:=(Flare.opy _ _).trans (by rw [show ‖basisKet i‖=(1:ℝ) from by simp [basisKet],mul_one]; exact c.norm_le _)
     have hu:acts (star X) v=v:=by unfold v; rw [←act_mul, show star X*P=P from ?_]; nth_rw 1 [←c.2.star_eq]; rw [← star_mul,t,c.2.star_eq]
     have hh:acts (quant P) (acts Z x)=acts Z x:=by nth_rw 2 [← f]; rw [←act_mul,←act_mul,show Z*quant P=quant P* Z from ?_]; unfold Z; rw [quant_ann,c.2.star_eq,show acts P v=v from by unfold v; rw [←act_mul,c.1]] -- tune let
     rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,show C (false,i)=1 from rfl,one_mul]; let S:= (s.map (drawT P)).prod
     have hx: ‖K (acts (S*drawT P (false,i)) (J x))‖≤ (s.map C).prod * (a*‖x‖):=by
         rw [hp,act_mul]; unfold J; rw [←act_mul Z,show Z*quant X=quant X*Z from ?_,act_mul]; swap; · unfold Z; rw [quant_ann,hu]
         apply le_trans (ih (acts Z x) hh); apply mul_le_mul_of_nonneg_left  (mul_le_mul_of_nonneg_left ((wing_opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((Flare.cost_pe true v).trans he))) hx); apply List.prod_nonneg; intro y hy; obtain ⟨z,-,rfl⟩:= List.mem_map.mp hy; unfold C TwistReceipt; split; exact norm_nonneg _; norm_num -- tune
     obtain ⟨Y,hY,hy⟩:= antiset c s (false,i); rcases hY with hY|hY <;> rw [hY,hy]; exact hx; rw [act_neg]; unfold K; rw [map_neg,norm_neg]; exact hx
   · rw [List.map_cons,List.prod_cons, List.map_cons,List.prod_cons,act_mul]; unfold K; rw [show drawT P (true,i) = create (acts (1-P) (basisKet i)) from ?_, ←act_mul, quant_create,act_mul]; swap; · unfold drawT seekF; rw [if_pos rfl,prong_p]
     apply le_trans (wing_opy _ _); rw [←act_mul U,show U*_ = F from rfl]; rw [mul_assoc]; exact mul_le_mul (Flare.cost_pe false (acts F (basisKet i))) (ih x f) (norm_nonneg _) (norm_nonneg _)
variable {C:LeanV n→ℝ}
omit c [Nonempty n] in
private lemma rowR {m:Type*}[LinearOrder m][Fintype m](S:Finset m)(F:m→FC n)(C:m→ℝ):∃ L:List m, column F S=(L.map F).prod ∧ (L.map C).prod=∏ z∈S,C z:=by refine ⟨S.sort (· ≤ ·),rfl,?_⟩; rw [← List.prod_toFinset C (sort_nodup ..), sort_toFinset] -- tune
omit c [Nonempty n] in
private lemma rowPrice {m:Type*}[LinearOrder m][Fintype m](Y:FC m)(W:FC n)(x:Wave n)(o:m→FC n)(C:ℝ)(hp:∀S:Finset m, ‖acts W (acts (column o S) x)‖ ≤ h^S.card*C): ‖acts W (acts (∑ s:Finset m, crumb Y s • column o s) x)‖ ≤ tier h Y * C:=by
 rw [act_sum,map_sum]; unfold tier; rw [sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum (fun (i:Finset m) _=>?_)); rw [act_smul,map_smul,norm_smul,mul_comm (h^_),mul_assoc]; exact mul_le_mul_of_nonneg_left (hp i) (norm_nonneg (crumb Y i))
lemma harvest (t:P*X=P)(j:‖quant (U*X*P)‖ ≤a)(u:Sea P x)(A:ribbon n)(y:0≤h)(e:∀z,0≤C z)(o:∀ z:LeanV n,TwistReceipt (U*(1-P)) z≤ h*Real.exp (C z)) : ‖acts (quant U) (acts (tank P A) (acts (quant X) x))‖ ≤ tier h A.val * (Real.exp (∑ z:LeanV n,C z)*a):=by
 let H:=Real.exp (∑ z,C z); let F:=TwistReceipt (U*(1-P)); have ha:0≤a:=(norm_nonneg _).trans j
 have hp (S:Finset (LeanV n)): ‖acts (quant U) (acts (column (drawT P) S) (acts (quant X) x))‖ ≤ h^S.card*(H*a):=by
    obtain ⟨L,hL,hk⟩:= rowR S (drawT P) F; have hz:=list_fist c t j L x (sea_idke c u); change ‖acts (quant U) _‖≤(L.map F).prod * (a*‖x‖) at hz; rw [u.2,mul_one,hk] at hz; rw [hL, ←mul_assoc]; refine hz.trans (mul_le_mul_of_nonneg_right ?_ ha); calc
       _ ≤ ∏ z∈S,h*Real.exp (C z) := prod_le_prod (fun i _=> by change 0 ≤ F i; unfold F TwistReceipt; split; exact norm_nonneg _; norm_num) (fun i _=>o i)
       _ ≤ h^S.card*H := by rw [prod_mul_distrib,prod_const, ← Real.exp_sum]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>e i))) (pow_nonneg y _)
 exact rowPrice (m:=LeanV n) A.val (quant U) (acts (quant X) x) (drawT P) (H*a) hp
end
end
-- assembled SOR rates. v fee global dimension at true estimate. Separate Gauge plank.
section
variable [Nonempty n]{N₀ U₀ L₀ R W₁:Op n}
structure Badge (P X R W B:Op n)(u c a b v e:ℝ):Prop where
 p:IsStarProjection P
 r:IsStarProjection R
 nearE : kg (P-R)≤e
 walks : kg (X*P-R)≤e
 grip : P*X=P
 TrueFrame: Priced (W*R-B) a b
 ref : ‖B‖≤1
 norm : ‖W‖≤u
 pod : cellU univ W c
 great:0<v
namespace Badge
variable (FI:Badge P X R W B s w a b v e)
local notation "Π"=> Fintype.card n
include FI
lemma pax : kg (W*P-B)≤2*(b+s^2*e):=by
 rw [show W*P-B=(W*R-B)+W*(P-R) from by noncomm_ring]; apply kg_plus FI.TrueFrame.sc; rw [mul_comm]; exact kg_lft FI.nearE FI.norm
lemma pixels : Priced (W*X*P-B) (a+(v*Π+ v⁻¹*(s^2*e))) (2*(b+s^2*e)):=by
 rw [show W*X*P-B=(W*R-B)+W*(X*P-R) from by noncomm_ring]; exact FI.TrueFrame.plusP (Priced.fromKg ((kg_lft FI.walks FI.norm).trans_eq (mul_comm ..)) FI.great)
abbrev resale (P W B:Op n)(z:LeanV n):ℝ:=if z.1 then (cellZ (W*P-B) z.2)^2 else 0
abbrev Pig(s a b v e:ℝ):= a+3*b+(3+v⁻¹)*(s^2*e)
variable {x': Wave n}
lemma bubble(j:ℝ)(g: w+2≤h)(l:Sea P x')(A:ribbon n)(τ:tier h A.val≤ Real.exp j): ‖acts (quant W) (acts (tank P A) (acts (quant X) x'))‖ ≤ Real.exp (j + v*Π + Pig s a b v e):=by -- x' add variable
 let H:=W*P-B; let U(i:n):=cellZ H i; let D:= resale P W B
 have hu:0≤w:=let i:= Classical.arbitrary n; le_trans (norm_nonneg _) (FI.pod i (mem_univ _))
 have hx:0< h:=by linarith
 have hh(i:LeanV n):0≤ D i:=by unfold D resale; split; exact sq_nonneg _; exact le_rfl
 have hv(z:LeanV n):TwistReceipt (W*(1-P)) z ≤ h*Real.exp (D z):=by
    cases z with | mk i v =>
    cases i
    · change 1≤ h*Real.exp 0; rw [Real.exp_zero,mul_one]; linarith
    change cellZ _ v ≤ h*Real.exp ((U v)^2); have e1:0≤U v:= cellZ_nn ..
    have t:cellZ (W*P) v ≤ U v+1:=by apply le_trans (b:=cellZ H v+cellZ B v) _ (add_le_add le_rfl ((cellZ_norm ..).trans FI.ref)); nth_rw 1 [←sub_add_cancel (W*P) B]; exact cellZ_add .. -- syntax
    rw [mul_sub,mul_one]; apply le_trans ((cellZ_sub ..).trans (add_le_add (FI.pod v (mem_univ _)) t)); refine (mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((U v)^2)) hx.le).trans' ?_; nlinarith only [e1,g,hu,sq_nonneg (U v-1),mul_nonneg hu (sq_nonneg (U v)),mul_le_mul_of_nonneg_right g (sq_nonneg (U v))]
 let Q:= a+(v*Π+ v⁻¹*(s^2*e)) + 2*(b+s^2*e)/2; have he: ‖quant (W*X*P)‖≤ Real.exp Q:=by
    nth_rw 1 [←sub_add_cancel (W*X*P) B,add_comm]; exact volupt FI.pixels FI.ref
 apply (harvest FI.p FI.grip he l A hx.le hh hv).trans; apply (mul_le_mul_of_nonneg_right τ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
 have ht: (∑ z,D z)=kg H:=by rw [Fintype.sum_prod_type]; simp [D,H,resale,kg_I,cellZ] -- binder z
 rw [ht]; have hz:=FI.pax; change kg H ≤ _ at hz; unfold Q Pig; nlinarith only [hz]
end Badge
end
end Ziz
end YM.CF.Fock.Reduction
