import Anomaly.Market.Tariff
/-!
Route lights carried by Vote's argument. Here all real angles only. Use afterwards
at linear/angular components allowed. Packed.Wave.P
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Regis.Head.GeometryP
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ ε Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f l m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
open CF.Swell.Sonar Garland Etch Next.Free Push.Local
-- use Complex outer and exposure real (norm charge one).
variable {I J:Type*} [Fintype I][Fintype J] {T D:ℝ} (L:Tour I n)(O:I→ Site n)
-- physical Mark=PPE standing, formula true and closed.Core. C(x)= x*(PPE). Inputs from Ord normalization.
variable (Pp: I→ Config G n→ℂ)(focusL:ℂ→L[ℝ] ℝ)(ov:‖focusL‖≤1)
def booth (U:Config G n):ℝ:= focusL (∏ i:I,Pp i (pull (L.orient i) (L.loc i) U))
def seats (L:Tour I n)(O:I→ Site n): I→ Site n:=fun i=> affine (L.orient i) (L.loc i) (O i)
def scopes(I':J→Tour I n) (O:I→ Site n) : Prop:=∀ i, Injective fun j=> seats (I' j) O i
lemma scope_shift (s:Signed)(b:Site n)(i:I): seats (L.moves s b) O i=affine s b (seats L O i):=by simp [seats,affine,Tour.moves, Signed.act_mul]; try ring -- tune affine simplify
lemma scopes_on (s:Signed)(b: Site n){E:J→Tour I n}(h:scopes E O) : scopes (fun i=>(E i).moves s b) O:=fun i r t p=> h i ((turnSites s b).injective (by change seats _ _ _=seats _ _ _ at p; simp_rw [scope_shift] at p; exact p))
lemma booth_pulled(s:Signed)(b:Site n)(U:Config G n): booth L Pp focusL (pull s b U)=booth (L.moves s b) Pp focusL U:=by unfold booth; simp_rw [pull_pull]; rfl
variable (W:I→ tableQ G n ℂ)(q:Clip)(D ε':ℝ)
def imagined (Y:Altar G n):= focusL (∏ i,coverT (W i) (L.orient i) (L.loc i) q ε' D Y)
def actualW (Y:Altar G n):= focusL (∏ i,crystalT (W i) (L.orient i) (L.loc i) q ε' Y)
lemma foresees : ContDiff ℝ 1 (imagined L focusL W q D ε') := focusL.contDiff.comp (contDiff_prod fun i _=> smoothEarn ..)
include ov
lemma contracts (x:ℂ):|focusL x|≤ ‖x‖:= (Real.norm_eq_abs _).symm.trans_le ((focusL.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) ov)) -- include
lemma observes (u:0<D)(h:∀ i,costs (W i) ≤ T)(Y:Altar G n): |imagined L focusL W q D ε' Y| ≤((2*D)^2*T)^Fintype.card I:= by
 apply (contracts focusL ov _).trans; rw [norm_prod]; apply (prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> (potQ _ _ _ _ ε' _ u Y).trans (mul_le_mul_of_nonneg_left (h i) (sq_nonneg _)))).trans_eq; rw [prod_const,card_univ]
variable (EΩ:J→ Tour I n)
def columnV (x:Altar G n):ℝ:= ∑ j, imagined (EΩ j) focusL W q D ε' x -- EΩ binder section order!
abbrev rentΦ (q:Clip)(ε D T:ℝ)(n:ℕ):ℝ:= (1+(2*D)^2*T)^n*(n:ℝ)*steed q ε D T
omit ov
lemma boundsProd {X Y:I→ℂ}{R:ℝ}(h:∀ i,‖X i‖≤R)(g:∀ i,‖Y i‖≤R)(r:1 ≤ R)(N:Finset I):
 ‖(∏ i∈N,X i)-(∏ i∈N,Y i)‖≤ R^N.card*∑ i∈N,‖X i-Y i‖:=by
 induction N using Finset.induction_on with
 | empty=>simp
 | insert i s v ih=>
   let A:=∏ i∈s,X i; let W:=∏ i∈s,Y i; let U:=∑ i∈s,‖X i-Y i‖; have he:0≤R:=zero_le_one.trans r; have hp:‖W‖≤ R^s.card:=by unfold W; rw [norm_prod]; exact (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>g i)).trans_eq (by simp)
   rw [prod_insert v,prod_insert v,sum_insert v,card_insert_of_notMem v,pow_succ']; change ‖X i*A-Y i*W‖≤ _*_ *(_ + U); rw [show X i*A-Y i*W=X i*(A-W)+(X i-Y i)*W from (by ring)]; refine (norm_add_le ..).trans ((add_le_add ((norm_mul ..).le.trans (mul_le_mul (h i) ih (norm_nonneg _) he)) ((norm_mul ..).le.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _)))).trans (?_)); change R*(R^s.card*U)+ ‖X i-Y i‖ * R^s.card≤ R*R^s.card*(_+U); nlinarith only [mul_le_mul_of_nonneg_left r (show 0≤ ‖X i-Y i‖ * R^s.card from by positivity)]
include ov
lemma slipBill (u:0<D)(h:∀ i,costs (W i)≤T)(p:0 ≤ T)(z:scopes EΩ O)(y:Altar G n) : ‖fderiv ℝ (columnV focusL W q D ε' EΩ) y‖ ≤ rentΦ q ε' D T (Fintype.card I) *Real.sqrt (Fintype.card J):=by
 let V:= Fintype.card I; let C:=1+(2*D)^2*T; let A:=rentΦ q ε' D T V; let B:=Real.sqrt (Fintype.card J); let R:ℝ≥0:=⟨A*B,by unfold A B rentΦ steed crayon Etch.rays; positivity⟩
 apply norm_fderiv_le_of_lipschitz ℝ (C:=R); refine LipschitzWith.of_dist_le_mul (fun x y=>?_)
 let H(i:J)(j:I)(x:Altar G n):= coverT (W j) ((EΩ i).orient j) ((EΩ i).loc j) q ε' D x; rw [dist_eq_norm,dist_eq_norm,columnV,columnV,←sum_sub_distrib]
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>C^V*∑ j:I, ‖H i j x-H i j y‖) (fun i _=>?_)).trans ?_)
 · unfold imagined; rw [←map_sub,Real.norm_eq_abs]; refine (contracts focusL ov _).trans (?_); have ht:1 ≤ C:=le_add_of_nonneg_right (by positivity); have hp(j:I)(x):‖H i j x‖≤ C:= ((potQ (W j) _ _ q ε' D u x).trans (mul_le_mul_of_nonneg_left (h j) (sq_nonneg _))).trans (le_add_of_nonneg_left zero_le_one) -- u
   exact (boundsProd (fun i=>hp i x) (fun i=>hp i y) ht univ).trans_eq (by rw [card_univ])
 rw [←mul_sum,sum_comm]; refine (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>steed q ε' D T*(B*‖x-y‖)) (fun i _=>usageS _ _ _ (fun j=>(EΩ j).orient i) (fun j=>(EΩ j).loc i) _ (z i) _ _ u (h i))) (by unfold C; positivity)).trans_eq (?_); rw [sum_const,card_univ,nsmul_eq_mul]; change _= A*B*_; unfold A rentΦ C V; ring
omit ov
lemma belief (q:Clip)(P:Attached H Z)(B:Z.Bounds q η C S)(s:Signed)(b:Site n)(v:Dir G n): imagined (L.moves s b) focusL W q D ε' (tiler B P v)=imagined L focusL W q D ε' (tiler B P (bank s b v)):=by unfold imagined; refine congrArg focusL (prod_congr rfl fun i _=> carries ..)
variable {q}
lemma pricing(o:Tour I n)(h:Copied o EΩ)(B:Z.Bounds q η C S)(P:Attached H Z){δ v:ℝ}(L_:Floor H q n δ v)(u:Bid.Sworn H n G)(q':ℝ)(e:∀ L:Tour I n,Integrable (fun x:stamen B P n=>imagined L focusL W q D ε' x.val) (stdGaussian (stamen B P n))) : plumeCost B P (columnV focusL W q D ε' EΩ) q'=Fintype.card J* (q'*clouds B P (imagined o focusL W q D ε')):=by
 rw [plumeCost, cloud_turn B P (columnV focusL W q D ε' EΩ) ((show ContDiff ℝ 1 (columnV focusL W q D ε' EΩ) from ContDiff.sum (fun k (_:k∈(univ:Finset J))=> foresees ..)).continuous)]
 have hh(i:J): clouds B P (imagined (EΩ i) focusL W q D ε')= clouds B P (imagined o focusL W q D ε'):=by
    obtain ⟨s,t,g⟩:=h.copy i; rw [g]; exact (cover_calms s t B P L_ u _ _ (foresees ..|>.continuous) (fun i=> Eq.symm (belief o _ _ _ _ _ _ _ _ _ i))).symm -- tune
 unfold clouds columnV; rw [integral_finsetSum univ (fun i _=> e _)]
 unfold clouds at hh; simp_rw [hh]; rw [sum_const,card_univ,nsmul_eq_mul,mul_left_comm]
end YM.Regis.Head.GeometryP
