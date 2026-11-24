import Anomaly.Market.Jewel
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Regis.Head.GeometryP
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ ε Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
open CF.Swell.Sonar Garland Etch Next.Free
variable {I J:Type*} [Fintype I][Fintype J] {T D:ℝ}
lemma sumFace (v: J→ Cell n)(h:Injective v)(x:Altar G n) : (∑ i:J, ‖cup (v i) x‖) ≤ Real.sqrt (Fintype.card J)*‖x‖:=by
 let S(i:J):= v i; let Z(i:J):= ‖cup (S i) x‖; let f(i: J × G.ColorIndex) : Cell n×Bool×G.ColorIndex:=(S i.1,false,i.2)
 have hf:Injective f:=by
    rintro ⟨a,b⟩ ⟨c,d⟩ g; have hz:b=d:=congrArg (fun i:Cell n × Bool × G.ColorIndex => i.2.2) g; exact Prod.ext (h (congrArg Prod.fst g)) hz
 have hx: (∑ i:J,Z i^2) ≤ ‖x‖^2:=by
    let U(w):=x w^2
    rw [EuclideanSpace.real_norm_sq_eq]; refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (f:=U) (subset_univ (univ.image f)) (fun w _ _=> sq_nonneg _))
    rw [sum_image (fun _ _ _ _=> hf.eq_iff.mp), Fintype.sum_prod_type]; unfold Z; simp_rw [EuclideanSpace.real_norm_sq_eq]; exact le_rfl
 have hu:=le_trans (Real.sum_mul_le_sqrt_mul_sqrt univ (fun i:J=>1) Z) (mul_le_mul_of_nonneg_left (le_trans (Real.sqrt_le_sqrt hx) (Real.sqrt_sq (norm_nonneg x)|>.le)) (Real.sqrt_nonneg _)); simpa only [one_pow,one_mul,sum_const,card_univ,nsmul_eq_mul,mul_one] using hu

abbrev crayon (q:Clip)(ε:ℝ):ℝ:= tariffLip*rays q ε
-- shifted canon anchors: a is affine origin gauge-zero of word-ball. require separated shots at shifted *reference-root*, not necessarily injective a. bounding even if a not injective. 
lemma candle (q:Clip)(g:Signed)(a:Site n)(ε:ℝ)(j:TrackKey G n)(x y:Altar G n)(h:0<D):
     |snub D (giveAt g a q ε x j)-snub D (giveAt g a q ε y j)| ≤ crayon q ε * ‖cup (Face.send g a j.1) (x-y)‖:=by
 apply le_trans (cutter D h _ _); rw [crayon,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold giveAt; let i:=Face.send g a j.1
 dsimp only; rw [← mul_sub]; let U:= river q i (x-y)
 have ht: (river q i (x-y)) j.2=(river q i x) j.2-(river q i y) j.2:=by rw [map_sub]; rfl
 rw [← ht,abs_mul,abs_mul]; have h:(|turned g j.1.2|)=1:=by nlinarith only [sq_abs (turned g j.1.2),turned_sq g j.1.2,abs_nonneg (turned g j.1.2)]
 rw [h,one_mul]; refine (mul_le_mul_of_nonneg_left (each U j.2) (abs_nonneg ε)).trans (le_of_eq ?_)
 unfold U river Etch.rays; simp [norm_smul, Real.norm_eq_abs,mul_assoc,i,abs_of_nonneg (Real.sqrt_nonneg _)] -- tune
where each(u:G.Color)(j:G.ColorIndex): |u j| ≤ ‖u‖:=by
       rw [← EuclideanSpace.basisFun_inner]; simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ j) u

lemma candleS (q:Clip)(d:TrackKey G n)(ε:ℝ) (g:J→Signed)(a:J→Site n)(o:Site n)(p:Injective (fun i=> affine (g i) (a i) o))(x y:Altar G n)(h:0<D):
     (∑ i:J,|snub D (giveAt (g i) (a i) q ε x d)-snub D (giveAt (g i) (a i) q ε y d)|) ≤ crayon q ε * (Fintype.card Signed*(Real.sqrt (Fintype.card J)* ‖x-y‖)):=by
 let F(i:J)(s:Signed) := Face.send s ((affine (g i) (a i) o)-s.act o) d.1
 have ht(i:J): Face.send (g i) (a i) d.1= F i (g i):=by unfold F affine; rw [add_sub_cancel_left]
 have he(s:Signed): Injective (fun i=>F i s):=by
    intro i j H; apply p; have h:=congrArg Prod.fst H; change Face.lower d.1 s _= Face.lower d.1 s _ at h
    unfold Face.lower atFace affine at h; simp only [add_left_inj] at h; simpa [affine] using h -- tune
 refine (sum_le_sum (fun i _=> (candle q (g i) (a i) ε d x y h).trans (?_ : _≤ crayon q ε *∑ s:Signed, ‖cup (F i s) (x-y)‖))).trans ?_
 · apply mul_le_mul_of_nonneg_left _ (by unfold crayon Etch.rays; positivity); rw [ht i]; exact single_le_sum (fun j _=>norm_nonneg (cup (F i j) (x-y))) (mem_univ _)
 rw [←mul_sum,sum_comm]; apply mul_le_mul_of_nonneg_left _ (by unfold crayon Etch.rays; positivity); refine (sum_le_sum (g:=fun s=> Real.sqrt (Fintype.card J)* ‖x-y‖) (fun s _=> sumFace _ (he s) _)).trans_eq (?_); rw [sum_const,card_univ,nsmul_eq_mul]

variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] (P_:tableQ G n X)
abbrev steed (q:Clip)(ε D T:ℝ):= T*(2*((1+2*D)^2*(crayon q ε* Fintype.card Signed)))
lemma usageS (q:Clip)(ε:ℝ)(g:J→Signed)(a:J→Site n)(o:Site n)(p:Injective (fun i=> affine (g i) (a i) o))(x y:Altar G n)(h:0<D)(w:costs P_≤T):
     (∑ i:J,‖coverT P_ (g i) (a i) q ε D x-coverT P_ (g i) (a i) q ε D y‖) ≤ steed q ε D T*(Real.sqrt (Fintype.card J)* ‖x-y‖):=by
 let N:=ChainKey G n; let B:= 1+2*D; have ht:1 ≤ B:=le_add_of_nonneg_right (by positivity)
 let W(i:J)(x:Altar G n)(d:TrackKey G n):= snub D (giveAt (g i) (a i) q ε x d)
 unfold coverT tariff; simp_rw [← sum_sub_distrib, ←sub_smul];
 let Z(k:N)(i:J):= ((∏ j,W i x (k j))-(∏ j,W i y (k j))) • P_ k
 refine (sum_le_sum (g:=fun i:J=> ∑ k, ‖Z k i‖) (fun i _=> norm_sum_le ..)).trans ?_; rw [sum_comm]
 let F:=Real.sqrt (Fintype.card J) *‖x-y‖; let K:= crayon q ε; have hF:0≤ F:=by unfold F; positivity
 have hK:0≤K:=by unfold K crayon Etch.rays; positivity
 have hp(k:N) : (∑ i:J,‖Z k i‖) ≤ B^2*(2:ℕ)*(K*Fintype.card Signed)*F*‖P_ k‖:=by
    have h0(i:J)(k:N)(x:Altar G n)(j):|W i x (k j)| ≤ B:= (snub_budget h _).1.trans (le_add_of_nonneg_left zero_le_one)
    let Y(i:J):=∑ j, |W i x (k j)-W i y (k j)|
    have hv:(∑ i:J,Y i) ≤ 2*(K*(Fintype.card Signed*F)) :=by unfold Y; rw [sum_comm]; refine (sum_le_sum (fun i _=> candleS q (k i) ε g a o p x y h)).trans_eq (?_); rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rfl
    refine (sum_le_sum (g:=fun i:J=> (B^2*Y i)*‖P_ k‖) (fun i _=>?_)).trans ?_
    · unfold Z; rw [norm_smul,Real.norm_eq_abs]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); apply (products_margin univ (h0 i k x) (h0 i k y) ht).trans_eq (?_); rw [card_univ,Fintype.card_fin]
    rw [←sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hv (sq_nonneg _)).trans_eq (?_)) (norm_nonneg _); push_cast; ring
 refine (sum_le_sum (fun i _=>hp i)).trans ?_; rw [←mul_sum]; change _*costs P_ ≤ _; refine (mul_le_mul_of_nonneg_left w (by positivity)).trans_eq (?_); unfold steed; unfold B F K; push_cast; ring
end YM.Regis.Head.GeometryP
