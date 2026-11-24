import YM.CF.Hove.Twine
import YM.CF.Hove.Trim
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

-- TWO tariff from rooted pair cost p≥2. Large/small displacements split shared (no two payments!)
variable {ι:Type*}[Fintype ι]
variable(m:ℕ)(p:2 ≤ m)(H:ι→ℝ)(a b l r t u:ι→ℂ)(g k w L B C D x y:ℝ)
local notation "U"=>paidX
variable (hp:∀ i,1≤ H i)
def recL (V:ι→ℝ)(a b t:ι→ℂ):Prop:= paidX (1:ι→ℝ) t ≤ C*k ∧ paidX V a ≤ C*k ∧ paidX V b ≤ C*((1+x)/L*k) ∧ paidX V t ≤ C*((1+x/L)^m*k) ∧ paidX V (t-(a+b)) ≤ C*((1+x)^m/L^2*k)
lemma chargeO (Z Z':ι→ℝ)(u:0≤Z)(h:Z ≤ Z')(x:ι→ℂ):paidX Z x ≤ paidX Z' x:= sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)
lemma yak (V V':ι→ℝ)(h:0≤V')(hh:V'≤V)(p: recL m k L C x V a b t): recL m k L C x V' a b t:=⟨p.1,(chargeO V' V h hh a).trans p.2.1,(chargeO V' V h hh b).trans p.2.2.1,(chargeO V' V h hh t).trans p.2.2.2.1,(chargeO V' V h hh _).trans p.2.2.2.2⟩
variable(hA:1 ≤ L)(uX:0≤x)(uY:0 ≤ y)(hB:0≤k)(pC:0≤C)(pD:0≤D)
local notation "ℒ"=>max x y
include hA uX hB pC in
lemma hangV (v:C ≤ D)(h:recL m k L C x H a b t): recL m k L D x H a b t:= by
 rcases h with ⟨i,l,b,r,k'⟩; refine ⟨i.trans ?_,l.trans ?_,b.trans ?_,r.trans ?_,k'.trans ?_⟩ <;> gcongr -- incl
-- combine lipid proof
local notation "q"=> ((1+max x y)^m/L^2)
local notation "Q"=> (dishV t u-billY a b l r)
variable (h:recL m k L C x H a l t)(e: recL m k L D y H b r u)
include p hp hA uX uY hB pC pD
lemma large_v (αL : L ≤ ℒ)(X:ℝ)(hv:0 ≤ X)(hx:X ≤ ℒ): (1+X/L)^m ≤ 2^m*q ∧1 ≤ q ∧ (1+ℒ)/L ≤ q:=by
 let z:=ℒ; let yP:=1+z; have hl:L≤ z:=αL; have hZ:X≤z:=hx; have hz:0<L:=lt_of_lt_of_le zero_lt_one hA; have hv:L^2>0:=by positivity
 have hk : yP^2≤ (1+ℒ)^m:= pow_le_pow_right₀ (by unfold yP z; linarith) p
 refine ⟨?_ , ?_,?_ ⟩
 · rw [←mul_div_assoc, le_div_iff₀ hv]; let w:= 1+X/L; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA p) (by positivity)); rw [←mul_pow,←mul_pow]; apply pow_le_pow_left₀ (by positivity); calc
     _ = L+X:=by field_simp
     _ ≤ _:=by change _≤2*yP; unfold yP; linarith
 · rw [le_div_iff₀ hv,one_mul]; apply le_trans _ hk; apply pow_le_pow_left₀ hz.le (by unfold yP; linarith)
 rw [le_div_iff₀ hv]; refine le_trans ?_ hk; calc
   _ = yP * L:=by unfold yP z; field_simp
   _ ≤ yP ^2:=by
              have hy':L≤yP:=by unfold yP; linarith
              exact (mul_le_mul_of_nonneg_left hy' (by positivity)).trans_eq (pow_two _).symm
variable {W V:ι→ℝ}
include h e
lemma hog (hw:0 ≤ W)(hv:0 ≤ V)(uP:W ≤ H)(vP:V ≤ H)(s:W=1∨V=1) : paidX (coilF W V) Q ≤ ((2:ℝ)^m+4)*q*(C*k*(D*k)):=by
 have ht:0 ≤ ℒ:=uX.trans (le_max_left ..)
 have hb:=yak m a l t k L C x H W hw uP h -- order?
 have hy:=yak m b r u k L D y H V hv vP e
 obtain ⟨uW,va,lb,lt,lr⟩:=hb; obtain ⟨pW,ya,ps,pt,pk⟩:=hy
 let B:=1+ℒ; have hP:1≤ B:=le_add_of_nonneg_right ht
 have hj:0 < L:=lt_of_lt_of_le zero_lt_one hA
 have hl:U W l ≤ C*(B/L*k):=lb.trans (by unfold B; gcongr; exact le_max_left ..)
 have hr:U V r ≤ D*(B/L*k):=ps.trans (by unfold B; gcongr; exact le_max_right ..)
 by_cases K:ℒ≤ L
 · let yd:=ℒ; have he:B≤2*L:=by unfold B; linarith
   have hc:U W (t-(a+l))≤ C*(q*k):=lr.trans (by gcongr; exact le_max_left ..)
   have hz:U V (u-(b+r))≤D*(q*k):=pk.trans (by gcongr; exact le_max_right ..)
   have hc':U V u≤(2:ℝ)^m*(D*k):=by
      refine pt.trans ?_; calc
         _ ≤ D*((2:ℝ)^m*k):=by gcongr; apply le_trans (add_le_add_right ((div_le_one hj).mpr ((le_max_right ..).trans K)) 1) (by norm_num)
         _ =_:=by ring
   exact mintK W V a b l r t u q k (2^m) L B C D hw hv hA hP pD he pC hB va ya hl hr hc hz hc' (by positivity) (by rw [div_pow]; exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hP p) (by positivity)) -- tune
 let J:=q; have hm:=large_v m p H k L C D x y hp hA uX uY hB pC pD (le_of_not_ge K)
 have ha:=hm x uX (le_max_left ..); have hy:=hm y uY (le_max_right ..);
 have hh:U (coilF W V) (dishV t u) ≤ (2^m*q)*(C*k*(D*k)):=by
    rw [dish_p]; cases s with
    | inl h=> rw [h]; apply (mul_le_mul uW (pt.trans (show _≤D*((2^m*q)*k) from mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy.1 hB) pD)) (windL _ _ hv) (mul_nonneg pC hB)).trans; apply le_of_eq; ring
    | inr h=> rw [h]; apply (mul_le_mul (lt.trans (show _≤ C*((2^m*q)*k) from mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.1 hB) pC)) pW (windL _ _ (fun _=>zero_le_one)) (by positivity)).trans; apply le_of_eq; ring
 have hν:0 ≤ coilF W V:=fun i=>mul_nonneg (hw _) (hv _)
 rw [sub_eq_add_neg]; refine (p_sum (fun i=> hν i) _ _).trans ((add_le_add hh ?_).trans_eq (show (2^m*q)*(C*k*(D*k))+4*q*(C*k*(D*k))=_ by ring))
 rw [p_negative]; unfold billY; refine (p_sum (fun i=> hν i) _ _).trans ((add_le_add (p_sum (fun i=> hν i) _ _) (le_refl _)).trans ?_); simp_rw [dish_p]
 have hL:U W l≤C*(q*k):=hl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.2.2 hB) pC)
 have hg:U V r≤D*(q*k):=hr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.2.2 hB) pD)
 apply (add_le_add (add_le_add (mul_le_mul va ya (windL _ _ hv) (mul_nonneg pC hB)) (mul_le_mul va hg (windL _ _ hv) (mul_nonneg pC hB))) (mul_le_mul hL ya (windL _ _ hv) ((windL _ _ hw).trans hL))).trans; let X:= C*k*(D*k); have hh':0≤ X:=by unfold X; positivity
 calc
    _ = (1+2*q)*X:=by unfold X; ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (by linarith [ha.2.1]) hh'
lemma hoop : paidX (coyF H) Q ≤ 2*((2:ℝ)^m+4)*q*(C*k*(D*k)):=by
 have ht:0 ≤ (1:ι→ℝ):= fun _=>zero_le_one
 have hV:0 ≤ H:= ht.trans hp; rw [fork_p]; exact (add_le_add (hog m p H _ _ _ _ _ _ k L C D x y hp hA uX uY hB pC pD h e hV ht le_rfl hp (Or.inr rfl)) (hog m p H _ _ _ _ _ _ k L C D x y hp hA uX uY hB pC pD h e ht hV hp le_rfl (Or.inl rfl))).trans_eq (by ring) -- tune
end YM.CF.Hove
