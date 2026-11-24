import YM.SatinExist.Giverny
/-!
 # `MintK`: fund the applicant as real resolvent price. No growth or POV assumptions.
-/
set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 330000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "ρ" => volume.restrict (Ioi (0:ℝ))
local notation "ρ'" => Ioi (0:ℝ)
local notation "μ" => Measure.prod (volume.restrict (Ioi (0:ℝ))) (volume.restrict (Ioi (0:ℝ)))
local notation "E" => elast S
abbrev moneyK (u:ℝ):ℂ:=thermalMass n u
local notation "R"=> moneyK n
local notation "K"=>Cache S
abbrev mill (v:ℝ):= R v • E v
lemma mill_pays : Integrable (mill S n) ρ:=by
 have h:Continuous (moneyK n):=by unfold moneyK thermalMass; fun_prop
 have he:ContinuousOn (mill S n) ρ':= fun x d=> ((h.continuousAt.smul (elast_good S d))).continuousWithinAt
 exact ((mass_set n).norm).mono' (he.aestronglyMeasurable measurableSet_Ioi) (Eventually.of_forall (fun x=> by change ‖(_ :ℂ) • E x‖ ≤ ‖thermalMass n x‖; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _) |>.trans_eq (Complex.norm_real (thermalMass n x)))) -- trans issue
lemma mintK_eq : Cache S (n+1)= ∫ x,mill S n x ∂ρ:=by
 ext1 z; rw [← ticket_sym,meter]; exact (ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.apply ℂ H.space z) (mill_pays S n))
variable (A:ℝ → H.Op) (P:ℝ) (C:Currency S A)(hp:0<P)(h:∀ᶠ x in Λ,‖A x‖≤ P/x^n)
local notation "GW" => escrow S A
include C
lemma covenant {x t:ℝ}(p:0<x)(q:x≤t): ‖A t‖ ≤ ‖A x‖:=by
 rw [C t x p q]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))))
omit C in
lemma expenseK (x y:ℝ): ‖GW x y‖ ≤ ‖A (min x y)‖:=by
 unfold escrow; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))))
include hp h
lemma wcapped : ∃ D:ℝ→ℝ, Integrable D ρ ∧ ∀ x, 0<x → ‖R x‖ * ‖A x‖ ≤ D x:=by
 obtain ⟨q,w,v⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp h
 let k:= thermalMass n; have h₀ : Integrable (thermalMass 0) ρ:=mass_set _; let K' (x:ℝ):= ‖thermalMass 0 x‖ * P + ‖k x‖*‖A q‖
 refine ⟨K', (h₀.norm.mul_const P).add ((mass_set _).norm.mul_const _), fun x p=> ?_⟩
 change ‖(k x:ℂ)‖*‖A x‖ ≤ _ ; unfold K'; rw [Complex.norm_real]
 rcases le_or_gt x q with t|t
 · refine le_add_of_le_of_nonneg ((mul_le_mul_of_nonneg_left (show ‖A x‖ ≤ _ from (show ‖A x‖ ≤ P/(x^n) from v ⟨p,t⟩)) (norm_nonneg _)).trans ?_) (mul_nonneg (norm_nonneg _) (norm_nonneg _)); rw [Real.norm_of_nonneg (mass_sign n p.le),Real.norm_of_nonneg (mass_sign 0 p.le)]; unfold thermalMass; simp only [pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one]
   change Real.exp (-x)*x^n/_*(P/x^n) ≤ _; have hF:1≤(n.factorial:ℝ):=by exact_mod_cast n.factorial_pos
   rw [show Real.exp (-x)*x^n/ (n.factorial:ℝ)*(P/x^n)= Real.exp (-x)*P/(n.factorial:ℝ) from (by field_simp)]
   exact div_le_self (mul_pos (Real.exp_pos _) hp).le hF
 exact le_add_of_nonneg_of_le (mul_nonneg (norm_nonneg _) hp.le) (mul_le_mul_of_nonneg_left (covenant S A C w t.le) (norm_nonneg _))
-- no Hausdorff-SOT fudge. Bill actual normalized two-sided continuous heat operators.
def paysR (p:ℝ×ℝ): H.Op:= (R p.1 * R p.2) • GW p.1 p.2
def allK : H.Op:= ∫ x, paysR S n A x ∂ μ
lemma priceR : Integrable (paysR S n A) μ:=by
 obtain ⟨k,d,c⟩:= wcapped S n A P C hp h; have t:Integrable (fun v=> ‖R v‖) ρ:= (mass_set _).norm.congr (Eventually.of_forall fun x=> (Complex.norm_real _).symm); have e:k∈Set.univ:= trivial
 let W:= (ρ' ×ˢ ρ'); have p' : MeasurableSet W:= MeasurableSet.prod measurableSet_Ioi measurableSet_Ioi
 have v: μ = ((volume (α:=ℝ)).prod volume).restrict W:= Measure.prod_restrict .. -- tune
 refine ((d.mul_prod t).add (t.mul_prod d)).mono' (?_ : AEStronglyMeasurable (paysR S n A) _) ?_
 · have hR: Continuous R:=by unfold moneyK thermalMass; fun_prop
   rw [v]; exact ContinuousOn.aestronglyMeasurable (show ContinuousOn (paysR S n A) W from fun x ⟨hx,hy⟩=> (((((hR.comp continuous_fst).mul (hR.comp continuous_snd)).continuousAt (x:=x)).smul (cash_loc S A C hx hy))).continuousWithinAt) p'
 rw [v]; filter_upwards [ae_restrict_mem p'] with z hp'; rcases z with ⟨a,b⟩; obtain ⟨p,q⟩:= hp'
 have ht(a:ℝ)(g:0<a):0≤k a:=(mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (c a g)
 change ‖(R a * R b) • GW a b‖ ≤ k a* ‖R b‖ + ‖R a‖*k b; rw [norm_smul,norm_mul]; apply (mul_le_mul_of_nonneg_left (expenseK S A a b) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
 rcases le_total a b with e|e
 · rw [min_eq_left e,mul_right_comm]; exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right (c a p) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (ht b q))
 rw [min_eq_right e,mul_assoc]; exact le_add_of_nonneg_of_le (mul_nonneg (ht a p) (norm_nonneg _)) (mul_le_mul_of_nonneg_left (c b q) (norm_nonneg _))
lemma dibs (t:ℝ)(p:0<t): (K (n+1))*A t*K (n+1)= E t*allK S n A * E t:=by
 have he:=priceR S n A P C hp h
 let B:=ContinuousLinearMap.mul ℂ H.Op
 let L: H.Op →L[ℂ] H.Op:= (B.flip (E t)).comp (B (E t))
 let Z:= B.comp (B.flip (A t))
 have hv : μ = ((volume (α:=ℝ)).prod volume).restrict (ρ' ×ˢ ρ') := Measure.prod_restrict ..
 let W(z:ℝ×ℝ):= Z (mill S n z.1) (mill S n z.2)
 have H: (∫ z,W z ∂ μ)= ∫ z,L (paysR S n A z) ∂ μ:= by
    rw [hv]; refine integral_congr_ae ((ae_restrict_mem (MeasurableSet.prod measurableSet_Ioi measurableSet_Ioi)).mono fun x ⟨u,v⟩=>?_)
    let r:= x.1; let s:=x.2; change (R r • E r)* A t * (R s • E s)= E t*((R r* R s) • GW r s)*E t; rw [smul_mul_assoc,smul_mul_assoc,mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_smul,fortune S A C p u v]
 change Z (K (n+1)) (K (n+1))=L (allK S n A); rw [mintK_eq,← integral_prod_bilin Z (mill_pays S n) (mill_pays S n),allK,← ContinuousLinearMap.integral_comp_comm _ he]; exact H
omit h hp C
-- Rules to compute the operator at a phase. Not every U starts with the costs.
def RealMint (A:ℝ→H.Op)(Z:H.Op):Prop:=∀ t:ℝ≥0,0<t→ A (t:ℝ)= Par S n t * Z * Par S n t
lemma realMint_eq (A:ℝ→H.Op)(Z:H.Op): RealMint S n A Z ↔ ∀ t:ℝ≥0,0<t → K n*A t*K n=S.E t*Z*S.E t:=by
 constructor
 · intro q t u; rw [q t u]; simp only [mul_assoc]
   rw [← mul_assoc (K n),P_Heq S t n u,show Par S n t * K n=S.E t from (change_m S n _ (dur.mpr u)).trans (S.roots_heat u)]
 intro q t u; suffices he:∀ A B:H.Op,K n * A * K n=K n * B * K n → A=B from he _ _ (Eq.trans (q t u) (by
   rw [← show Par S n t * K n=S.E t from (change_m S n _ (dur.mpr u)).trans (S.roots_heat u)]; nth_rw 1 [←((gear S _ (dur.mpr u) n).pow_left n).eq]; change _= K n* (Par S n t*Z*Par S n t)* K n; simp only [mul_assoc]))
 intro A' B t; have hk:IsSelfAdjoint (K n):= (saucer_sym S).pow _
 have hp: (K n)*A'=(K n)*B:=by
   apply star_injective; rw [star_mul,star_mul,hk.star_eq]; apply DFunLike.ext _ _
   intro x; apply cache_I S n; have ht:= congrArg star t; simp_rw [star_mul,hk.star_eq] at ht; exact DFunLike.congr_fun ht x
 ext1 x; exact cache_I S n (DFunLike.congr_fun hp x)
lemma RealMint.increases (Z:H.Op) (q:RealMint S n A Z)(m:ℕ) : RealMint S (m+n) A ((K m)*Z*(K m)):=by
 apply (realMint_eq ..).mpr; intro t v; rw [cacheA]
 calc
    _= K m*(K n*A t*K n)*K m:=by nth_rw 2 [((Commute.refl (saucer S)).pow_left m|>.pow_right n).eq]; simp only [mul_assoc] -- tune. matching
    _= S.E t*(K m*Z*K m)*S.E t:=by rw [(realMint_eq ..).mp q t v]; simp only [mul_assoc]; rw [← mul_assoc (K m), ←mul_assoc (S.E t) (K m) (Z*_), ((cupE S t).pow_left m).eq] 
include hp C h
lemma funds_heat : RealMint S (n+1) A (allK S n A):=by
 apply (realMint_eq ..).mpr; intro t g; have H:= dibs S n A P C hp h ↑t (show 0 < (t:ℝ) from g); simpa only [elast,Real.toNNReal_coe] using H
end YM.SatinJets
