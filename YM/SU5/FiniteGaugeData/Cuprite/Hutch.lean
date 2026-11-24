import YM.SU5.FiniteGaugeData.Cuprite.Pose
/-! # Baseline purchase. η margin and t guaranteed together. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Cascade Brique Real NormedSpace MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n][DecidableEq n]{A B P Q Y D X U:Op n}{a r μ b:ℝ}
abbrev spring(Q A:Op n):Op n:=A*star A+(1-Q)
def bloom(Q A:Op n)(μ:ℝ):Op n:=spring Q A + μ • Q
-- α
namespace Hutch
variable (q:IsStarProjection Q)(w:0<μ)(d:μ ≤ 1)
include q w d
private lemma coola(A:Op n): bloom Q A μ =A*star A + (Canon n μ + (1-μ) • (1-Q)):= by
 unfold bloom spring Canon; rw [sub_smul,smul_sub,smul_sub,one_smul,one_smul]; abel
omit q w d in
lemma bloom_zero (Q A:Op n): bloom Q A 0=spring Q A:=by unfold bloom; rw [zero_smul,add_zero]
lemma cozy_floor (A:Op n) : Canon n μ ≤ bloom Q A μ:=by
 rw [coola q w d]; exact ( (le_add_of_nonneg_right (smul_nonneg (sub_nonneg.mpr d) q.one_sub.nonneg))).trans (le_add_of_nonneg_left (by cfc_tac))
lemma cosy (A:Op n): lit (bloom Q A μ):= lit_of_fee w (cozy_floor q w d A)
lemma spin_f(A:Op n) : A*star A≤bloom Q A μ:=by rw [coola q w d]; exact le_add_of_nonneg_right (add_nonneg (canon_nn w.le) (smul_nonneg (sub_nonneg.mpr d) q.one_sub.nonneg))
lemma worth_f(h:Q*A=A): Q*bloom Q A μ*Q+(1-Q) = bloom Q A μ:=by
 have he :star A * Q=star A:= by nth_rw 1 [← show star Q=Q from q.2]; rw [←star_mul,h]
 unfold bloom spring; simp only [mul_add,add_mul,mul_sub, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,show Q*Q=Q from q.1,←mul_assoc Q,h, mul_assoc A,mul_one,he,sub_self,add_zero]
 abel -- tune
lemma petaline(A:Op n): let T:=tangle (bloom Q A μ); ‖T*A‖ ≤ 1:=by
 intro T; have ht:= cosy q w d A; have hc:0≤T:=refl_nn (lit_inv ht).1; apply own2 _ zero_le_one
 rw [star_mul,IsSelfAdjoint.of_nonneg hc,←mul_assoc (T*A),mul_assoc T A]; -- syntax
 refine le_trans (b:=T*bloom Q A μ*T) ?_ (le_of_eq (b:=Canon _ (1 ^ 2)) ?_); -- tune
 · exact IsSelfAdjoint.of_nonneg hc|>.conjugate_le_conjugate (spin_f q w d A)
 · rw [show T*(bloom Q A μ)*T= _ from tangle_n ht, one_pow,Canon,one_smul]
lemma tangle_power(A:Op n): ‖tangle (bloom Q A μ)‖≤(Real.sqrt μ)⁻¹:=by
 let H:=bloom Q A μ; let T:=tangle H; have h:= cosy q w d A; change ‖T‖≤_; have he: ‖star T*T‖= ‖T‖*‖T‖:= CStarRing.norm_star_mul_self; rw [show star T=T from refl_star (lit_inv h).1, show T*T=H⁻¹ from intake_t h] at he
 have hz:=inv_power h w (cozy_floor q w d A); change ‖H⁻¹‖≤_ at hz; have ht: μ⁻¹ = ((Real.sqrt μ)⁻¹)^2 :=by rw [inv_pow,Real.sq_sqrt w.le]
 rw [he,ht] at hz; nlinarith [norm_nonneg T, show 0≤(Real.sqrt μ)⁻¹ from by positivity]
-- priceVs underlying projection, H >= μ I.
lemma inv_lgp (h:lit (spring Q A))(e:‖D‖^2 ≤ μ/2): (bloom Q (A+D) μ)⁻¹ ≤ (2:ℝ) • (spring Q A)⁻¹ := by
 let Z:=D*star D
 have hD:Z ≤ Canon n (μ/2):= by apply le_trans CStarAlgebra.mul_star_le_algebraMap_norm_sq; rw [canon_map]; exact algebraMap_mono _ e
 let B:=A+D; let Y:=B*star B; let X:=A*star A
 have hp: X ≤ Y+Z+ (Y+Z) := by
    apply sub_nonneg.mp; have he: (Y+Z)+(Y+Z)-X=(A+D+D)*star (A+D+D):=by unfold Y B X Z; simp only [star_add,add_mul,mul_add]; abel
    rw [he]; exact mul_star_self_nonneg _
 let K:=bloom Q B μ; let L:= spring Q A
 -- aim L ≤ 2 K. L= X+(1-Q), K≥Y+Canon μ but losing complement. actual diff remainder +(1-Q)+2μQ. pays D both (≤μ I) since 1≥μ.
 have hm:L ≤ K + K:=by
    let R:=Canon n (μ/2); apply le_trans (b:= (Y+(Y+(R+R)))+(1-Q))
    · refine add_le_add (hp.trans ((by abel : Y+Z+(Y+Z)= Y+(Y+(Z+Z))) ▸ ?_)) le_rfl -- tune ▸
      exact add_le_add le_rfl (add_le_add le_rfl (add_le_add hD hD))
    have he:R+R=Canon n μ:=by unfold R Canon; rw [←add_smul, add_halves] -- lemma
    have hw:Canon n μ≤ (1-Q)+μ • Q:=by simpa [bloom,spring] using (cozy_floor q w d 0) -- tune
    have hx:Canon n μ≤ (1-Q)+μ • Q+μ • Q:= hw.trans (le_add_of_nonneg_right (smul_nonneg w.le q.nonneg))
    rw [he]; apply (add_le_add (add_le_add le_rfl (add_le_add le_rfl hx)) (le_refl (1-Q))).trans_eq; unfold K bloom spring Y; abel
 have hu:(1/2:ℝ) • L ≤ K:= (smul_le_smul_of_nonneg_left hm (by norm_num: (0:ℝ) ≤1/2)).trans_eq (by rw [smul_add,←add_smul]; norm_num)
 apply le_trans (inv_order (lit_smul (a:=1/2) h (by norm_num)) hu); rw [inv_fee (show lit L from h) (by norm_num:(0:ℝ)<1/2)]; norm_num; rfl
omit q w d
lemma TrR_cov(h:star A=A)(B C:Op n): TrR (A*(B*star C))=TrR (A*(C*star B)):=by rw [←TrR_star,star_mul,star_mul,star_star,h,TrR_comm]
-- no uniform op norm req on inv at base
structure Hot(Q A:Op n):Prop where
 projection : IsStarProjection Q
 active: Q*A=A
 live : lit (spring Q A)
include w d
abbrev Poem(Q A D:Op n):ℝ:=TrR ((spring Q A)⁻¹ * (A*star D))
def horizonM (Q A:Op n)(μ r:ℝ):ℝ:= (μ+r^2)*TrR ((spring Q A)⁻¹)/2
lemma poem_cost(h:Hot Q A)(D:Op n)(e:‖D‖≤r): rueD (bloom Q (A+D) μ)/2 ≤ rueD (spring Q A)/2 + Poem Q A D + horizonM Q A μ r := by
 let K:=spring Q A; let H:=bloom Q (A+D) μ; have he: lit K:= h.live; have hp: lit H:= cosy h.projection w d (A+D); have hz:= route_log hp he; have hK:0≤K⁻¹:= (lit_inv he).1
 have hb: H-K=(A*star D+D*star A)+(D*star D+μ • Q):=by unfold H K bloom spring; simp only [star_add,add_mul,mul_add]; abel
 rw [hb,mul_add,mul_add,mul_add,TrR_add,TrR_add,TrR_add,TrR_cov (show star K⁻¹=K⁻¹ from IsSelfAdjoint.of_nonneg hK) D A] at hz
 have ha:TrR (K⁻¹*(D*star D)) ≤ r^2 * TrR K⁻¹ :=by
    refine le_trans (b:=‖D*star D‖*TrR K⁻¹) ((abs_le.mp (TrR_quote hK _)).2) (mul_le_mul_of_nonneg_right ?_ (TrR_nn hK)); rw [CStarRing.norm_self_mul_star,←sq]; exact pow_le_pow_left₀ (norm_nonneg _) e _
 have hv:TrR (K⁻¹*(μ • Q)) ≤ μ* TrR K⁻¹:=by
    refine le_trans ((abs_le.mp (TrR_quote hK (μ • Q))).2) (mul_le_mul_of_nonneg_right ?_ (TrR_nn hK)); rw [norm_smul,Real.norm_of_nonneg w.le]; exact mul_le_of_le_one_right w.le (h.projection.norm_le _)
 change rueD H/2 ≤ rueD K/2+TrR (K⁻¹ * (A*star D))+(μ+r^2)*TrR K⁻¹/2; linarith
end Hutch
end YM.CF.Fock.Reduction
