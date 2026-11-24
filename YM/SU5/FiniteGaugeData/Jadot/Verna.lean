import YM.SU5.FiniteGaugeData.Jadot.Dijon
/-! # Regularization paid at cubic angular cost. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Verna
variable {n:Type*} [Fintype n][DecidableEq n]{A B C P Q L D W:Op n}{a b s r μ:ℝ}
lemma regEx (h:lit A)(p:0≤μ): lit (A+Canon n μ):=by
 have he:A≤ A+Canon n μ:=le_add_of_nonneg_right (canon_nn p); exact ⟨h.1.trans he,CStarAlgebra.isUnit_of_le _ he h⟩
-- trick diagonalize only *L* (L=tangle A). Instead of needing positive spectrum invert d, represent resolvent at A* as S via parallel pencil.L.Verify formula symbol =L²/(1+ μ L²) without spectral A.
lemma frugal (h:lit A)(p:0≤μ) : A⁻¹-(A+Canon n μ)⁻¹ ≤ Real.sqrt μ • (tangle A * A⁻¹):=by
 let S:= A⁻¹; let L:= tangle A; let Z:=A+Canon n μ; have hx : L*L=S:= intake_t h; have he: lit L:=refl_live (lit_inv h); obtain ⟨U,d,T⟩:=spectral_exists L he.isSelfAdjoint; have hz:0≤d:= (spectral_le U ..).mp (by rw [spectral_zero,← T]; exact he.1)
 let f(i:n):= 1+μ*(d i)^2; let g(i:n):= (f i)⁻¹ -- tune parsing
 have hg :0≤g:= fun i=>inv_nonneg.mpr (add_nonneg zero_le_one (mul_nonneg p (sq_nonneg _))) -- tune
 let W:=spectral U f; let Y:= spectral U g; have ht: W=1+μ • S:=by rw [←hx, T,spectral_mul, spectral_smul U μ,←spectral_one U,spectral_add]; exact congrArg (spectral U) (by ext i; change 1+μ*(d i)^2=1+μ*(d i*d i); ring)
 have hh: Z⁻¹=S*Y:=by
    apply inv_red (regEx h p); rw [←mul_assoc,show Z*S=W from by unfold Z; rw [add_mul,canon_left,show A*S=1 from lit_mulin h,ht]]; unfold W Y; rw [spectral_mul,← spectral_one U]; exact congrArg (spectral U) (funext (fun i=>mul_inv_cancel₀ (show f i≠0 from (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg p (sq_nonneg _))).ne'))) -- tune parsing
 let c:= Real.sqrt μ; change S-Z⁻¹ ≤ c • (L*S); unfold Y at hh; rw [hh, ←hx, T,spectral_mul,spectral_mul,spectral_mul,spectral_sub,spectral_smul,spectral_le]; intro i; let x:=d i; let f0:=1+μ*x^2; change x*x-x*x*f0⁻¹ ≤ c*(x*(x*x)); have hc:0≤ c:=by unfold c; positivity
 have hx:0≤x:= hz i; have hp:f0>0:= by unfold f0; positivity
 have hu: μ=c^2:= (Real.sq_sqrt p).symm
 rw [←div_eq_mul_inv]; apply (le_of_mul_le_mul_right _ hp); rw [sub_mul,div_mul_cancel₀ _ hp.ne']; unfold f0; rw [hu]; calc
    _ = x^2 * ((c*x)^2) := by ring
    _ ≤ x^2 * (c*x*(1+(c*x)^2)) := by
       have he: c*x ≤ 1+(c*x)^2:= by nlinarith only [sq_nonneg (c*x-1),sq_nonneg (c*x)]
       apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); rw [sq (c*x)]; -- prolif both
       exact mul_le_mul_of_nonneg_left (by rw [←sq]; exact he) (mul_nonneg hc hx)
    _ = _:=by ring
lemma ennui (q:IsStarProjection Q)(h:lit (Rheims.frost Q P 0))(r:0≤μ):
 (Rheims.frost Q P 0)⁻¹-(Rheims.frost Q P μ)⁻¹ ≤ Real.sqrt μ • (Lumi Q P 0)^3:=by
 let S:=Rheims.frost Q P 0; let T:=Rheims.frost Q P μ; let G:=S+Canon n μ; have he:T≤G:=by
    unfold G S T Rheims.frost; rw [bloom_zero]; exact add_le_add le_rfl (smul_le_smul_of_nonneg_left q.le_one r) -- tune lemma
 let L:=Lumi Q P 0; have hu:L*S⁻¹=L^3:=by rw [show L^3=L*L^2 from pow_succ' L 2,sq, show L*L=S⁻¹ from intake_t h] -- tune l rhs
 refine (sub_le_sub le_rfl (inv_order ?_ he)).trans ((frugal h r).trans_eq (by rw [show tangle S*S⁻¹=L^3 from hu])) -- local let mism
 apply ice q _ r; change lit (bloom Q (Q*P) 0) at h; rwa [bloom_zero] at h
-- cost columns of L change
lemma cstarMul (e:‖A‖≤1): star A*A ≤ 1:= le_trans CStarAlgebra.star_mul_le_algebraMap_norm_sq ((algebraMap_mono _ (show ‖A‖^2≤1 from by nlinarith only [e,norm_nonneg A])).trans_eq (map_one _))
lemma thinner(h:Commute A W)(w:0≤W)(p:‖A‖≤1): star A*W*A≤W:=by
 let R:= ReflW W; have he:Commute R A:= sqrt_comm h.symm; have hz:star R=R:=refl_star w; have hh:star A*R=R*star A:=by
    conv_lhs=> right; rw [←hz]
    conv_rhs=> left; rw [←hz]
    rw [←star_mul,←star_mul,he.eq]
 have ht:R*R=W:= refl_sq w; have hw : R*(star A*A)*R=star A*W*A:= by rw [←ht]; rw [←mul_assoc R,←hh, mul_assoc (star A*R),←he.eq,mul_assoc (star A),mul_assoc (star A),←mul_assoc R] -- tune
 rw [←hw]; exact (IsSelfAdjoint.conjugate_le_conjugate (cstarMul p) hz).trans_eq (by rw [mul_one,ht])
lemma paleA (h: Commute L W)(v:0≤L)(p:L≤W) : L^3≤ W^3:=by
 let K:= W-L; have he:Commute L K:= h.sub_right (Commute.refl L); have hs:0≤W:=v.trans p; have hy:Commute W K:=(Commute.refl W).sub_right h.symm
 have ho : L^2 ≤ W^2:=by apply sub_nonneg.mp; have hk:= (show L≤W from p); have hh:= diff_pos h p v; rw [sq,sq]; exact le_trans ((star_mul_self_nonneg K).trans_eq (by rw [IsSelfAdjoint.of_nonneg (show 0≤K from sub_nonneg.mpr p)])) hh -- trans_eq tune
 have hz:Commute W (W^2-L^2):= ((Commute.refl W).pow_right 2).sub_right (h.symm.pow_right 2)
 have hl:Commute K (L^2):=he.symm.pow_right 2
 apply sub_nonneg.mp; rw [show W^3-L^3=W*(W^2-L^2)+K*(L^2) from by unfold K; noncomm_ring]; exact add_nonneg (Commute.mul_nonneg hs (sub_nonneg.mpr ho) hz) (Commute.mul_nonneg (sub_nonneg.mpr p) (by rw [sq]; exact Commute.mul_nonneg v v (Commute.refl _)) hl) -- pow ∈
/- Bound with a point-majorant on all Fourier-spin blocks. -/
variable (p:IsStarProjection P)(q:IsStarProjection Q)
local notation "L" t:max => Lumi Q P t
local notation "K" t:max => Rheims.frost Q P t
local notation "A0"=> Q*P*(1-Q)
structure Booster(Q P:Op n)(W:Op n)(C:ℝ):Prop where
 base:IsStarProjection Q
 iceE:IsStarProjection P
 live: lit (Rheims.frost Q P 0)
 arm: (Rheims.frost Q P 0)⁻¹≤ W*W
 deal: Commute (Rheims.frost Q P 0)⁻¹ W
 safe: 1≤W
 soft : Commute (Q*P*(1-Q)) W
 volume :∀ i:n, ((W^3) i i).re ≤ C
 positive:0≤C
namespace Booster
variable(d:Booster Q P W a)
include d
lemma te(v:0≤μ) : lit (Rheims.frost Q P μ):=ice d.base (by have h:=d.live; unfold Rheims.frost at h; rwa [bloom_zero] at h) v
lemma upperB : Lumi Q P 0 ^3≤ W^3:=by
 have h:=d.live; apply paleA (sqrt_comm d.deal) (pole d.base h).litA.1; exact (CFC.sqrt_le_sqrt _ _ d.arm).trans_eq (CFC.sqrt_mul_self W (zero_le_one.trans d.safe))
lemma kgA(v:0≤μ): star (Lumi Q P μ)*Lumi Q P μ ≤ W^3:=by
 let H:= Rheims.frost Q P μ; have h:star (L μ)=L μ:= (pole d.base (d.te v)).upperR; rw [h,intake_t] -- abbreviation `rw` might
 have hx:Commute (W*W) (W-1):= (((Commute.refl W).mul_left (Commute.refl W))).sub_right (Commute.one_right _)
 have he:0≤W:= zero_le_one.trans d.safe; have ht:W*W≤W^3:=by apply sub_nonneg.mp; rw [show W^3-W*W=(W*W)*(W-1) from by noncomm_ring]; exact Commute.mul_nonneg (Commute.mul_nonneg he he (Commute.refl _)) (sub_nonneg.mpr d.safe) hx
 exact (inv_order d.live (frost_order d.base v)).trans (d.arm.trans ht)
 exact d.te v
lemma ledger_b (v:0≤ s)(t:s≤μ): star (L s-L μ)*(L s-L μ) ≤ Real.sqrt μ • W^3:=by
 have l:star (L s)=L s:=(pole d.base (d.te v)).litA.isSelfAdjoint; have h:=d.te (v.trans t); rw [star_sub,l,(pole d.base h).upperR]; refine (lumi_diff d.base (d.te v) t h).2.trans ?_; apply le_trans (b:= (Rheims.frost Q P 0)⁻¹-(Rheims.frost Q P μ)⁻¹); · exact sub_le_sub (inv_order d.live (frost_order d.base v)) le_rfl
 exact (ennui d.base d.live (v.trans t)).trans (smul_le_smul_of_nonneg_left d.upperB (Real.sqrt_nonneg _))
local notation "π" x:max => Zami Q P x
lemma ledger_c(v:0≤ s)(t:s≤μ): let V:=Zami Q P s-Zami Q P μ; let M:= Real.sqrt μ • W^3; star V*V≤M ∧ V*star V≤M:=by
 let A:=Q*P*(1-Q); let E:=L s-L μ; intro V M; have hC: ‖A‖≤1:=by
    have he:‖Q*P‖≤1:=(norm_mul_le ..).trans (mul_le_one₀ (d.base.norm_le _) (norm_nonneg _) (d.iceE.norm_le _)); exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) d.base.one_sub.norm_le).trans he) -- tune `norm_le` arg
 have h0:0≤ star E*E:= star_mul_self_nonneg E; have he:V=E*A:=by unfold V E A Zami; rw [sub_mul]; simp only [mul_assoc]
 have hx:= d.ledger_b v t; have hw:star E=E:= ((pole d.base (d.te v)).litA.isSelfAdjoint.sub ((pole d.base (d.te (v.trans t))).litA.isSelfAdjoint)); have hu: Commute A M:= (d.soft.pow_right _).smul_right _
 rw [he]; constructor
 · rw [star_mul,←mul_assoc,mul_assoc (star A)]; exact (star_left_conjugate_le_conjugate hx A).trans (thinner hu (h0.trans hx) hC)
 have ht:A*star A ≤1:=by have hh:=cstarMul (show ‖star A‖≤1 from (norm_star A).trans_le hC); rwa [star_star] at hh
 rw [star_mul,hw,←mul_assoc,mul_assoc E]; refine (IsSelfAdjoint.conjugate_le_conjugate ht hw).trans ?_; rw [mul_one]; exact ((show E*E=star E*E from congrArg (·*E) hw.symm)).trans_le hx
lemma bonus (v:star A*A≤ b • W^3)(t:0≤b):cellU univ A (Real.sqrt (b*a)):=by
 intro i _; unfold cellZ; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp; rw [caible,Real.sq_sqrt (mul_nonneg t d.positive)]; refine (Drama.Pack.comp_pay v i).trans ?_; rw [Matrix.smul_apply,Complex.smul_re,smul_eq_mul]; exact mul_le_mul_of_nonneg_left (d.volume i) t
lemma visits(v:0≤μ): cellU univ (Lumi Q P μ) (Real.sqrt a):=by simpa only [one_mul] using (d.bonus (b:=1) (by rw [one_smul]; exact d.kgA v) zero_le_one)
lemma Change (v:0≤ s)(t:s≤μ): let r:=Real.sqrt (Real.sqrt μ*a); cellU univ (Lumi Q P s-Lumi Q P μ) r ∧ cellU univ (π s-π μ) r ∧ cellU univ (star (π s-π μ)) r:=by
 refine ⟨d.bonus (d.ledger_b v t) (Real.sqrt_nonneg _), d.bonus (d.ledger_c v t).1 (Real.sqrt_nonneg _), d.bonus (by rw [star_star]; exact (d.ledger_c v t).2) (Real.sqrt_nonneg _)⟩
end Booster
end Verna
end YM.CF.Fock.Reduction
