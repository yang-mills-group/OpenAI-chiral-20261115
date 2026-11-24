import YM.SU5.FiniteGaugeData.Cuprite.Hutch
/-! # Whole comparison calculations in Schatten. Cover/missing etc. ANY precision at this mean.
Quantified license reusable for Mark. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Cascade -- kg
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n][DecidableEq n]{A B P Q Y D X U W R S T:Op n}{a r μ b h C v u k e δ:ℝ}
namespace Drama
-- global E fixed in use, multiplicative modulus. use serial tune.
structure Burrow(e k a:ℝ)(X Y:Op n):Prop where
 left: ‖X‖≤ a
 right: ‖Y‖≤ a
 hs : kg (X-Y) ≤ k*e
lemma Burrow.nn (p:Burrow e k a A B):0≤a:=(norm_nonneg _).trans p.left
lemma safe (p:‖A‖≤r): Burrow e 0 r A A:=⟨p,p,by rw [sub_self,zero_mul,kg]; simp⟩
lemma Burrow.plus (p:Burrow e k a A B)(q:Burrow e h r X Y): Burrow e (2*(k+h)) (a+r) (A+X) (B+Y):=by
 refine ⟨(norm_add_le ..).trans (add_le_add p.left q.left),(norm_add_le ..).trans (add_le_add p.right q.right),?_⟩; rw [show A+X-(B+Y)=(A-B)+(X-Y) from by abel]; refine (kgs ..).trans ((mul_le_mul_of_nonneg_left (add_le_add p.hs q.hs) zero_le_two).trans_eq (by ring))
lemma Burrow.mul (p:Burrow e k a A B)(q:Burrow e h r X Y): Burrow e (2*(k*r^2+h*a^2)) (a*r) (A*X) (B*Y):=by
 refine ⟨(norm_mul_le ..).trans (mul_le_mul p.left q.left (norm_nonneg _) p.nn),(norm_mul_le ..).trans (mul_le_mul p.right q.right (norm_nonneg _) p.nn),?_⟩
 rw [show A*X-B*Y= (A-B)*X+B*(X-Y) by noncomm_ring]; apply (kgs ..).trans; have ht:= (kg_b ..).trans (mul_le_mul p.hs (pow_le_pow_left₀ (norm_nonneg _) q.left 2) (sq_nonneg _) ((kgN _).trans p.hs)); have hu:= (kg_a ..).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) p.right 2) q.hs (kgN _) (sq_nonneg _)); exact (mul_le_mul_of_nonneg_left (add_le_add ht hu) zero_le_two).trans_eq (by ring)
lemma Burrow.starred(p:Burrow e k a A B): Burrow e k a (star A) (star B):=⟨(norm_star _).trans_le p.left,(norm_star _).trans_le p.right,by rw [←star_sub,kgt]; exact p.hs⟩
lemma Burrow.subv(p:Burrow e k a A B): Burrow e k a (-A) (-B):=⟨(norm_neg _).trans_le p.left,(norm_neg _).trans_le p.right,by rw [show -A- -B=(-1:ℝ) • (A-B) from by rw [neg_smul,one_smul]; abel, kt_can]; exact le_trans (by ring_nf; rfl) p.hs⟩ -- tune
lemma Burrow.negsub (p:Burrow e k a A B)(q:Burrow e h r X Y): Burrow e (2*(k+h)) (a+r) (A-X) (B-Y):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact p.plus q.subv
lemma Burrow.transf (p:Burrow e k a A B)(h:0≤e)(t:k≤C)(hx:‖A‖ ≤ r)(hy:‖B‖ ≤ r): Burrow e C r A B:=⟨hx,hy,p.hs.trans (mul_le_mul_of_nonneg_right t h)⟩
lemma Burrow.flipI(p:Burrow e k a A B)(x:lit A)(h:lit B)(l:‖A⁻¹‖ ≤ r)(u:‖B⁻¹‖≤r): Burrow e (r^4*k) r A⁻¹ B⁻¹ := by
 refine ⟨l,u,?_⟩; rw [show A⁻¹-B⁻¹=A⁻¹ *( B-A )* B⁻¹ by rw [mul_sub, sub_mul,lit_inmul x,mul_assoc,lit_mulin h,mul_one,one_mul]]
 have hc:= p.subv.hs; rw [neg_sub_neg] at hc; have hK: kg (A⁻¹*(B-A)) ≤ r^2*kg (B-A) := (kg_a ..).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) l _) (kgN _))
 apply (kg_b ..).trans; apply le_trans (mul_le_mul (hK.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg _))) (pow_le_pow_left₀ (norm_nonneg _) u 2) (sq_nonneg _) (mul_nonneg (sq_nonneg r) ((kgN _).trans p.hs))); exact le_of_eq (by ring)
variable [Nonempty n]
local notation "ε"=>‖W-1‖
lemma needy (p:IsStarProjection Q) (T:Op n): ‖Q*T‖ ≤ ‖T‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
lemma needy' (p:IsStarProjection Q)(T:Op n): ‖T*Q‖≤ ‖T‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (p.norm_le _))
-- purchase spherical finances. k:R∀... width art.
-- Q upper, P actual, R base.
open Hutch
structure Pack(μ M e:ℝ)(Q P R X W:Op n):Prop where
 p:IsStarProjection P
 q:IsStarProjection Q
 r:IsStarProjection R
 pos:0<μ
 smallB:μ≤1
 body: ‖W-1‖^2≤ μ/2
 unity : 1≤M
 live : lit (spring Q (Q*R))
 est : kg (X*P-R) ≤ e
 close : kg (P-R) ≤ e
 bound : ‖X*P‖ ≤ M
variable {M:ℝ}{z:Pack μ M e Q P R X W}
local notation "B₀" => Q*R
local notation "Ω"=>Q*W*X*P
local notation "Ξ"=> Q*W*R
local notation "Ω'"=> bloom Q Ω μ
local notation "Ξ'"=> bloom Q Ξ μ
namespace Pack
variable (Z:Pack μ M e Q P R X W)
include Z
lemma e_nn: 0≤e:= (kgN _).trans Z.est
lemma wrench: ε≤Real.sqrt μ:=by nlinarith only [Real.sq_sqrt Z.pos.le,Z.pos,Z.body,Real.sqrt_nonneg μ]
lemma roll : ε≤1:= Z.wrench.trans ((Real.sqrt_le_sqrt Z.smallB).trans (by norm_num))
lemma want: ‖W‖≤2:=by have hp:= Z.roll; nth_rw 1 [←sub_add_cancel W 1]; exact (norm_add_le ..).trans (by rw [norm_one]; linarith)
lemma stamp : ‖Q*W‖≤ 2:=(needy Z.q W).trans Z.want
lemma A_body: Burrow e 8 (2*M) Ω Ξ:=by
 have p:Burrow e 1 M (X*P) R:=⟨Z.bound,(Z.r.norm_le R).trans Z.unity, by rw [one_mul]; exact Z.est⟩; have ht:= (safe Z.stamp).mul p; rw [mul_assoc (Q*W)]; simpa only [zero_mul,one_mul,zero_add,(by norm_num:(2:ℝ)^2=4),(by norm_num:(2:ℝ)*4=8)] using ht
local notation "₳"=> (2*M)*(2*M) +1 +1
local notation "𝒞"=> 256*(2*M)^2
lemma A_cape : Burrow e 𝒞 ₳ Ω' Ξ':=by
 let K₀:=Z.A_body; unfold bloom spring; have ht:= ((K₀.mul K₀.starred).plus (safe (Z.q.one_sub.norm_le _))).plus (safe (show ‖μ • Q‖≤1 from by rw [norm_smul,Real.norm_of_nonneg Z.pos.le]; exact (mul_le_of_le_one_right Z.pos.le (Z.q.norm_le _)).trans Z.smallB)); apply ht.transf Z.e_nn _ ht.left ht.right; nlinarith [sq_nonneg (2*M)]
local notation "₭"=> (μ⁻¹)^4*𝒞
lemma A_inv : Burrow e ₭ μ⁻¹ Ω'⁻¹ Ξ'⁻¹:= Z.A_cape.flipI (cosy Z.q Z.pos Z.smallB _) (cosy Z.q Z.pos Z.smallB _) (inv_power (cosy Z.q Z.pos Z.smallB _) Z.pos (cozy_floor Z.q Z.pos Z.smallB _)) (inv_power (cosy Z.q Z.pos Z.smallB _) Z.pos (cozy_floor Z.q Z.pos Z.smallB _)) -- tune
local notation "₮"=> Q*W*(1-P)
local notation "₲"=> Q*W*(1-R)
lemma QVP : Burrow e 8 2 ₮ ₲:=by
 have ht:Burrow e 1 1 (1-P) (1-R):=⟨Z.p.one_sub.norm_le _,Z.r.one_sub.norm_le _,by
    have h:= ((⟨Z.p.norm_le _,Z.r.norm_le _,Z.close.trans_eq (one_mul e).symm⟩: Burrow e 1 1 P R)).subv.hs; rwa [show 1-P-(1-R)= -P- -R from by abel]⟩ -- tune exact
 have he:=(safe Z.stamp).mul ht; norm_num at he; exact he
omit [Nonempty n] Z in -- still kg nontriv ok
lemma adams (A X:Op n)(h:lit A): star ((tangle A)*X)*((tangle A)*X)=star X*A⁻¹*X:=by rw [star_mul,←mul_assoc,show star (tangle A)=tangle A from (refl_live (lit_inv h)).isSelfAdjoint,mul_assoc (star X),intake_t h]
local notation "₫"=> 2*( (2*(8*(μ⁻¹)^2 + ₭ * 2^2)) * 2^2 + 8 * (2*μ⁻¹)^2)
local notation "₻" => 2 * μ⁻¹ * 2
abbrev ωB(A X:Op n):Op n:= star (tangle A*X)*(tangle A*X)
lemma illuminated : Burrow e ₫ ₻ (ωB Ω' ₮) (ωB Ξ' ₲):=by
 unfold ωB; rw [adams _ _ (cosy Z.q Z.pos Z.smallB _),adams _ _ (cosy Z.q Z.pos Z.smallB _)]; exact (Z.QVP.starred.mul Z.A_inv).mul Z.QVP
local notation "Ξ⁰"=> spring Q (Q*R)
local notation "𝓤"=> Q*(W-1)*R
local notation "𝖩"=> Q*(1-R)
abbrev TierV(V M X:Op n) :=ωB (spring V (V*M)) X -- for K. useful.Uncompressed
abbrev pointM (n:Type*) [Fintype n][DecidableEq n](Q R:Op n)(C:ℝ): Prop:=∀i:n,‖acts (tangle (spring Q (Q*R)) * (Q*(1-R))) (basisKet i)‖ ≤ C -- may interface with sqrt. perhaps switch square lemma easier.
lemma wants_lgp : Ξ=B₀+𝓤:=by show Q*W*R=Q*R+Q*(W-1)*R; noncomm_ring
lemma needs : ‖𝓤‖≤ε:= (needy' Z.r _).trans (needy Z.q _)
omit [Nonempty n] Z in
lemma comp_pay (h:A≤B)(i:n): (A i i).re≤ (B i i).re:=by
 apply sub_nonneg.mp; change 0≤ ((B-A) i i).re; exact (Complex.le_def.mp ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).diag_nonneg)).1 -- tune binder
lemma card_led : Ξ'⁻¹ ≤ (2:ℝ) • Ξ⁰⁻¹:=by rw [Z.wants_lgp]; exact inv_lgp Z.q Z.pos Z.smallB Z.live ((pow_le_pow_left₀ (norm_nonneg _) Z.needs 2).trans Z.body)
lemma card_upper (k:pointM n Q R C)(i:n): ‖acts (tangle Ξ'*₲) (basisKet i)‖≤ 2*C+1:=by
 let B:= Ξ⁰; let t:= tangle (bloom Q (Q*W*R) μ); let Y:= Q*(1-R); let U:= Q*(W-1)*(1-R); let a:=basisKet i; let r:=tangle B; have ht:lit Ξ':= cosy Z.q Z.pos Z.smallB _
 have h:(star (t*Y)*(t*Y))≤(2:ℝ) • (star (r*Y)*(r*Y)):=by
    rw [show star (t*Y)*(t*Y)=_ from adams _ _ ht, show star (r*Y)*(r*Y)=_ from adams _ _ Z.live,←Algebra.smul_mul_assoc, ←Algebra.mul_smul_comm]; exact star_left_conjugate_le_conjugate Z.card_led Y -- direction tune
 have hK:= k i; change ‖acts (r*Y) a‖ ≤ C at hK; have hc:= (norm_nonneg _).trans hK
 have hx:= caible (t*Y) i; have hy:= caible (r*Y) i
 have hz: ‖acts (t*Y) a‖^2 ≤ 2*‖acts (r*Y) a‖^2:= by rw [show ‖acts (t*Y) a‖^2=_ from hx,show ‖acts (r*Y) a‖^2=_ from hy]; refine (comp_pay h i).trans_eq ?_; rw [Matrix.smul_apply,Complex.smul_re,smul_eq_mul] -- tune
 have hp: ‖acts (t*Y) a‖≤2*C:=by nlinarith [mul_le_mul hK hK (norm_nonneg _) hc,norm_nonneg (acts (t*Y) a)]
 have hh: ‖acts (t*U) a‖ ≤1:=by
    have he:‖U‖≤Real.sqrt μ := ((needy' Z.r.one_sub _).trans (needy Z.q _)).trans Z.wrench
    let K:= t*U; change ‖acts K a‖ ≤1
    refine ((acts K).le_opNorm a).trans ?_; rw [show ‖a‖=(1:ℝ) from by simp [a,basisKet],mul_one]
    exact (norm_mul_le ..).trans ((mul_le_mul (tangle_power Z.q Z.pos Z.smallB _) he (norm_nonneg _) (by positivity)).trans_eq (inv_mul_cancel₀ (Real.sqrt_pos.mpr Z.pos).ne'))
 change ‖acts (t*_) a‖≤_; rw [show Q*W*(1-R)=Y+U by unfold Y U; noncomm_ring, mul_add,act_add]
 exact (norm_add_le ..).trans (add_le_add hp hh)
-- royalty definitions public
-- choose labels cost ζ field baseline. false mark cost may as well 0. distinct BOTH. price θ finite for fixed μ.
def cardfee (Q P R X W:Op n)(μ:ℝ)(i:n):ℝ:=‖(ωB (bloom Q (Q*W*X*P) μ) (Q*W*(1-P))-ωB (bloom Q (Q*W*R) μ) (Q*W*(1-R))) i i‖
def RedAccount (μ M v:ℝ):ℝ:= v⁻¹* (2*( (2*(8*(μ⁻¹)^2 + (μ⁻¹)^4*(256*(2*M)^2) * 2^2)) * 2^2 + 8 * (2*μ⁻¹)^2))
lemma cardbill (k:0<v): (∑ i:n, cardfee Q P R X W μ i) ≤ v * Fintype.card n + RedAccount μ M v * e:=
 (tax_diag k _).trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_left Z.illuminated.hs (inv_nonneg.mpr k.le)).trans_eq (mul_assoc ..).symm)) -- tune type fail
lemma cardpoint (k:pointM n Q R C)(i:n)(p:2*C+2≤ h): ‖acts (tangle Ω' * ₮) (basisKet i)‖≤ h * Real.exp (cardfee Q P R X W μ i):=by
 let A:= ωB Ω' ₮; let B:= ωB Ξ' ₲; let K:=cardfee Q P R X W μ i; have ht:= Z.card_upper k i; let x:=basisKet i; let a:= ‖acts (tangle Ω'*₮) x‖; let c:= ‖acts (tangle Ξ'*₲) x‖; have hc:c≤2*C+1:=ht
 have hK:0≤K:=norm_nonneg _; have hz:a^2-c^2≤ K:=by
    rw [show a^2= _ from caible (tangle Ω'*₮) i, show c^2= _ from caible (tangle Ξ'*₲) i]; change ((A-B) i i).re≤‖(A-B) i i‖; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
 have he:c+1≤h:=by linarith
 have hp:0≤c:=norm_nonneg _
 have h0:0≤h:=by linarith
 change a ≤ h*_ ; apply le_trans (b:=c+1+K); · nlinarith only [hK,he,p,h0,hz,hp, mul_nonneg hp hK,sq_nonneg K]
 refine (mul_le_mul_of_nonneg_left (Real.add_one_le_exp K) h0).trans' ?_; nlinarith only [he,h0,hK,mul_nonneg hp hK,mul_le_mul_of_nonneg_right he hK]
def XrayPay (μ M v:ℝ):ℝ:= v⁻¹* μ⁻¹ ^ 2 *(256*(2*M)^2)
lemma photo (p:0<v) (h:ε≤r): rueD Ω'/2 ≤ rueD Ξ⁰/2 + Poem Q (Q*R) 𝓤 + horizonM Q (Q*R) μ r + (v*Fintype.card n + XrayPay μ M v *e)/2 :=by
 let M₀:= spring Q (Q*R); let B:= Ξ'; let A:= Ω'; have hp: rueD B /2 ≤ rueD (spring Q (Q*R)) /2 + Poem Q (Q*R) 𝓤 + horizonM Q (Q*R) μ r:=by
    unfold B; rw [Z.wants_lgp]; exact poem_cost Z.pos Z.smallB (⟨Z.q,by rw [←mul_assoc,Z.q.1],Z.live⟩) _ (Z.needs.trans h)
 have ht:= route_log (cosy Z.q Z.pos Z.smallB Ω) (cosy Z.q Z.pos Z.smallB Ξ); have hx:= inv_power (cosy Z.q Z.pos Z.smallB Ξ) Z.pos (cozy_floor Z.q Z.pos Z.smallB Ξ); let L:= B⁻¹*(A-B); have hX : TrR L ≤ v*Fintype.card n+XrayPay μ M v*e:=by
    refine (le_abs_self _).trans ((TrR_c p).trans ((add_le_add le_rfl ?_)))
    have he := (kg_a ..).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) Z.A_cape.hs (kgN _) (by positivity)); exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr p.le)).trans_eq (by unfold XrayPay; simp only [mul_assoc])
 change rueD A ≤ rueD B + TrR L at ht; linarith only [ht,hp,hX]
end Pack
end Drama
end YM.CF.Fock.Reduction
