import PF.Pigment
/-!
 `Op` bench for LZ.3 polar/log and LZ.4 (trace orientation matters).
 Exact branch log uses bcoef/∫ convention of Branch.SupportLn/Petal.Merc on a small arc; keeps norm bound through same power recipe as next Linked runtime. Some calculus adapted from CF/Petal/Merc.lean and explicit derivative-at-zero composition from BPress/Pf/Rotate.lean.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 80000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.PureForce
namespace Near
open Function Filter Finset NormedSpace Fock Branch MeasureTheory Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker Interval
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I]{A B: Op I}
-- not new log convention:
variable (A)
private abbrev heat (t:ℝ):Op I:= -t • A
private abbrev curve (t:ℝ):Op I:= 1-heat A t
private abbrev driver (t:ℝ):Op I:= Ring.inverse (curve A t)*A
private abbrev arc (t:ℝ):Op I:= ∫ x in (0:ℝ)..t, driver A x
private abbrev safe:= {t:ℝ| ‖heat A t‖<1}
private lemma within (t:ℝ)(_:t∈ safe A){x:ℝ}(hx:x∈uIcc 0 t): ‖x‖*‖A‖≤ ‖heat A t‖:=by
  rw [heat,norm_smul,norm_neg]; gcongr
  simp only [Real.norm_eq_abs]; apply abs_le'.mpr; obtain ⟨he,hu⟩:= hx; change min 0 t ≤ _ at he; change _ ≤ max 0 t at hu
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h]; rw [max_eq_right h] at hu; rw [min_eq_left h] at he; constructor<;>linarith
  rw [abs_of_nonpos h]; rw [max_eq_left h] at hu; rw [min_eq_right h] at he; constructor <;> linarith
private lemma contains (t:ℝ)(ht:t∈ safe A){x:ℝ}(hx:x∈ uIcc 0 t) : ‖heat A x‖<1:=by simpa only [heat,norm_smul,norm_neg] using (within A t ht hx).trans_lt (show ‖heat A t‖<1 from ht)

private lemma develops (t:ℝ)(ht:t∈ safe A):
    arc A t = ∑' n:ℕ, (∫ x in (0:ℝ)..t,(-x)^n) • A^(n+1):=by
  let F:ℕ→ C(ℝ,Op I):=fun n=>⟨fun x=> (-x)^n • A^(n+1),by fun_prop⟩
  have he (x:ℝ)(hx:x∈uIcc 0 t): driver A x=∑' n,F n x:=by
    unfold driver curve
    have hv:=contains A _ ht hx; rw [NormedRing.inverse_one_sub _ hv]; change (∑' n:ℕ, heat A x^n)*A =_; rw [← (summable_geometric_of_norm_lt_one hv).tsum_mul_right A]
    apply tsum_congr; intro n
    change ((-x) • A)^n*A=(-x)^n • A^(n+1); rw [smul_pow, Algebra.smul_mul_assoc, ←pow_succ]
  unfold arc; rw [intervalIntegral.integral_congr he,←intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm]
  · apply tsum_congr; intro n; exact intervalIntegral.integral_smul_const _ _
  apply ((summable_geometric_of_lt_one (norm_nonneg (heat A t)) (show ‖heat A t‖<1 from ht)).mul_right ‖A‖).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro n; refine (ContinuousMap.norm_le _ (by positivity)).mpr (fun y=>?_)
  change ‖(-y.val)^n • A^(n+1)‖ ≤ _
  rw [norm_smul,norm_pow,norm_neg]
  calc
    _ ≤ (‖y.val‖*‖A‖)^n*‖A‖:= (mul_le_mul_of_nonneg_left (norm_pow_le A _) (by positivity)).trans_eq (by rw [mul_pow,pow_succ,mul_assoc])
    _ ≤ _ := by gcongr; exact within A t ht y.property

private lemma arcD (t:ℝ)(ht:t∈ safe A): HasDerivAt (arc A) (driver A t) t:=by
  have he : IsOpen (safe A):= isOpen_lt (by unfold heat; fun_prop) continuous_const
  have hx (y:ℝ)(p:y∈safe A):ContinuousAt (driver A) y:= by
    have ht:ContinuousAt Ring.inverse (curve A y):= NormedRing.inverse_continuousAt (Units.oneSub (heat A y) p)
    suffices hb: Continuous (curve A) by exact (ht.comp hb.continuousAt).mul_const A
    unfold curve heat; fun_prop
  apply intervalIntegral.integral_hasDerivAt_right _ (ContinuousAt.stronglyMeasurableAtFilter he hx t ht) (hx _ ht); exact ContinuousOn.intervalIntegrable (fun y v=> (hx _ (contains _ _ ht v)).continuousWithinAt)
private lemma relate {s t:ℝ}(h:s∈safe A)(v:t∈safe A): Commute (arc A t) (arc A s):=by
 rw [develops A s h, develops A t v]; refine Commute.tsum_left _ (fun i=> Commute.tsum_right _ fun j=>?_); exact (((Commute.refl A).pow_pow _ _).smul_left _).smul_right _
private lemma motive (t:ℝ)(ht:t∈safe A): HasDerivAt (fun x=> exp (-arc A x)) (-driver A t * exp (-arc A t)) t:=by
 letI : NormedAlgebra ℚ (Op I) := NormedAlgebra.restrictScalars ℚ ℂ (Op I)
 let V:=-arc A t
 let F(x:ℝ):Op I:= -arc A x-V
 have hp: IsOpen (safe A):= isOpen_lt (by unfold heat; fun_prop) continuous_const
 have he: (fun x=>exp (-arc A x))=ᶠ[𝓝 t] fun x=>exp (F x) * exp V := by
   filter_upwards [hp.mem_nhds ht] with x hx
   have hw: Commute (F x) V:= (((relate A ht hx).neg_left.neg_right).sub_left (Commute.refl _))
   rw [←exp_add_of_commute hw,sub_add_cancel]
 rw [he.hasDerivAt_iff]; apply HasDerivAt.mul_const
 have hd:HasFDerivAt exp (1:Op I→L[ℝ] Op I) (F t):=by change HasFDerivAt exp _ (V-V); rw [sub_self]; exact hasFDerivAt_exp_zero
 exact hd.comp_hasDerivAt _ ((arcD A t ht).neg.sub_const V)

lemma pencil_exp (h:‖A‖<1): exp (pencil A)=1+A:=by
 let Y:=uIcc 0 (1:ℝ); let D t:=curve A t*exp (-arc A t)
 have hu: (1:ℝ)∈ safe A:=by unfold safe; simp [heat,h]
 have hp t (p:t∈Y): HasDerivAt D 0 t:=by
    have hv:t∈safe A:=contains A _ hu p
    have hc:HasDerivAt (curve A) A t:=by unfold curve heat; simpa using (((hasDerivAt_id' t).neg.smul_const A).const_sub 1)
    have hb:= hc.mul (motive A t hv)
    refine hb.congr_deriv ?_; change A*exp _ + curve A t*(-driver A t*exp _)=(0:Op I)
    have ht:curve A t*driver A t=A := by unfold driver; rw [←mul_assoc,Ring.mul_inverse_cancel _ (show IsUnit (curve A t) from Units.isUnit (Units.oneSub _ hv)),one_mul]
    rw [←mul_assoc (curve A t),mul_neg,ht, neg_mul,add_neg_cancel]
 have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hp (by simp)
 simp only [D,curve,heat,one_smul,neg_smul, neg_zero,zero_smul,add_zero,sub_neg_eq_add, intervalIntegral.integral_zero, show arc A 0=0 from intervalIntegral.integral_same,exp_zero,mul_one] at he
 haveI : NormedAlgebra ℚ (Op I) := NormedAlgebra.restrictScalars ℚ ℂ (Op I)
 have hx : (1+A)*exp (-pencil A)=1:=by rw [←show arc A 1=pencil A from develops A 1 hu]; exact sub_eq_zero.mp he.symm
 rw [←one_mul (exp (pencil A)),←hx,mul_assoc,←exp_add_of_commute ((Commute.refl _).neg_left),neg_add_cancel,exp_zero,mul_one,hx]
variable {A}
lemma pencil_norm {r:ℝ}(h:‖A‖≤ r)(p:r<1):‖pencil A‖ ≤ r*(1-r)⁻¹:=by
 have hv:= summable_geometric_of_lt_one ((norm_nonneg _).trans h) p
 let f(n:ℕ):=bcoef n • A^(n+1)
 have he(n:ℕ):‖f n‖ ≤ r*r^n:=by unfold f; rw [norm_smul]; apply (mul_le_of_le_one_left (norm_nonneg _) (bc_norm _)).trans; exact (norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) h _).trans_eq (pow_succ' ..))
 exact (norm_tsum_le_tsum_norm ((hv.mul_left r).of_nonneg_of_le (fun i=> norm_nonneg (f i)) he)).trans ((((hv.mul_left r).of_nonneg_of_le (fun i=> norm_nonneg (f i)) he).tsum_le_tsum he (hv.mul_left r)).trans_eq (by rw [tsum_mul_left,tsum_geometric_of_lt_one ((norm_nonneg _).trans h) p]))

local notation "H"=> (1/8:ℝ)
private lemma pow_change (h:‖A‖≤H) (g:‖B‖≤H)(i:ℕ) : ‖A^(i+1)-B^(i+1)‖ ≤ (i+1:ℝ)*H^i*‖A-B‖:=by
 induction i with
 | zero=> simp
 | succ i t=>
   rw [pow_succ A (i+1),pow_succ B (i+1),show A^(i+1)*A-B^(i+1)*B=(A^(i+1)-B^(i+1))*A+B^(i+1)*(A-B) by noncomm_ring]
   refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul t h (norm_nonneg _) (by positivity))) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) g _)) (norm_nonneg _)))).trans_eq ?_)
   rw [pow_succ]; push_cast; ring
private abbrev cash (X:Op I)(n:ℕ):= (Nat.factorial n:ℝ)⁻¹ • X^n
private lemma cheap (i:ℕ):0 ≤ (Nat.factorial i:ℝ)⁻¹ ∧ (Nat.factorial i:ℝ)⁻¹ ≤1:=by
 have hp:0<(Nat.factorial i:ℝ):=by positivity
 exact ⟨by positivity,(inv_le_one₀ hp).mpr (by exact_mod_cast Nat.factorial_pos i)⟩
lemma exp_small (h:‖A‖≤ H)(g:‖B‖≤H)(p: exp A= exp B): A=B:=by
 have hs (A:Op I): Summable (cash A) := by simpa only [expSeries_apply_eq] using (expSeries_summable (𝕂:=ℝ) A)
 have hx i: ‖cash A (i+(1+1))-cash B (i+(1+1))‖ ≤ (1/4:ℝ)^(i+1)* ‖A-B‖:=by
   unfold cash; rw [←smul_sub,norm_smul,Real.norm_of_nonneg (cheap _).1,show i+(1+1)=i+1+1 from rfl]
   have hh(i:ℕ):(i+1:ℝ)≤2^i:=by
     induction i with
     | zero=> simp
     | succ i v => rw [pow_succ]; push_cast; have hp:1 ≤ (2:ℝ)^i:= one_le_pow₀ (by norm_num); linarith
   calc
     _ ≤ ((↑(i+1):ℝ)+1)*H^(i+1)*‖A-B‖ := (mul_le_of_le_one_left (norm_nonneg _) (cheap _).2).trans (pow_change h g _)
     _ ≤ 2^(i+1)*H^(i+1)*‖A-B‖:= by gcongr ?_ * _ * _; exact hh _
     _ = _ :=by rw [←mul_pow]; norm_num
 let v:= fun i:ℕ=> (cash A i -cash B i); have ht:Summable v := (hs A).sub (hs B); have hd : ∑' i,v i=0:= ((hs A).tsum_sub (hs B)).trans (sub_eq_zero.mpr (by unfold cash; rw [← show exp A= ∑' n,cash A n from congrFun (exp_eq_tsum ℝ) A,←show exp B=_ from congrFun (exp_eq_tsum ℝ) B,p])) -- unfold cash rw
 rw [←ht.sum_add_tsum_nat_add 2] at hd
 have hp : Summable fun i:ℕ=> (1/4:ℝ)^(i+1)* ‖A-B‖:= ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_right _
 have hi : ‖(∑' i:ℕ, v (i+2))‖ ≤ (1/3:ℝ)*‖A-B‖:=by
    refine (norm_tsum_le_tsum_norm (hp.of_nonneg_of_le (fun i=>norm_nonneg _) hx)).trans (((hp.of_nonneg_of_le (fun i:ℕ=>norm_nonneg _) hx).tsum_le_tsum hx hp).trans_eq ?_)
    simp_rw [pow_succ,tsum_mul_right,tsum_geometric_of_lt_one (show (0:ℝ)≤1/4 by norm_num) (by norm_num)]; ring
 rw [sum_range_succ, sum_range_one] at hd; simp only [v,cash, Nat.factorial, pow_one,pow_zero,Nat.cast_one, mul_one,inv_one,one_smul,sub_self,zero_add] at hd; have he : A-B = -(∑' i:ℕ,v (i+2)):=by exact eq_neg_of_add_eq_zero_left hd
 rw [← norm_neg (∑' i:ℕ, v (i+2)), ←he] at hi
 exact sub_eq_zero.mp (norm_le_zero_iff.mp (by linarith)) -- v now unfolded hd
-- near unitary log exact th. minuscule constant irrelevant.
local notation "E8"=> (1/32:ℝ)
lemma skim (p:‖A-1‖≤ E8)(h:A∈ unitary (Op I)): let Y:= pencil (A-1);
    ‖Y‖ ≤ H ∧ exp Y=A ∧ star Y= -Y:=by
 intro Y; letI: NormedAlgebra ℚ (Op I):= NormedAlgebra.restrictScalars ℚ ℂ _
 have hm: ‖Y‖≤ H:=(pencil_norm p (by norm_num)).trans (by norm_num)
 have he: exp Y=A:=by change exp (pencil (A-1))=_; rw [pencil_exp _ (p.trans_lt (by norm_num))]; abel
 refine ⟨hm,he,exp_small (by simpa only [norm_star]) (by simpa only [norm_neg]) ?_⟩
 rw [←star_exp Y,he]
 have hv: exp Y * exp (-Y)=1:=by rw [←exp_add_of_commute ((Commute.refl Y).neg_right),add_neg_cancel,exp_zero]
 obtain ⟨h₁,h₂⟩:= h; rw [he] at hv
 calc
   star A = (star A * A) * exp (-Y):=by rw [mul_assoc,hv,mul_one]
   _ = exp (-Y):=by rw [h₁,one_mul]
variable (A B)
def reflector := (2:ℝ) • A-1
lemma invol (p:IsStarProjection A) : let J:= reflector A;
    star J=J ∧ J*J=1 ∧ ‖J‖=1:=by
 intro J
 have hv:star J=J:=by unfold J reflector; rw [star_sub,star_smul,star_one,p.isSelfAdjoint,star_trivial]
 have hp:A*A=A:=p.isIdempotentElem.eq
 have hJ:J*J=1:=by
   unfold J reflector; rw [show (2:ℝ) • A=A+A from two_smul ..]; noncomm_ring [hp]
 have hu:J∈unitary (Op I):= ⟨hv.symm ▸ hJ,by rw [hv,hJ]⟩ -- subst trick may replace Js RHS
 exact ⟨hv,hJ,CStarRing.norm_of_mem_unitary hu⟩
-- J B ... near arc := J' * J delta exponential. L defines exact trace-free polar-log equivalent

def bud := reflector B * reflector A

def braid: Op I:= (1/2:ℝ) • pencil (bud A B-1)

def sling: Op I:= exp (braid A B)

lemma bud_price (h:IsStarProjection A)(B:Op I): ‖bud A B-1‖ ≤ 2*‖B-A‖:=by
 obtain ⟨_,p,e⟩:= invol A h
 have ht:=norm_mul_le (reflector B-reflector A) (reflector A)
 rw [e,mul_one,sub_mul,p] at ht
 refine ht.trans_eq ?_; rw [reflector, reflector, sub_sub_sub_cancel_right, ←smul_sub,norm_smul, Real.norm_of_nonneg (by norm_num)]
lemma ribbon (h:IsStarProjection A)(t:IsStarProjection B)(p: ‖B-A‖ ≤ 1/64):
    let L:=braid A B; let U:=sling A B; let J:= reflector A;
    star L = -L ∧ J*L*J= -L ∧ Matrix.trace L=0 ∧ U∈unitary (Op I) ∧ U*U= bud A B ∧ U*A=B*U ∧ ‖L‖ ≤ 1/16:=by
 intro L U J; obtain ⟨e₁,e₂,e₃⟩:= invol A h; obtain ⟨p₁,p₂,_⟩:=invol B t; let J':=reflector B
 let a: UNI I:=⟨J, ⟨by rw [show star J=J from e₁]; exact e₂,by rw [show star J=J from e₁]; exact e₂⟩⟩
 haveI : NormedAlgebra ℚ (Op I):= NormedAlgebra.restrictScalars ℚ ℂ _
 obtain ⟨hr,hv,hg⟩:=skim (show ‖bud A B-1‖≤ E8 from (bud_price A h B).trans (by linarith only [p]))
   (show bud A B∈unitary (Op I) from by
     unfold bud; rw [Unitary.mem_iff,star_mul,e₁,p₁]; constructor
     · rw [mul_assoc,←mul_assoc (reflector B),p₂,one_mul,e₂]
     rw [mul_assoc,←mul_assoc (reflector A),e₂,one_mul,p₂])
 let Y:=pencil (bud A B-1)
 have ht: ‖L‖ ≤ 1/16:=by change ‖(1/2:ℝ) • Y‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (by norm_num)]; linarith only [hr]
 have hy: star L= -L:=by change star ((1/2:ℝ) • Y)= _; rw [star_smul,star_trivial,show star Y= -Y from hg,smul_neg]; rfl
 have hm:L+L=Y:=by unfold L Y braid; module
 have hx: twist a Y= -Y:=by
    refine (exp_small (B:=star Y) (calc
      ‖twist a Y‖ ≤ ‖Y‖ := le_of_eq ?no
      _ ≤ H :=hr) (by rw [norm_star]; exact hr) ?_).trans hg
    · rw [twist_formula]; change ‖a.val*Y*star a.val‖=_; rw [← show (↑(star a):Op I)=star a.val from rfl,CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
    rw [←breeze_exp,show exp Y=_ from hv,twist_formula,show a.val=J from rfl,←star_exp,show exp Y=_ from hv,bud,star_mul,e₁,p₁]; change J*(J'*J)*J=J*J'; rw [mul_assoc,mul_assoc J',show J*J=1 from e₂,mul_one]; -- tune
 have hq: J*L*J= -L:=by change J * ((1/2:ℝ) • Y)*J= _; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rw [twist_formula] at hx; rw [show J*Y*J= -Y by change ↑a*Y*J= -Y; simpa only [show star a.val=J from e₁] using hx, smul_neg]; rfl
 have hT: Matrix.trace L=0:=by
    have hp:=congrArg Matrix.trace hq; rw [Matrix.trace_mul_cycle, show J*J=1 from e₂,one_mul,Matrix.trace_neg] at hp
    have ht: 2 * L.trace=0:=by linear_combination hp
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num: (2:ℂ) ≠0)
 have hl: U∈unitary (Op I) :=exp_mem_unitary_of_mem_skewAdjoint hy
 have hb:U*U=bud A B:=by change exp L*exp L=_; rw [←exp_add_of_commute (Commute.refl L),hm,hv]
 have hz: J*U*J=star U:=by change ↑a*exp L*J=star (exp L); rw [←show star a.val=J from e₁,←twist_formula, breeze_exp,twist_formula,star_exp,hy]; congr 1; change J*L*star J= _; rw [show star J=J from e₁,hq]
 have hR:=hl; obtain ⟨l,r⟩ := hR
 have hg : J'*U=U*J:=by
   have hd:J*U=star U*J:=by rw [←hz,mul_assoc,show J*J=1 from e₂,mul_one]
   have hf: J'=U*U*J:=by rw [hb]; unfold bud; rw [mul_assoc,show reflector A*J=1 from e₂,mul_one]
   rw [hf,mul_assoc (U*U),hd,←mul_assoc,mul_assoc U,r,mul_one]
 refine ⟨hy,hq,hT,hl,hb,?_,ht⟩
 have hs:=hg; unfold J' J reflector at hs; rw [sub_mul,mul_sub,one_mul,mul_one,Algebra.mul_smul_comm,Algebra.smul_mul_assoc] at hs
 exact smul_right_injective _ (show (2:ℝ)≠ 0 by norm_num) (sub_left_inj.mp hs.symm)
-- U is actually the unitary polar part of V_# (§LZ.3 normal log branch). Pricing may use this pencil recipe directly without loading sqrt and then log. Need certify uniquely near identity and transformations cross orientation.
-- enough to report V_#=U * H with H strictly positive; $V(V*V)^-1/2$ then follows when needed.
-- prove ‖U-1‖ ≤ from geometric
lemma expBall (h:‖A‖≤ 1/16): ‖exp A-1‖≤ 1/8:=by
  have hs:Summable (cash A):=by simpa only [expSeries_apply_eq] using (expSeries_summable (𝕂:=ℝ) A)
  rw [exp_eq_tsum ℝ]; change ‖(∑' i,cash A i)-1‖ ≤ _; rw [←hs.sum_add_tsum_nat_add 1,sum_range_one, show cash A 0=1 from by simp [cash],add_sub_cancel_left]
  have ht(i:ℕ):‖cash A (i+1)‖≤(1/16)*(1/16:ℝ)^i:=by unfold cash; rw [norm_smul,Real.norm_of_nonneg (cheap _).1]; exact (mul_le_of_le_one_left (norm_nonneg _) (cheap _).2).trans ((norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) h _).trans_eq (pow_succ' ..)))
  have he:= (summable_geometric_of_lt_one (show 0≤(1/16:ℝ) by norm_num) (by norm_num)).mul_left (1/16:ℝ); have hb:= he.of_nonneg_of_le (fun i=> norm_nonneg (cash A (i+1))) ht
  refine (norm_tsum_le_tsum_norm hb).trans ((hb.tsum_le_tsum ht he).trans ?_)
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
lemma strait (h:IsStarProjection A)(t:IsStarProjection B)(p: ‖B-A‖ ≤ 1/64):
    let U:=sling A B; let X:=(1/2:ℝ) • (U+star U);
    (B*A+(1-B)*(1-A))=U*X ∧ (1/2:ℝ) • (1:Op I)≤ X:=by
 intro U X; obtain ⟨_,_,_,hh,hx,_,hr⟩:= ribbon A B h t p; have ht:‖U-1‖≤1/8:=expBall _ hr
 have hy:IsSelfAdjoint X:=by unfold IsSelfAdjoint X; rw [star_smul,star_trivial, star_add,star_star,add_comm]
 have hz:X-1=(1/2:ℝ) • ((U-1)+star (U-1)):=by rw [star_sub,star_one]; unfold X; module
 have he: ‖1-X‖≤1/2:=by
    rw [norm_sub_rev,hz,norm_smul,Real.norm_of_nonneg (by norm_num)]; have hv:=norm_add_le (U-1) (star (U-1)); rw [norm_star] at hv; linarith
 constructor
 · rw [show U*X=(1/2:ℝ) • (U*U+U*star U) by unfold X; rw [Algebra.mul_smul_comm, mul_add],hh.2,hx]
   unfold bud reflector; simp only [two_smul, sub_mul,mul_sub, add_mul,mul_add,one_mul,mul_one]; module
 · have hp : 1-X ≤ ‖1-X‖ • 1:= op_le_norm_one (show star (1-X)=1-X by rw [star_sub,star_one,show star X=X from hy])
   have hv: 1-X≤ (1/2:ℝ) • 1:=hp.trans (smul_le_smul_of_nonneg_right he zero_le_one)
   suffices z:1 - (1/2:ℝ) • (1:Op I) ≤ X by
     rwa [show (1:Op I)-(1/2:ℝ) • 1=(1/2:ℝ) • 1 by module] at z
   apply sub_le_iff_le_add.mpr; rw [add_comm]; exact sub_le_iff_le_add.mp hv
-- covariance under two input transport incl complement. use series equality or logs small inj.
variable (g:UNI I)
lemma turns (h:IsStarProjection A)(t:IsStarProjection B)(p:‖B-A‖≤1/64):
    let C:=twist g A; let D:=twist g B; let Z:=braid A B; let U:=sling A B;
    twist g Z=braid C D ∧ twist g U=sling C D ∧ twist g Z=braid (1-C) (1-D) ∧ twist g U=sling (1-C) (1-D):=by
 intro C D Z U; have hd : bud C D-1= twist g (bud A B-1):=by unfold C D bud reflector; rw [map_sub,map_mul,map_sub,map_sub,map_one,map_smul,map_smul]
 have he : ‖bud A B-1‖<1:= (bud_price A h B).trans_lt (by linarith only [p])
 let L : Op I →L[ℝ] Op I:= (twist g).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 have hx : twist g Z=braid C D :=by
   unfold Z braid; rw [hd,map_smul]; congr 1; unfold pencil; change L (∑' i, _)= _; let W:=bud A B-1
   have hu : Summable (fun i:ℕ=> bcoef i • W^(i+1)):= (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) he))).of_norm_bounded (fun i=> by rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (bc_norm _)).trans (norm_pow_le ..)) -- technology
   rw [L.map_tsum hu]; apply tsum_congr; intro i; change twist g _=_; rw [map_smul,map_pow]
 have hz := show twist g U= _ from breeze_exp g Z
 rw [hx] at hz
 have hr (X:Op I): reflector (1-X)= -reflector X:=by unfold reflector; module
 have hp: braid (1-C) (1-D)=braid C D:=by simp only [braid,bud,hr,neg_mul_neg]
 exact ⟨hx,hz,hx.trans hp.symm,hz.trans (congrArg exp hp.symm)⟩
end Near
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.PureForce
