import YM.SU5.Relativistic.Slicer
/-! # pressure & seam norm for shears -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Lattice Finset Thera
open Papyrus.Granat
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I] {P Q B:Op I} (p:IsStarProjection P)(q:IsStarProjection Q)(b:IsStarProjection B) (k:ℕ)
/-- identity minus *lost*, strict positive -/
def lace (B P:Op I) : Op I := B*(1-P)*B
def jeans (k:ℕ)(B P:Op I): Op I:=1-lace B P+(lace B P)^(k+k+1)
local notation "Z" => lace B P
local notation "X" => Comb B P
local notation "K" => 1-P
include p b
private lemma mount (k:ℕ) : (1-X k)*B=P*B+(1-P)*B*(Z)^k:=by
 let V:= 1-P; let E:=1-P*B*P
 have hp:X k*P=X k:=comb_xp p k
 clear hp -- ih avoid
 induction k with
 | zero => simp [Comb]; noncomm_ring
 | succ k ih=>
   have hp:E*B=B-P*B*P*B:=by unfold E; rw [sub_mul,one_mul]
   have hk:X k*P=X k:= comb_xp p k
   have hh:X k*E*B=X k*B - X k*B*P*B:=by rw [mul_assoc (X k),hp,mul_sub]; simp only [←mul_assoc,hk]
   have hg:B*Z=Z:=by unfold lace; rw [←mul_assoc, ←mul_assoc,b.isIdempotentElem.eq]; -- tune
   have hv:P*B+(1-P)*B=B:=by noncomm_ring
   have hx:P*B*Z=(P*B)*Z:=rfl
   have hy:X k*B*Z=X k*B - X k*B*P*B:=by
     rw [mul_assoc _ B, hg]; unfold lace; rw [←mul_assoc,←mul_assoc,mul_sub (_*B),sub_mul,mul_one,mul_assoc _ B B,b.isIdempotentElem.eq] -- tuner
   have hl:V*B*P*B=V*B-V*B*Z:=by
     rw [mul_assoc V B Z, hg]; unfold lace; rw [←mul_assoc V,←mul_assoc V B, mul_sub _ 1 P,mul_one,sub_mul (V*B),mul_assoc V B B,b.isIdempotentElem.eq]; abel
   rw [Comb]; change (1-(V*B*P+X k*E))*B= _
   rw [sub_mul,add_mul, one_mul,hh,←hy,hl]
   have he: V*B*Z^(k+1)=(V*B-X k*B)*Z:=by
     rw [pow_succ,←mul_assoc]; congr 1
     rw [sub_mul,one_mul] at ih; 
     change _=P*B+V*B*Z^k at ih
     apply add_left_cancel (a:= P*B) -- name?
     rw [←ih,←add_sub_assoc,show P*B+V*B=B from hv]
   change B - (V*B-V*B*Z+ _)=_+V*B*Z^(k+1); rw [he,sub_mul (V*B)]
   nth_rw 1 [←hv]; change P*B+V*B-_=_; abel
lemma fin_jeans : B*(star (1-X k)*(1-X k))*B+(1-B)= jeans k B P:=by
 let C:= 1-X k; let S:=P*B; let Q:=1-P; let L:= Q*B
 have he:star (P*B)=B*P:=by rw [star_mul,b.isSelfAdjoint,p.isSelfAdjoint]
 have ht:star S*S=B*P*B:=by unfold S; rw [he,←mul_assoc, mul_assoc B P P,p.isIdempotentElem.eq]
 have hh:star L*L=Z:=by unfold L; rw [star_mul,b.isSelfAdjoint,show star Q=Q from p.one_sub.isSelfAdjoint, ←mul_assoc,mul_assoc B Q Q,show Q*Q=Q from p.one_sub.isIdempotentElem]; rfl
 have hu:star S*L=0:=by unfold S L; rw [he,←mul_assoc,mul_assoc B P Q,show P*Q=0 from Porth p,mul_zero,zero_mul]
 have hz:star L*S=0:=by rw [←star_zero (R:=Op I),←hu,star_mul (star S) L,star_star]
 have hP:star Z=Z:= by unfold lace; simp only [star_mul,b.isSelfAdjoint.star_eq,p.one_sub.isSelfAdjoint.star_eq,mul_assoc]
 rw [show B*(star (1-X k)*(1-X k))*B=star (C*B)*(C*B) from (by rw [star_mul, b.isSelfAdjoint]; unfold C; noncomm_ring),show C*B=S+L*Z^k from mount p b k,star_add,star_mul L (Z^k),star_pow,hP, mul_add,add_mul,add_mul,ht,mul_assoc (Z^k),hz,mul_zero,←mul_assoc (star S),hu,zero_mul]
 have hl:Z^k*star L*(L*Z^k)=Z^(k+k+1):=by rw [←mul_assoc, mul_assoc (Z^k),hh,show k+k+1=k+1+k by omega,pow_add,pow_succ] -- tune
 rw [hl, jeans]; have h:B*P*B=B-Z:=by unfold lace; rw [mul_sub B 1 P,mul_one,sub_mul,b.isIdempotentElem.eq]; abel
 rw [h]; abel
omit p b
def hatch(k:ℕ):ℝ:=1-(2⁻¹:ℝ)^(k+k+1)
lemma hatch_lo :0 ≤ hatch k:=sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
lemma hatch_up : hatch k < 1:=sub_lt_self 1 (by positivity)
private lemma heelP {x:ℝ}(h:0≤x)(g:x≤1) : 0≤x-x^(k+k+1) ∧ x-x^(k+k+1)≤hatch k:=by
 have he:x^(k+k+1)≤x:= by rw [pow_succ,mul_comm]; exact mul_le_of_le_one_right h (pow_le_one₀ h g)
 refine ⟨sub_nonneg.mpr he,?_⟩; obtain v|v:=le_total x (2⁻¹:ℝ)
 · have ht:(2⁻¹:ℝ)^(k+k+1)≤ 2⁻¹:=by rw [pow_succ,mul_comm]; exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
   apply le_trans (sub_le_self _ (pow_nonneg h _)) (v.trans _); unfold hatch; linarith
 exact sub_le_sub g (pow_le_pow_left₀ (by norm_num) v _)
include p b
lemma lemongA : ‖lace B P‖ ≤ 1:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (b.norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (b.norm_le _)).trans (p.one_sub.norm_le _))))
section
variable [Nonempty I]
lemma hem_p: ‖jeans k B P - 1‖ ≤ hatch k:=by
 have he:0≤ Z:=le_trans (star_mul_self_nonneg ((1-P)*B)) (le_of_eq (by rw [star_mul,b.isSelfAdjoint,p.one_sub.isSelfAdjoint,←mul_assoc,mul_assoc B (1-P) (1-P),p.one_sub.isIdempotentElem.eq]; rfl))
 have hx:lace B P ≤1:=by
    rw [show (1:Op I)=(algebraMap ℝ (Op I) 1) from (map_one _).symm] -- tune occurrence
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (zero_le_one' ℝ) he).mp (lemongA p b)
 obtain ⟨U,d,g⟩:= spectral_exists Z (by unfold IsSelfAdjoint; unfold lace; rw [star_mul,star_mul, p.one_sub.isSelfAdjoint,b.isSelfAdjoint,mul_assoc])
 rw [g,←spectral_zero U,spectral_le] at he; rw [g,←spectral_one U,spectral_le] at hx
 have hp: jeans k B P-1 = -(spectral U (d-d^(k+k+1))):=by unfold jeans; rw [g,spectral_pow,← spectral_sub]; abel
 have ht:= fun i=>heelP k (show 0≤ d i from he i) (hx _ : d i ≤1)
 rw [hp,norm_neg]; let f:=d-d^(k+k+1); have hy:0≤ spectral U f:=by rw [←spectral_zero U,spectral_le]; exact fun i=> (ht i).1
 apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (hatch_lo k) hy).mpr; rw [Algebra.algebraMap_eq_smul_one,←spectral_one U,spectral_smul,spectral_le]; intro i; simpa [f] using (ht i).2
end
omit p b
-- norm proof doesn't need chosen log branch of complex
abbrev stunt (k:ℕ)(B P:Op I):ℝ:= Real.log ‖(jeans k B P).det‖ /2
include p b
lemma purse (f:Wave I)(x:Sea B f): ‖acts (quant (1-X k)) f‖=Real.exp (stunt k B P):=by
 let K':= acts (quant (1-X k)) f; let H:=Saber p (B:=B) k
 have hg:0< ‖K'‖:=norm_pos_iff.mpr fun v=> (norm_pos_iff.mp (show 0<‖f‖ from x.2.symm ▸ zero_lt_one)) (by
    have he:star H.buy=1-X k:=by unfold H Saber; simp

    have hp:acts (quant (star H.sell)) K'=f:=by unfold K'; rw [←he,←act_mul,←quant_mul, ←star_mul,H.pay,star_one, quant_one,act_one]
    rw [←hp,v,map_zero])
 have ht: inner ℂ K' K'=(jeans k B P).det:=by
    let F:=1-X k; rw [←fin_jeans p b]
    have hf := meadow b f x (star F*F)
    rw [←hf]; change inner ℂ (acts (quant F) f) K'=inner ℂ f (acts (quant (star F*F)) f); rw [quant_mul,quant_star,act_mul]; exact (by nth_rw 1 [←star_star (quant F)]; rw [act_inner])
 rw [inner_self_eq_norm_sq_to_K] at ht
 unfold stunt; rw [←ht,norm_pow]; change ‖K'‖=Real.exp (Real.log (‖(‖K'‖:ℂ)‖^2)/2); rw [Complex.norm_real,Real.norm_of_nonneg hg.le, Real.log_pow]; change ‖K'‖=_; rw [Nat.cast_ofNat, show 2 *Real.log ‖K'‖/2= _ from (show _=Real.log ‖K'‖ from by ring), Real.exp_log hg]
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.purse
