import YM.CF.Fixed.EnergyBalance

/-! Mixed terms of the positive spectral sum, sparse variables.
Dimension-free tail. This uses binomial series near an involutive link block.
Covariance/support of such powers under physical gauges stated elsewhere. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Fixed.Bulk
open Function NormedSpace Lattice Fock Filter Metric Matrix Finset SignScalar
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {z x r a b : ℝ}
lemma bin_sqr (p:‖z‖<1): bin z^2=(1-z)⁻¹:=by
  have hs:= bin_summable z p; rw [sq,bin,tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs]; refine Eq.trans (tsum_congr (g:=fun n:ℕ=> z^n) fun b=>?_) (tsum_geometric_of_norm_lt_one p); conv_rhs => rw [←one_mul (z^b), ←c_conv b,Finset.sum_mul]
  apply sum_congr rfl; intro i hi; rw [← show i.1+i.2= _ from HasAntidiagonal.mem_antidiagonal.mp hi,pow_add]; ring
lemma bin_W (p:‖z‖≤1/4):0< bin z:=by
  let r:ℝ:=1/4; have he:‖z‖<1:=p.trans_lt (by norm_num); let f(n:ℕ):= SignScalar.c n*z^n; let w:=∑' n:ℕ,f (n+1); have hw:w=bin z-1:=by have ht:= (bin_summable z he).of_norm.sum_add_tsum_nat_add 1; unfold bin; simpa [w,f,sum_range_one,c,sub_eq_iff_eq_add',eq_sub_iff_add_eq'] using ht -- tune
  have hv : ‖w‖≤1/2:=by
    let g(n:ℕ):= r*r^n; have hu:0≤r:=by unfold r; norm_num
    have hz:r<1:=by unfold r; norm_num
    have hG : Summable g:= (summable_geometric_of_lt_one hu hz).mul_left r; have hp(n:ℕ): ‖f (n+1)‖≤ g n:= by rw [show g n=r^(n+1) from (pow_succ' r n).symm]; unfold f; rw [norm_mul,norm_pow]; exact le_trans (mul_le_of_le_one_left (by positivity) (c_norm _)) (pow_le_pow_left₀ (norm_nonneg _) p _)
    have hh: Summable fun i:ℕ=> ‖f (i+1)‖:= hG.of_nonneg_of_le (fun _=> norm_nonneg _) hp; apply (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum hp hG).trans ?_); unfold g; rw [tsum_mul_left,tsum_geometric_of_lt_one hu hz]; unfold r; norm_num
  rw [Real.norm_eq_abs,hw] at hv; linarith [abs_le.mp hv]

def coefficient : ℕ→ℝ
  | 0=>1 | n+1=> c (n+1)-c n
lemma fee_series(k:ℕ) : |coefficient k|≤1:=by cases k with|zero=>norm_num [coefficient]|succ n=> unfold coefficient; exact abs_le.mpr ⟨by linarith [c_nn (n+1),c_le n],by linarith [c_le (n+1),c_nn n]⟩
lemma sumZ (p:‖z‖≤1/4): HasSum (fun k:ℕ=> coefficient k * z^k) (Real.sqrt (1-z)):=by
  let f(k:ℕ):= c k*z^k
  have he:HasSum f (bin z):= ((bin_summable z (p.trans_lt (by norm_num))).of_norm).hasSum; let g:ℕ→ℝ | 0=>0 | n+1=> f n*z
  have hx:HasSum g (bin z*z):= by apply (hasSum_nat_add_iff' 1).mp; simp only [sum_range_one,show g 0=0 from rfl,sub_zero]; exact he.mul_right z
  have hs := sub_pos.mpr (show z<1 from le_trans (le_abs_self z) p|>.trans_lt (by norm_num: (1:ℝ)/4<1)); rw [show (fun k:ℕ=>coefficient k*z^k)=_ from ?_, show Real.sqrt (1-z)=bin z-bin z*z from ?_]; exact he.sub hx; swap
  · funext i; cases i with| zero=>simp [f,g,c,coefficient]|succ i=>simp only [coefficient,f,g]; rw [sub_mul]; rw [pow_succ z]; ring
  rw [show bin z-bin z*z=bin z*(1-z) from by ring]; apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_pos (bin_W p) hs).le).1; rw [Real.sq_sqrt hs.le,mul_pow,bin_sqr (p.trans_lt (by norm_num)),sq,← mul_assoc,inv_mul_cancel₀ hs.ne',one_mul]
-- matrix
section cross
variable {n:Type*}[Fintype n][DecidableEq n][Nonempty n]
variable (A B : Op n) {X Y:Op n}
omit [Nonempty n] in
lemma spectral_small (U:UNI n)(d:n→ℝ)(h: ‖spectral U d‖≤r)(i:n): ‖d i‖ ≤ r:=by
  unfold spectral at h; rw [twist_norm] at h; have hx:= norm_entry (diagonal (fun j=>(d j:ℂ))) i i; simpa using hx.trans h
omit [Nonempty n] in
lemma sqrt_formula (h:IsSelfAdjoint A)(p:‖A‖≤1/4): HasSum (fun i:ℕ=> coefficient i • A^i) (CFC.sqrt (1-A)):=by
  obtain ⟨U,d,rfl⟩:= spectral_exists _ h
  rw [←spectral_one U,spectral_sub,sqrt_spec U (1-d) (fun i=>sub_nonneg.mpr ((le_trans (le_abs_self (d i)) (spectral_small U d p i)).trans (show (1:ℝ)/4≤1 by norm_num)))] -- tune defeq
  let L:(n→ℝ)→ₗ[ℝ] Op n:={toFun:=spectral U,map_add':=fun x y=>(spectral_add ..).symm,map_smul':= fun x y=>(spectral_smul ..).symm}
  have ht: HasSum (fun i:ℕ=> coefficient i • d^i) (fun x=> Real.sqrt (1-d x)):= Pi.hasSum.mpr fun i=>sumZ (spectral_small U d p i)
  simp_rw [spectral_pow,spectral_smul]; exact ht.map L L.continuous_of_finiteDimensional
/-- Price assumptions in integral duality. -/
def Influence : ℝ→ Op n→Prop:= fun K A=>∀ B:Op n, |trR (A*B)|≤ K*‖B‖
lemma infl_tr (h:Influence x A): |trR A|≤x:=by simpa using h 1
omit [Nonempty n] in
lemma increase (h:Influence x A)(p:x≤z): Influence z A:= fun B=> (h B).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _))
omit [Nonempty n] in
lemma inf_add (h:Influence a A)(v:Influence b B) : Influence (a+b) (A+B):= by unfold Influence; intro V; rw [add_mul,plus_t,add_mul]; exact le_trans (abs_add_le ..) (add_le_add (h V) (v V))
omit [Nonempty n] in
lemma inf_right (p:0≤r)(H:Influence r A)(h:‖B‖≤z): Influence (r*z) (A*B):= by unfold Influence; intro V; rw [mul_assoc,mul_assoc]; exact le_trans (H (B*V)) (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) p)
omit [Nonempty n] in
lemma inf_left (p:0≤r)(H:Influence r A)(h:‖B‖≤z): Influence (r*z) (B*A):= by
  unfold Influence; intro V; rw [mul_assoc (b:=A),comm_t,mul_assoc]; specialize H (V*B)
  apply H.trans; rw [mul_assoc r]; exact mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _)|>.trans_eq (mul_comm ..))) p
lemma inf_power (h:‖A‖≤r)(u:‖A+X‖≤ r)(hp:Influence a X)(he:0≤a)(n:ℕ) : Influence ((n+1:ℝ)*r^n*a) ((A+X)^(n+1)-A^(n+1)):=by
  have hz:0≤r:=(norm_nonneg _).trans h
  induction n with
  | zero=> simpa using hp
  | succ n ih=> rw [show (A+X)^(n+1+1)-A^(n+1+1) = ((A+X)^(n+1) - A^(n+1))*(A+X) + A^(n+1)*X from by rw [pow_succ (A+X) (n+1),pow_succ A (n+1)]; noncomm_ring]; apply increase _ (inf_add _ _ (inf_right _ _ (by positivity) ih u) (inf_left X _ he hp ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) h (n+1))))); rw [Nat.cast_add_one,pow_succ]; apply le_of_eq; ring
lemma norm_power (h:‖A‖≤r)(u:‖A+X‖≤ r)(q:‖X‖≤a)(n:ℕ) : ‖(A+X)^(n+1)-A^(n+1)‖ ≤ (n+1:ℝ)*r^n*a:=by
  have hz:0≤r:=(norm_nonneg _).trans h; have he:0≤a:=(norm_nonneg _).trans q
  induction n with
  | zero=> simpa using q
  | succ n ih=> rw [show (A+X)^(n+1+1)-A^(n+1+1) = ((A+X)^(n+1) - A^(n+1))*(A+X) + A^(n+1)*X from by rw [pow_succ (A+X) (n+1),pow_succ A (n+1)]; noncomm_ring]; refine le_trans ((norm_add_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))) ((add_le_add (mul_le_mul ih u (norm_nonneg _) (by positivity)) (mul_le_mul ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) h (n+1))) q (norm_nonneg _) (by positivity))).trans_eq ?_); rw [Nat.cast_add_one,pow_succ]; ring

def mixed (A X Y:Op n)(i:ℕ) := (A+X+Y)^i+A^i-(A+X)^i-(A+Y)^i
omit [Nonempty n] in
lemma mix_2 (A X Y:Op n): mixed A X Y 2=X*Y+Y*X:= by unfold mixed; noncomm_ring
lemma mix_bound (h:‖A‖≤r)(p:‖A+X‖≤r)(q:‖A+Y‖≤r)(w:‖A+X+Y‖≤r)(u:Influence x X)(t:‖Y‖≤z)(k:0≤x) (n:ℕ) : Influence ((n+1:ℝ)*(n+2:ℝ)*r^n*x*z) (mixed A X Y (n+2)):=by
  have he:0≤r:=(norm_nonneg _).trans h; have hx:0≤z:=(norm_nonneg _).trans t
  induction n with
  | zero=> rw [show 0+2= (2:ℕ) from rfl,mix_2]; refine increase _ (inf_add _ _ (inf_right X Y k u t) (inf_left X Y k u t)) (le_of_eq ?_); push_cast; ring
  | succ n ih=> rw [show mixed A X Y (n+1+2) = mixed A X Y (n+2) * (A+X+Y) + ((A+X)^(n+2)-A^(n+2))*Y + ((A+Y)^(n+2)-A^(n+2))*X from ?_]
                · refine increase _ (inf_add _ _ (inf_add _ _ (inf_right _ _ (by positivity) ih w) (inf_right _ _ (by positivity) (inf_power A h p u k (n+1)) t)) (inf_left _ _ k u (norm_power A h q t (n+1)))) (le_of_eq ?_); push_cast; simp_rw [pow_succ]; ring
                unfold mixed; rw [show n+1+2=n+2+1 from rfl]; simp only [pow_succ _ (n+2)]; noncomm_ring
abbrev mixedTrace (A X Y:Op n)(k:ℕ):= coefficient k * trR (mixed A X Y k)
abbrev rootMixed (A X Y:Op n):=trR (CFC.sqrt (1-(A+X+Y)))+trR (CFC.sqrt (1-A))-trR (CFC.sqrt (1-(A+X))) -trR (CFC.sqrt (1-(A+Y)))
omit [Nonempty n] in
lemma charge_sum (v:r≤1/4)(h:‖A‖≤r)(p:‖A+X‖≤r)(q:‖A+Y‖≤r)(w:‖A+X+Y‖≤r)(j:IsSelfAdjoint A)(i:IsSelfAdjoint X)(a:IsSelfAdjoint Y): HasSum (mixedTrace A X Y) (rootMixed A X Y):=by
  let f: Op n→ₗ[ℝ]ℝ:={toFun:=trR,map_add':=plus_t,map_smul':= scale_t}
  have hp:=((((sqrt_formula (A+X+Y) ((j.add i).add a) (w.trans v)).add (sqrt_formula A j (h.trans v))).sub (sqrt_formula (A+X) (j.add i) (p.trans v))).sub (sqrt_formula _ (j.add a) (q.trans v))).map f f.continuous_of_finiteDimensional
  simp only [map_add, map_sub] at hp
  refine hp.congr_fun ?_; intro k; unfold mixedTrace mixed; rw [diff_t,diff_t,plus_t]; simp only [Function.comp_apply,map_sub,map_add,map_smul,mul_sub,mul_add]; rfl
lemma mix_cost (v:r≤1/4)(h:‖A‖≤r)(p:‖A+X‖≤r)(q:‖A+Y‖≤r)(w:‖A+X+Y‖≤r)(u:Influence x X)(t:‖Y‖≤z)(k:0≤x)(J:IsSelfAdjoint A)(i:IsSelfAdjoint X)(a:IsSelfAdjoint Y) : |rootMixed A X Y+(1/4:ℝ)*trR (X*Y)| ≤ 12*r*x*z := by
  have hz(n:ℕ) : |mixedTrace A X Y (n+2)| ≤ (n+1:ℝ)*(n+2:ℝ)*r^n*x*z:=by rw [mixedTrace,abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (fee_series _)).trans (infl_tr _ (mix_bound A h p q w u t k n))
  have he:0≤r:=(norm_nonneg _).trans h; have hl:0≤z:=(norm_nonneg _).trans t
  have hx:=hasSum_nat_add_iff' 3|>.2 (charge_sum A v h p q w J i a); let Q(n:ℕ):= (n+2:ℝ)*(n+3:ℝ)*r^(n+1); have hq(n:ℕ) : Q n ≤ 6*r*((1/2:ℝ)^n):=by
    induction n with
    | zero=> unfold Q; refine le_of_eq ?_; norm_num -- tune
    | succ n ih=> 
                  apply le_trans (b:=Q n * (1/2)) _ ((mul_le_mul_of_nonneg_right ih (by norm_num)).trans_eq (by rw [pow_succ]; ring)); unfold Q; rw [pow_succ (n:=n+1)]; push_cast; have hp:0 ≤ r^(n+1):=by positivity
                  nlinarith [mul_le_mul_of_nonneg_right v (show 0≤ (n+4:ℝ)*(n+3:ℝ)*r^(n+1) by positivity), mul_nonneg (show 0 ≤ (n:ℝ) *(n+3) by positivity) hp]
  have hp(y:ℕ):‖mixedTrace A X Y (y+3)‖≤6*r*x*z*((1/2:ℝ)^y):= by apply (hz (y+1)).trans; push_cast; rw [show (y+1:ℝ)+1=y+2 from by ring, show (y+1:ℝ)+2=y+3 from by ring]; exact le_trans (b:= (6*r*((1/2:ℝ)^y))*x*z) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hq y) k) hl) (le_of_eq (by ring)) -- tune
  have hh := (summable_geometric_of_lt_one (show 0≤(1/2:ℝ) by norm_num) (by norm_num)).mul_left (6*r*x*z); have hy:=hh.of_nonneg_of_le (fun n=>norm_nonneg _) hp; let W:=mixedTrace A X Y; have hg: (∑ i∈range 3,mixedTrace A X Y i)= -(1/4:ℝ)*trR (X*Y):=by
    rw [sum_range_succ _ 2,sum_range_succ _ 1,sum_range_one]; unfold mixedTrace; rw [mix_2,show coefficient 2= -(1/8:ℝ) from by norm_num [coefficient,c],show mixed A X Y 1=0 from by unfold mixed; noncomm_ring,show mixed A X Y 0=0 from by unfold mixed; noncomm_ring]; rw [plus_t,comm_t Y X]; simp [trR]; ring
  rw [hg,neg_mul,sub_neg_eq_add] at hx; rw [←hx.tsum_eq,←Real.norm_eq_abs]; refine ((norm_tsum_le_tsum_norm hy).trans (hy.tsum_le_tsum hp hh)).trans_eq ?_; rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
-- apply to shifted Hamiltonians. sign here critical.
def bump (A X : Op n):= A^2-(A+X)^2
lemma mix_raise (p:Safe A)(s:Safe (A+X))(e:Safe (A+Y))(f:Safe (A+X+Y))(hXY:X*Y=0)
    (u:Influence x (bump A X))(t:‖bump A Y‖≤ z)(v:r≤1/4)(k:0≤x)(h:‖1-A^2‖≤r)(h1:‖1-(A+X)^2‖≤r)(h2:‖1-(A+Y)^2‖≤r)(h3:‖1-(A+X+Y)^2‖≤r): -(1/4:ℝ)* trR (bump A X * bump A Y)-12*r*x*z ≤ 2 *(energy (A+X+Y)+energy A-energy (A+X)-energy (A+Y)) := by
  let F:=1-A^2; let L:=bump A X; let V:= bump A Y
  have he:F+L=1-(A+X)^2:=by unfold F L bump; abel
  have hx:F+V=1-(A+Y)^2:=by unfold F V bump; abel
  have hX:IsSelfAdjoint X:=by rw [←add_sub_cancel_left A X]; exact s.self.sub p.self
  have hY:IsSelfAdjoint Y:=by rw [←add_sub_cancel_left A Y]; exact e.self.sub p.self
  have hc:Y*X=0:=by rw [←hX.star_eq,←hY.star_eq,←star_mul,hXY,star_zero]
  have hz:F+L+V=1-(A+X+Y)^2:=by rw [he]; unfold V bump; rw [show (A+X+Y)^2= (A+X)^2+(A+Y)^2 -A^2+(X*Y+Y*X) from by noncomm_ring,hXY,hc]; abel
  have hh:= mix_cost F v h (he ▸ h1) (hx ▸ h2) (hz ▸ h3) u t k (IsSelfAdjoint.one _ |>.sub (p.self.pow 2)) ((p.self.pow 2).sub (s.self.pow 2)) ((p.self.pow 2).sub (e.self.pow 2))
  unfold rootMixed at hh; rw [hz,hx,he] at hh -- order?
  simp only [F,sub_sub_cancel] at hh; rw [energy_eq f, energy_eq p, energy_eq s, energy_eq e]; simp only [plus_t]; linarith [abs_le.mp hh]
end cross
end YM.CF.Fixed.Bulk
