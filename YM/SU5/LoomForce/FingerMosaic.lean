import YM.SU5.LoomForce.GaugeWake
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
-- self Wick of a spin-zero fingerprint. TWO possibly different frame
-- material maps into one regulator Gaussian. cross not assuming positivity until election.
open Next.Rank Buffered Afterglow.Tower.VacuumSelection.Spine.LoomForce
open ProbabilityTheory NormedSpace WickG MeasureTheory
open Regis.Resonance
namespace Finger
variable {I Q:Type*}[Fintype I][Fintype Q][DecidableEq Q]
local notation "Έ"=> I→I→ℂ
variable (F X Y:I→I→ℂ)
def Ledger (K X: I→ I→ℂ): ℂ:= ∑ i:I, ∑ j:I, star (K i j) * ( ∑ u:I, ∑ v:I,K u v* (X i u* X j v+X i v*X j u) )
def account (G:Έ)(x:I→ℝ): ℂ:= ∑ i:I,∑ j:I,G i j*(x i:ℝ)*(x j:ℝ)

variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] (U V:I→E)
local notation "μ"=> stdGaussian E
local notation "L[" F "," X "]"=> fun x:E=> account F (fun i:I=> inner ℝ (X i) x)
local notation "M₀"=> L[F,V]
local notation "M₁"=> fun x:E=> star ((L[F,U]) x)
local notation "Kx"=> WickG.grainG
private lemma pay_l (p:List E): (∫ x, (payday p x:ℂ) ∂μ)= WickG.read Kx p:= by rw [integral_complex_ofReal,WickG.read,peek_memo _ _ (le_refl _ )]
lemma bookFull : (∫ x,(M₁ x)*(M₀ x) ∂μ) - (∫ x,M₁ x ∂μ)*(∫ x,M₀ x∂μ) = Ledger F (fun x y=> WickG.grainG (U x) (V y)):=by
 let f(i:I×I):= [U i.1,U i.2]; let g(i:I×I):= [V i.1,V i.2]; let A(i:I×I):ℂ:= star (F i.1 i.2); let B(i:I×I):ℂ:= F i.1 i.2
 let l (C:ℂ)(p:List E)(x:E):= C* (payday p x:ℂ); let w (C:ℂ)(p:List E):= C*WickG.read Kx p
 have hu(X:I→E)(x:E): (L[F,X]) x=∑ i:I×I,l (B i) [X i.1,X i.2] x:= by
    unfold account; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp [B,l,payday,mul_assoc]
 have hv(x:E): M₀ x= ∑ i:I×I,l (B i) (g i) x:= hu V x
 have hh(x:E): M₁ x= ∑ i:I×I,l (A i) (f i) x:= by change star ((L[F,U]) x) =_; rw [hu,star_sum]; exact sum_congr rfl fun i _=> by dsimp only [A,B,l,f]; rw [star_mul', show star (↑(payday _ x):ℂ)=_ from Complex.conj_ofReal _]
 have ht(x:E): M₁ x*M₀ x=∑ i:I×I,∑ j:I×I,l (A i*B j) (f i ++ g j) x:=by
    rw [hh x,hv x,sum_mul]; simp_rw [mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp only [f,g,l,payday,List.map_append,List.prod_append,Pi.mul_apply,Complex.ofReal_mul]; ring
 have he(a:ℂ)(L:List E): Integrable (l a L) μ:= (payday_val L).accepted.ofReal.const_mul a
 have hl(a:ℂ)(p:List E): (∫ x,l a p x∂μ)= w a p:=by unfold l w; rw [integral_const_mul,pay_l]
 let a:= M₁; let b:= M₀
 change (∫ x, a x*b x∂μ)-(∫ x,a x∂μ)*(∫ x,b x∂μ) = _
 have hz(x:E): a x*b x= ∑ i:I×I,∑ j:I×I,l (A i*B j) (f i ++ g j) x:= ht x
 have hA(x): a x =∑ i:I×I, l (A i) (f i) x:=hh x; have hB(x): b x = ∑ i:I×I, l (B i) (g i) x:=hv x
 simp_rw [hz,hA,hB,integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> he _ _)),integral_finsetSum _ (fun i _=> he _ _),hl]
 unfold Ledger; rw [sum_mul]; simp_rw [mul_sum]; rw [←sum_sub_distrib,Fintype.sum_prod_type]; simp_rw [←sum_sub_distrib,Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>sum_congr rfl (fun j _=> sum_congr rfl fun i₁ _=> sum_congr rfl fun v _=>?_)
 simp [w,f,g,read_more,WickG.pick,A,B]; ring
#print axioms bookFull
-- compact response on fixed rank type. Keep > since timeline shrinking and need quantitative gap

variable {X Y}
omit [Fintype I] in
private lemma crossbill (d b:ℝ)(h:0≤b)(t:0 ≤d)(p:∀ i j,‖Y i j‖≤ b)(u:∀ i j,‖X i j-Y i j‖≤ d)(i j l u':I) : ‖X i j * X l u'-Y i j* Y l u'‖ ≤ 2*b*d+d^2:=by
 have hx: ‖X i j‖ ≤ ‖Y i j‖+‖X i j-Y i j‖:=by have ht:=norm_add_le (X i j-Y i j) (Y i j); rw [sub_add_cancel,add_comm] at ht; exact ht
 calc
    _ ≤ ‖X i j-Y i j‖*‖Y l u'‖+ ‖X i j‖*‖X l u'-Y l u'‖:=by
      simp_rw [←norm_mul]; rw [show X i j* X l u'-_= (X i j-Y i j)*Y l u'+X i j*(X l u'-Y l u') by ring]; apply norm_add_le
    _ ≤ d*b+(b+d)*d:=add_le_add (mul_le_mul (u _ _) (p _ _) (norm_nonneg _) t) (mul_le_mul (hx.trans (add_le_add (p _ _) (u _ _))) (u _ _) (norm_nonneg _) (add_nonneg h t))
    _ = _:=by ring

lemma variance_drift {C:ℝ}(c:∑ i:I,∑ j:I,‖F i j‖ ≤ C) (d b:ℝ)(hp:0≤b)(t:0≤d)(p:∀ i j,‖Y i j‖≤ b)(u:∀ i j,‖X i j-Y i j‖≤ d): ‖Ledger F X-Ledger F Y‖ ≤ C^2*(2*(2*b*d+d^2)):=by
 let Q:= 2*b*d+d^2; have hQ:0≤ Q:= by unfold Q; positivity
 unfold Ledger; rw [←sum_sub_distrib]; simp_rw [←sum_sub_distrib,←mul_sub,←sum_sub_distrib,←mul_sub]; refine (norm_sum_le ..).trans ?_
 have ht(G:I→I→ℂ)(D:ℝ)(hm:∀ i j, ‖G i j‖≤ ‖F i j‖*D)(hz:0≤D): ∑ i:I,‖∑ j:I,G i j‖ ≤ C*D:=le_trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans ((sum_le_sum (fun j _=> hm i j)).trans_eq (sum_mul ..).symm))) (by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right c hz) -- try
 have hC:0≤ C:= (sum_nonneg (fun i _=> sum_nonneg (fun j _=> norm_nonneg _))).trans c
 rw [pow_two C,mul_assoc]; apply ht _ _ _ (mul_nonneg hC (mul_nonneg (by norm_num) hQ))
 intro i j; rw [norm_mul,norm_star]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 apply (norm_sum_le ..).trans (ht _ _ _ (by change 0 ≤ 2*Q; positivity)); intro z u'; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [add_sub_add_comm]; let k:=crossbill d b hp t p u
 exact (norm_add_le ..).trans ((add_le_add (k i z j u') (k i u' j z)).trans_eq (two_mul _).symm)
#print axioms variance_drift
#check @sum_mul_sq_le_sq_mul_sq
variable (t:I→Q)
def credit(q r:Q):ℂ:=∑ i:I with t i=q, ∑ j:I with t j=r, F i j
local notation "ψ"=> credit F t
-- DecidableEq Q consistent instances; no change
private lemma repl (F:I→I→ℂ) (K:Q→Q→ℂ): (∑ i:I,∑ j:I,F i j*K (t i) (t j))=∑ i:Q,∑ j:Q,credit F t i j * K i j:=by
 unfold credit; simp_rw [sum_mul]; rw [←sum_fiberwise_of_maps_to (t:=univ) (g:=t) (fun i _=> mem_univ (t i))]; refine sum_congr rfl fun i _=>?_
 conv_rhs => rw [sum_comm]
 refine sum_congr rfl fun j u=>?_ ; rw [(mem_filter.mp u).2,←sum_fiberwise_of_maps_to (t:=univ) (g:=t) (fun i _=> mem_univ (t i))]; refine sum_congr rfl fun k _=> sum_congr rfl fun i₁ u=>?_ ; rw [(mem_filter.mp u).2]
lemma bookDown (X:Q→Q→ℂ): Ledger F (fun x y=> X (t x) (t y)) = Ledger (credit F t) X:=by
 let K(i j:Q):ℂ:= ( ∑ u:Q, ∑ v:Q,credit F t u v* (X i u * X j v+X i v * X j u) )
 unfold Ledger; rw [sum_congr rfl (show ∀ i:I,i∈univ→ _ = ∑ j:I,star (F i j)*K (t i) (t j) from fun i _=>sum_congr rfl fun j _=> congrArg (star (F i j) * ·) (repl t F (fun u v=> X (t i) u * X (t j) v + X (t i) v * X (t j) u)))]
 rw [show (∑ i:I,∑ j:I,star (F i j)*K (t i) (t j))= _ from repl t (fun i j=> star (F i j)) K]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw [show credit (fun i j=> star (F i j)) t i j= star (credit F t i j) from ?_]; unfold credit; simp_rw [star_sum]

lemma revenue_total (p:∀ i j,F i j= F j i)(m:ℝ) : Ledger F (fun x y=> if t x=t y then (m:ℂ) else 0)= ((2*m^2*∑ i:Q,∑ j:Q,‖credit F t i j‖^2:ℝ) : ℂ):=by
 rw [bookDown F t (fun i j=> if i=j then (m:ℂ) else 0)]; unfold Ledger
 have ht(i j:Q): ψ i j= ψ j i:=by unfold credit; rw [sum_comm]; exact sum_congr rfl fun a _=> sum_congr rfl fun b _=> p b a
 let s:= fun i j:Q=> if i=j then (m:ℂ) else 0
 have hy(i j:Q): ∑ u:Q, ∑ v:Q, ψ u v * (s i u*s j v)= ψ i j*(m:ℝ)^2:=by
    have he{u}:u≠i→s i u=0:=fun p=>if_neg (Ne.symm p)
    have hk{v}:v≠j→s j v=0:=fun p=>if_neg (Ne.symm p)
    rw [sum_eq_single_of_mem i (mem_univ _) (by intros; apply sum_eq_zero; intros; rw [he (by assumption),zero_mul,mul_zero]), sum_eq_single_of_mem j (mem_univ _) (by intros; rw [hk (by assumption),mul_zero,mul_zero]),pow_two]; simp [s]
 have hu(i j:Q): (∑ u:Q, ∑ v:Q,ψ u v *(s i v*s j u))= ψ i j*(m:ℝ)^2:=by
    conv_lhs => arg 2; ext u; arg 2; ext v; rw [mul_comm (s i v)]
    rw [hy j i,ht j i]
 have hm(i j:Q):star (ψ i j)*(∑ u:Q, ∑ v:Q, ψ u v*(s i u*s j v+s i v*s j u))=2*(m:ℂ)^2 * (↑‖ψ i j‖ :ℂ)^2:=by
   simp_rw [mul_add,sum_add_distrib]; rw [hy i j,hu i j]; rw [←Complex.mul_conj']; change _= _*(ψ i j*star (ψ i j)); ring
 change (∑ i:Q,∑ j:Q, star (ψ i j)*(∑ u:Q,∑ v:Q, ψ u v*(s i u*s j v+s i v*s j u)))= _
 simp_rw [hm]; push_cast; simp_rw [mul_sum]
#print axioms revenue_total

def probe (x:Q→ℝ): ℝ:= 1+∑ i:Q×Q,‖(x i.1:ℂ)*(x i.2:ℝ)‖^2
omit [DecidableEq Q] in
lemma probe_pos (x:Q→ℝ): 0 < probe x:= add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun _ _=> sq_nonneg _)
lemma revealed (m:ℝ)(x: Q→ℝ)(p:∀ i j,F i j=F j i) {a:ℝ}(d:0≤a)
    (u:a≤ (account F (x∘t)).re) : 2*m^2*(a^2/probe x)≤ (Ledger F (fun i j=> if t i=t j then (m:ℂ) else 0)).re := by
 rw [revenue_total F t p m,Complex.ofReal_re]; apply mul_le_mul_of_nonneg_left _ (by positivity)
 let Q' := Q×Q; let V:= ψ; let z(i:Q') :ℂ:= (x i.1:ℂ)*(x i.2:ℝ); let u':= uncurry V
 have hv:account F (x∘t)=∑ i:Q',u' i*z i:= by
    unfold account; simp only [Function.comp,Function.uncurry,z,u']; rw [Fintype.sum_prod_type]; simp_rw [mul_assoc]; exact repl t F (fun i j=> (x i:ℂ) * (x j:ℝ))
 rw [hv] at u; have ht:= u.trans ((Complex.re_le_norm _).trans (norm_sum_le ..))
 simp_rw [norm_mul] at ht; let U:= fun i=>‖u' i‖; let Z:= fun i=>‖z i‖
 have hp:= (pow_le_pow_left₀ d ht 2).trans (sum_mul_sq_le_sq_mul_sq univ U Z)
 apply (div_le_iff₀ (probe_pos x)).mpr; apply hp.trans; rw [← Fintype.sum_prod_type' _] -- wrong lemma
 exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (sum_nonneg fun i _=>sq_nonneg (U i))
#print axioms revealed
end Finger
end YM.CF.LitCurrent.Surplus
