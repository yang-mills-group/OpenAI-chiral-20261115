import YM.SU5.FiniteGaugeData.CodaT.Pep
import Mathlib.Analysis.Complex.BorelCaratheodory
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
namespace Aria
private lemma dg_money {n:Type*}[LinearOrder n][Fintype n](u:ℂ)(x:Op n):dg (u • x)=u • dg x:=by unfold dg dyad; simp only [Matrix.smul_apply,smul_sum,smul_eq_mul,smul_smul]; -- tune
-- Family stencil bounds, any mort affordable. can use known nilpot class after coupling.
variable (m:ℕ)(x:W K)(ζ:ℂ)
def tail : W K:= ∑ i∈ range m, (((i.factorial:ℂ)⁻¹) • (ζ • x)^i)
lemma powerAt (S:Finset Cover)(b:Locator K x S):Locator K (x^m) S:=by induction m with|zero=> exact (pow_zero x).symm ▸ locate_one K S|succ m ih=> rw [pow_succ]; exact locate_join _ _ ih b
-- presentation via Family val map
lemma party {I:Type*}(f:I→W K)(S: Finset Cover) (V:Finset I)(p:∀ i∈V,Locator K (f i) S):Locator K (∑ i∈ V,f i) S:=by
 classical
 induction V using Finset.induction_on with
 | empty=> rw [sum_empty]; exact locate_zero ..
 | insert i s h ih=> rw [sum_insert h]; exact locate_sum _ _ (p i (mem_insert_self ..)) (ih fun j u=> p _ (mem_insert_of_mem u))
lemma tailSite(b:Locator K x S):Locator K (tail m x ζ) S:=party _ S _ (fun i v=>locate_scale K _ _ (powerAt i _ S (locate_scale K _ _ b)))
lemma cosum {I:Type*}(f:I→ W K)(A:Finset I): (∑ i∈A,f i).val=∑ i∈A,(f i).val:= map_sum (well K).val _ _ 
lemma flare(b:Locator K x S)(r:ℝ)(h:0≤r): ∃ c:ℝ,0≤c ∧∀ (ζ:ℂ),‖ζ‖≤r →∀ n:Side,∀ U:Fields (K.c n), ‖(tail m x ζ).val n U‖ ≤ c:=by
 let U:= duration S*‖reading K S x b‖; let M(i:ℕ):ℝ:= ‖((i.factorial:ℂ)⁻¹)‖*(r*U)^i; have he:0≤U:=mul_nonneg (duration_pos _).le (norm_nonneg _)
 refine ⟨∑ i∈ range m,M i,sum_nonneg (fun i _=> mul_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg h he) _)),fun ζ hz n z=>?_⟩
 have hw:‖x.val n z‖≤U:=by nth_rw 1 [←reading_p K S x b]; exact compose_price S _ (reading K S x b) _ _
 let T:= r*U; have hv: ‖ζ • x.val n z‖≤r*U:=by rw [norm_smul]; exact mul_le_mul hz hw (norm_nonneg _) h
 unfold tail; simp_rw [cosum,Subalgebra.coe_smul,Subalgebra.coe_pow,Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) hv i)) (norm_nonneg _) -- tune ^0. Nonempty yes
lemma raiseX(hu:x^m=0)(T:Side)(g:Fields (K.c T)): (tail m x ζ).val T g=exp (ζ • x.val T g):=by
 let F:=ζ • x; have ht:F^m=0:=by unfold F; rw [smul_pow,hu,smul_zero];
 unfold tail; rw [exp_eq_tsum ℂ]; simp_rw [cosum,Subalgebra.coe_smul,Subalgebra.coe_pow,Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]; change _=∑' i:ℕ,(i.factorial:ℂ)⁻¹ • ((ζ • x).val T g)^i; refine (tsum_eq_sum (s:=range m) ?_).symm; intro i hi
 let X:=F^i; have hz:F^i=0:=pow_eq_zero_of_le (Nat.le_of_not_gt (mt mem_range.mpr hi)) ht; apply smul_eq_zero_of_right -- lemma?
 have T0: X.val T g=0:=by unfold X; rw [hz]; rfl
 exact T0
-- exact nonlinear marker
variable (A:Desire K S)
lemma germ (p:A.paid^m=0)(U:Fields (K.c N)): (tail m A.paid ζ).val N U= quant (1+ζ • A.print (K.c N) U.1):=by
 rw [raiseX _ _ _ p N U,A.ticket]; unfold projectF; rw [←dg_money]; apply tallied; rw [Matrix.mul_smul, Matrix.smul_mul,A.nil, smul_zero,smul_zero]
lemma soldGerm {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)(s i:ℕ)(A:Desire (tent Y h) S)(p:A.paid^m=0): sold Y h s i (tail m A.paid ζ).val = fun X=> quant (1+ ζ • A.print (side Y i s) X.1):= by
 rw [sold_v]; unfold send; rw [funext (germ (N:=momentm Y i s) m ζ A p)]; exact castK (terrain Y h (Y.ir i) s) A
where castK{N M:Side}{S:Finset Cover}{K:Calibration}(p:N=M)(A:Desire K S): let f:Mark N:=fun X=> quant (1+ζ • A.print N X.1); (show Mark M from p ▸ f)=fun X=>quant (1+ζ • A.print M X.1):=by subst M; rfl
local notation "A₁"=> W K →ₗ[ℂ]ℂ
def noteT (Φ:W K→ₗ[ℂ]ℂ):ℂ→ℂ :=fun ζ=>Φ (tail m x ζ)
variable (Φ:W K →ₗ[ℂ]ℂ) (h₁:Φ 1=1)(hm: 2 ≤ m)
lemma note_formula : noteT m x Φ ζ = ∑ i∈range m, (i.factorial:ℂ)⁻¹*(ζ^i*Φ (x^i)):= by unfold noteT tail; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,smul_pow,map_smul]; rfl
lemma note_next(k:ℕ): noteT (k+1) x Φ = fun ζ=> noteT k x Φ ζ + (k.factorial:ℂ)⁻¹*(ζ^k*Φ (x^k)):=by funext; rw [note_formula,note_formula,sum_range_succ]
lemma poem : Differentiable ℂ (noteT m x Φ):=by rw [funext (fun ζ=> note_formula m x ζ Φ)]; fun_prop
include h₁ hm
lemma at_two : noteT m x Φ 0=1:=by
 rw [note_formula,sum_eq_single 0]; · simp [h₁]
 · intro b _ h; simp [h]
 intro h; simp at h; omega
lemma lyric : HasDerivAt (noteT m x Φ) (Φ x) 0:=by
 obtain ⟨y,rfl⟩:= Nat.exists_eq_add_of_le' hm; induction y with
 | zero=>
          rw [Nat.zero_add,note_next x Φ 1,note_next x Φ 0, show noteT 0 x Φ=0 from funext fun i=> (by simp [noteT,tail])]; simp only [Nat.factorial, Nat.cast_one,mul_one,inv_one, pow_zero,pow_one,one_mul,h₁, Pi.zero_apply,zero_add]; simpa using! (((hasDerivAt_id' (0:ℂ)).mul_const (Φ x)).const_add 1)
 | succ y ih=> rw [show y+1+2=y+2+1 from by omega, note_next x Φ];
                have he:= ((hasDerivAt_id' (0:ℂ)).pow (y+2)).mul_const (Φ (x^(y+2)))|>.const_mul ((↑(Nat.factorial (y+2)):ℂ)⁻¹); simp at he; convert (ih (by omega)).add he using 1 <;> (first| simp only [add_zero]| rfl) -- tune
-- price witness subharmonic derivative.L
omit h₁ hm
lemma capRate {p:ℂ}{f:ℂ→ℂ}(U:f 0=0)(F:DifferentiableOn ℂ f (ball 0 r))(pH:HasDerivAt f p 0)(hp:0<t)(he:0<r)(hw:∀ z∈ ball 0 r,(f z).re ≤ t): ‖p‖ ≤ 4*t /r:= by
 rw [← pH.deriv, norm_deriv_eq_norm_fderiv]; have ht:0<r/2:=by positivity
 apply norm_fderiv_le_of_lip' ℂ (by positivity) -- tune
 filter_upwards [ball_mem_nhds (0:ℂ) ht] with z v; have hg:= mem_ball_zero_iff.mp v
 rw [U,sub_zero,sub_zero]; apply (Complex.borelCaratheodory_zero hp F (fun z v=>hw z v) he (mem_ball_zero_iff.mpr (by linarith : ‖z‖ < r)) U).trans; rw [div_mul_eq_mul_div]; rw [div_le_div_iff₀ (show 0 < r-‖z‖ by linarith) he]; nlinarith only [mul_le_mul_of_nonneg_left hg.le (show 0≤t*‖z‖ from by positivity)]
lemma come {p c:ℂ}{f:ℂ→ℂ}(U:f 0=1)(F:DifferentiableOn ℂ f (ball 0 r))(pH:HasDerivAt f p 0)(hp:0<t)(he:0<r)(hw:∀ z∈ ball 0 r, ‖f z‖ ≤ Real.exp ((z*c).re)*(1+t)): ‖p-c‖ ≤ 4*t/r:= by
 let g(z:ℂ):=f z*Complex.exp (-z*c)-1; have h(v:ℂ): v*(-1)= -v:=by simp
 have hh:HasDerivAt g (p-c) 0:=by
    simpa [g,sub_eq_add_neg,U] using (pH.mul (((hasDerivAt_id' (0:ℂ)).neg.mul_const c).cexp)).sub_const (1:ℂ)
 refine capRate (f:=g) (by simp [g,U]) (by unfold g; fun_prop) hh hp he ?_; intro z v; let X:=z*c; let Z:= f z * Complex.exp (-X); have he:‖Z‖ ≤1+t:=by
    have heX :(Real.exp (-X).re)= (Real.exp X.re)⁻¹:=by rw [Complex.neg_re,Real.exp_neg]
    unfold Z; rw [norm_mul,Complex.norm_exp,heX]; exact (mul_le_mul_of_nonneg_right (hw z v) (by positivity)).trans_eq (by unfold X; field_simp)
 rw [show g z=Z-1 by unfold g Z X; rw [neg_mul],Complex.sub_re, Complex.one_re]; linarith only [he,Complex.re_le_norm Z]
end Aria
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
