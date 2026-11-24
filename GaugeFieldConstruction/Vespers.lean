import GaugeFieldConstruction.Nimble
/-! # Fourier windows with weighted ℓ². -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch
section
-- distribution of support positions as real linear forms. E can be single or pair. no assumption a=2 entrywise for Reel if using Tape.
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def PayS (P:E→L[ℝ]ℝ) : E→ ℂ:=fun x=> Complex.exp (Complex.I*↑(P x))
lemma PayS_diff (P:E→L[ℝ]ℝ)(x:E): let f(t:ℝ):=PayS P (t • x); ∀ t:ℝ, HasDerivAt f (f t*(Complex.I*↑(P x))) t :=by
 intro f t; unfold f PayS; simp_rw [map_smul P,smul_eq_mul, Complex.ofReal_mul]
 let K:=Complex.I* (P x:ℂ); have he: HasDerivAt (fun i:ℝ=> (i:ℂ)* K) K t:= by simpa only [one_mul] using ((show HasDerivAt (fun i:ℝ=> (i:ℂ)) 1 t from Complex.ofRealCLM.hasFDerivAt.hasDerivAt).mul_const K)
 have ht(i:ℝ): (i:ℂ)*K=Complex.I*((i:ℂ)*(P x:ℂ)):=by unfold K; ring
 simp_rw [←ht]; exact he.cexp -- tune order
lemma pay_zero(P:E→L[ℝ]ℝ) : PayS P 0=1:=by simp [PayS]
lemma pay_money(P:E→L[ℝ]ℝ)(x:E): ‖PayS P x‖=1:=by simp [PayS,Complex.norm_exp]
abbrev FeeL(P:E→L[ℝ]ℝ):= Complex.I • Complex.ofRealCLM.comp P
def FeeD (P:E→L[ℝ]ℝ): Bank.Duo E ℂ :=by
 let X:=FeeL P; let M:= ContinuousLinearMap.mul ℝ ℂ; exact ⟨(((M.comp X).flip.comp X).flip),fun i j=>mul_comm ..⟩
def bookP (P:E→L[ℝ]ℝ)(z:ℂ):Ole E ℂ :=postF (1, FeeL P, FeeD P) ((ContinuousLinearMap.mul ℝ ℂ).flip z)
lemma factor_sale (P:E→L[ℝ]ℝ)(z:ℂ) : AptK (fun x=> PayS P x*z) (bookP P z):=by
 have he: AptK (PayS P) (1,FeeL P,FeeD P):=by
    constructor; intro x; let f(t:ℝ):= PayS P (t • x); let L:= Complex.I*(P x:ℂ); have hx(t): HasDerivAt f (f t*L) t:=PayS_diff P x t; have hp: deriv f= fun i=>f i*L:= funext fun i=>(hx i).deriv; have hv:f 0=1:=by rw [show f 0=PayS P 0 from (by unfold f; rw [zero_smul]),pay_zero]
    refine ⟨?_,hv, ?_,?_⟩
    · refine (show ContDiff ℝ (1+1) f from contDiff_succ_iff_deriv.mpr ⟨fun i=> (hx i).differentiableAt,by norm_num,?_⟩).contDiffAt.of_le (by norm_num)
      rw [hp]; apply ContDiff.mul _ contDiff_const; apply contDiff_one_iff_deriv.mpr; have hg : Differentiable ℝ f:=fun _=>(hx _).differentiableAt; exact ⟨hg,hp.symm ▸ hg.continuous.mul continuous_const⟩
    · change deriv f 0=L; rw [(hx _).deriv,hv,one_mul]
    change deriv (deriv f) 0=L*L; rw [hp]; exact ((hx 0).mul_const _).deriv.trans (by rw [hv,one_mul])
 exact he.geomF ((ContinuousLinearMap.mul ℝ ℂ).flip z)
lemma fund0 (P:E→L[ℝ]ℝ)(z:ℂ): (bookP P z).1=z:= one_mul z
lemma fund1 (P:E→L[ℝ]ℝ)(z:ℂ)(x:E): (bookP P z).2.1 x= (Complex.I*↑(P x))*z:= rfl
lemma fund2 (P:E→L[ℝ]ℝ)(z:ℂ)(x y:E): (bookP P z).2.2.val x y=(Complex.I*↑(P x))*(Complex.I*↑(P y))*z:=rfl
lemma fundK (P:E→L[ℝ]ℝ)(z:ℂ){r:ℝ}(t:‖P‖≤r)(p:1≤ r): ‖bookP P z‖ ≤ r^2*‖z‖:=by
 let A:=bookP P z; let X:= r^2*‖z‖; have hp:0≤r:=zero_le_one.trans p; have h:0≤X:=by unfold X; positivity
 have hx(x): ‖Complex.I*(P x:ℂ)‖≤ r*‖x‖:= by rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]; exact (P.le_opNorm x).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _))
 rw [Prod.norm_def, Prod.norm_def]; refine max_le (by rw [fund0]; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ p)) (max_le ?_ ?_)
 · refine ContinuousLinearMap.opNorm_le_bound _ h fun i=>?_ ; rw [fund1,norm_mul]; refine (mul_le_mul_of_nonneg_right (hx i) (norm_nonneg _)).trans ?_; linarith only [mul_le_mul_of_nonneg_right (show r ≤ r^2 from (le_self_pow₀ p (by decide))) (show 0 ≤ ‖i‖*‖z‖ by positivity)]
 apply ContinuousLinearMap.opNorm_le_bound A.2.2.val h; intro x; apply ContinuousLinearMap.opNorm_le_bound _ (M:=X*‖x‖) (by positivity); intro y; unfold A; rw [fund2,norm_mul,norm_mul]; refine (mul_le_mul_of_nonneg_right (mul_le_mul (hx x) (hx y) (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans_eq ?_; unfold X; ring
variable {I:Type*}
set_option maxHeartbeats 90000 in
lemma mainStream [FiniteDimensional ℝ E] (F:I→ℂ)(Q:I→E→L[ℝ]ℝ)(u:I→ℝ)(ht:∀ i,‖Q i‖≤ u i)(h:∀ i,1 ≤ u i)(p:Summable (fun i=> u i^2 * ‖F i‖)):
 let Z(i):= bookP (Q i) (F i); let f(x):= ∑' i,PayS (Q i) x * F i
 ∃ V: Ole E ℂ,AptK f V∧ ‖V‖ ≤ ∑' i,u i^2*‖F i‖∧ V.1=(∑' i,(Z i).1)∧ V.2.1=(∑' i,(Z i).2.1)∧ V.2.2.val= (∑' i,(Z i).2.2.val):=by
 intro Z f; let K(i):= u i^2*‖F i‖; let X(i):=(Z i).1; let D(i):=(Z i).2.1; let Qp(i):=(Z i).2.2.val; let A₁:=∑' i,D i; let A₂:= ∑' i,Qp i; let A₀:=∑' i,X i;
 have htZ(i):‖Z i‖≤ K i:= fundK _ _ (ht i) (h i);
 have h₁(i): ‖X i‖ ≤ K i:= (le_max_left .. |>.trans (htZ i))
 have h₂(i): ‖D i‖ ≤ K i:= ((le_max_left ..).trans (le_max_right ..)).trans (htZ i)
 have h₃(i): ‖Qp i‖ ≤ K i:= ((le_max_right ..).trans (le_max_right ..)).trans (htZ i)
 have hp:= p.of_nonneg_of_le (fun i=>norm_nonneg (X i)) h₁; have hg:= p.of_nonneg_of_le (fun i=>norm_nonneg (D i)) h₂; have hu:= p.of_nonneg_of_le (fun i=>norm_nonneg (Qp i)) h₃;
 have hvD : Summable D:=hg.of_norm; have hx: Summable Qp:= hu.of_norm
 have he(i j:E): A₂ i j=∑' t,Qp t i j := ((ContinuousLinearMap.apply ℝ ℂ j).comp (ContinuousLinearMap.apply ℝ (OneF E ℂ) i)).map_tsum hx
 let Wp:Ole E ℂ:= (A₀,A₁,⟨A₂,fun i j=>by rw [he i j,he j i]; exact tsum_congr (fun i=> (Z i).2.2.property ..)⟩)
 refine ⟨Wp,⟨fun i=>?_⟩, (show max ‖A₀‖ (max ‖A₁‖ ‖A₂‖) ≤ ∑' i,K i from max_le ((norm_tsum_le_tsum_norm hp).trans (hp.tsum_le_tsum h₁ p)) (max_le ((norm_tsum_le_tsum_norm hg).trans (hg.tsum_le_tsum h₂ p)) ((norm_tsum_le_tsum_norm hu).trans (hu.tsum_le_tsum h₃ p)))),rfl,rfl,rfl⟩

 let A(j:I): E→ℂ:= fun x=> PayS (Q j) x*F j; let H(j:I)(t:ℝ):= A j (t • i); let L(j):= Complex.I*(Q j i:ℂ)
 let B(j:I)(t:ℝ):= H j t * L j; let V(j:I)(t:ℝ):= B j t * L j
 have hL(j): ‖L j‖≤ u j*‖i‖:=by unfold L; rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]; exact ((Q j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (ht j) (norm_nonneg _))
 have hH(j t): ‖H j t‖=‖F j‖:=by unfold H A; rw [norm_mul,pay_money,one_mul]
 have hS(t:ℝ):Summable (fun j=>H j t):= Summable.of_norm_bounded p (fun i=> by rw [hH]; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (h i)))
 have hX(j t): ‖B j t‖≤ K j*‖i‖:=by unfold B; rw [norm_mul,hH]; apply (mul_le_mul_of_nonneg_left (hL j) (norm_nonneg _)).trans; unfold K; linarith only [mul_le_mul_of_nonneg_left (le_self_pow₀ (h j) (by decide: (2:ℕ)≠0)) (show 0≤ ‖F j‖*‖i‖ by positivity)]
 have hV(j t): ‖V j t‖≤ K j*‖i‖^2:=by
    unfold V B; rw [norm_mul,norm_mul,hH]; refine (mul_le_mul (mul_le_mul_of_nonneg_left (hL j) (norm_nonneg _)) (hL j) (norm_nonneg _) (by have ht:=h j; positivity)).trans_eq ?_; unfold K; ring
 have hb(j t): HasDerivAt (H j) (B j t) t:= ((PayS_diff (Q j) i t).mul_const (F j)).congr_deriv (mul_right_comm ..)
 have hv(j t): HasDerivAt (B j) (V j t) t:= (hb j t).mul_const _
 let R(t:ℝ):=∑' j,B j t; let Y(t:ℝ):=∑' j,V j t; let W(t:ℝ):= f (t • i); have hr(t): HasDerivAt W (R t) t:= hasDerivAt_tsum (show Summable (fun i' => K i'*‖i‖) from p.mul_right _) hb hX (hS 0) t
 have hy(t): HasDerivAt R (Y t) t:= hasDerivAt_tsum (p.mul_right _) hv hV (Summable.of_norm_bounded (p.mul_right _) (fun j=>hX j (0:ℝ))) t
 have hQ : ContDiff ℝ (1+1) W:=contDiff_succ_iff_deriv.mpr ⟨fun t=>(hr t).differentiableAt,(by norm_num),show ContDiff ℝ 1 (deriv W) from by
    rw [funext (fun t=> (hr t).deriv)]; refine contDiff_one_iff_deriv.mpr ⟨fun t=> (hy t).differentiableAt,?_⟩; rw [funext (fun i=> (hy i).deriv)]; exact continuous_tsum (fun j=>((show Continuous (B j) from (show Differentiable ℝ (B j) from fun _=>(hv ..).differentiableAt).continuous).mul (continuous_const (y:= L j)))) (p.mul_right _) hV⟩
 refine ⟨hQ.contDiffAt.of_le (by norm_num),?_, ?_,?_⟩
 · change W 0=A₀; exact tsum_congr (fun j=>(factor_sale (Q j) (F j)|>.turn i).post)
 · change deriv W 0=A₁ i; rw [show A₁ i= _ from (ContinuousLinearMap.apply ℝ ℂ i).map_tsum hvD,(hr 0).deriv]; apply tsum_congr; intro j; exact (hb j 0).deriv.symm.trans (factor_sale (Q j) (F j)|>.turn i).fone -- tune rhs
 change deriv (deriv W) 0=A₂ i i; rw [he, funext (fun t=>(hr t).deriv), (hy 0).deriv]; apply tsum_congr; intro j; have he:= (factor_sale (Q j) (F j)|>.turn i).gOne; change deriv (deriv (H j)) 0= Qp j i i at he; rw [funext (fun t=>(hb j t).deriv), (hv j 0).deriv] at he; exact he
end
end Lenten
end YM.CF.TableF
end
