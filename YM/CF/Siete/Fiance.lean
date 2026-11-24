/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Siete.Museum
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Clinic
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open MultiNext.SignedSource Lyre Banjo Analysis Pressure
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n m:Side}{k p j:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{E D F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup D][NormedSpace ℝ D]{C ε r u Q:ℝ}
def Guide(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](B:E→Prop)(x:E)(f:E→F)(n:ℕ)(C:ℝ):Prop:= ContDiffAt ℝ (n:ℕ∞ω) f x ∧ ∀ i ≤ n,∀ v:Fin i→E,(∀ j,B (v j))→‖iteratedFDeriv ℝ i f x v‖≤C
lemma Guide.size {B:E→Prop}{x:E}{f:E→F}(h:Guide E B x f k C):‖f x‖≤ C:=by simpa only [iteratedFDeriv_zero_apply] using h.2 0 (Nat.zero_le _) (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
lemma Guide.rise {B:E→Prop}{x:E}{f:E→F}(h:Guide E B x f k C)(p:C ≤ u): Guide E B x f k u :=⟨h.1,fun i b x u=>(h.2 i b x u).trans p⟩
lemma Guide.duo {B:E→Prop}{x:E}{f:E→F}{g:E→D}(h:Guide E B x f k C)(p:Guide E B x g k C): Guide E B x (fun i=>(f i,g i)) k C:=by
 refine ⟨h.1.prodMk p.1,fun i l z b=>?_⟩; rw [iteratedFDeriv_prodMk h.1 p.1 (Nat.cast_le.mpr l)]; exact max_le (h.2 i l z b) (p.2 i l z b)
lemma Guide.minus {B:E→Prop}{x:E}{f g:E→F}(h:Guide E B x f k C)(p:Guide E B x g k u):Guide E B x (f-g) k (C+u):=by
 refine ⟨h.1.sub p.1,fun i hi m hp=>?_⟩; rw [iteratedFDeriv_sub_apply (h.1.of_le (Nat.cast_le.mpr hi)) (p.1.of_le (Nat.cast_le.mpr hi))]; exact (norm_sub_le ..).trans (add_le_add (h.2 i hi m hp) (p.2 i hi m hp))
-- new weight incoming single unit for ALL derivative orders. denominator chosen polynomial (giving tail)
lemma handle {f:E→F}{L:E→L[ℝ] F}{y:D}{g:D→E}{b:D→Prop}(hf:Portrait f L k ε r Q)(p:ε≤u)(hp:0≤Q)(hu:u ≤ 1)(ht:u ≤ r)(q:Guide D b y g k u)(hn: 2 ≤ k) : Guide D b y ((f-⇑L)∘ g) k (clinicFee k Q*u^2) :=by
 let f':= f -(⇑L); have hv:=q.size; have hy:0≤u:= (norm_nonneg _).trans hv; have hh:=hf.uniform _ (hv.trans ht); have hx:ContDiffAt ℝ (k:ℕ∞ω) f' (g y):=hh.smooth.sub L.contDiff.contDiffAt
 refine ⟨hx.comp _ q.1,fun i hi v h=>?_⟩
 by_cases t:i=0
 · subst i; rw [iteratedFDeriv_zero_apply]; refine (hf.zeroth_charge hn hv ht).trans ?_; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p hp) hy,mul_le_mul_of_nonneg_right (clinicFee_le k hp) (sq_nonneg u)]
 change ‖iteratedFDeriv ℝ i (f' ∘ g) y v‖ ≤ _; rw [iteratedFDeriv_comp hx q.1 (Nat.cast_le.mpr hi),FormalMultilinearSeries.taylorComp,_root_.sum_apply]
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>2*Q*u^2) (fun iA pA=>?_ )).trans ?_)
 ·  
   let w(j:Fin iA.length):=iteratedFDeriv ℝ (iA.partSize j) g y (v ∘ iA.emb j)
   have hw:(∏ i,‖w i‖)≤ u^iA.length:= le_trans (prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> q.2 _ ((iA.partSize_le j).trans hi) _ fun _=> h _)) (le_of_eq (by simp))
   let M:= iteratedFDeriv ℝ iA.length f' (g y); change ‖M w‖≤ _
   have hpos:=iA.length_pos (Nat.pos_of_ne_zero t)
   by_cases hz:iA.length=1
   · have hg: ‖M‖≤2*Q*u:=by unfold M; rw [hz, norm_iteratedFDeriv_one]; unfold f'; rw [fderiv_sub (hh.smooth.differentiableAt (by exact_mod_cast (show k≠0 by omega))) L.differentiableAt,L.fderiv]; refine (hf.first_charge hn (hv.trans ht)).trans ?_; nlinarith only [mul_le_mul_of_nonneg_left (add_le_add p hv) hp]
     refine (M.le_opNorm _).trans ((mul_le_mul hg (hw.trans (le_of_eq ?_)) (prod_nonneg fun i _=>norm_nonneg _) (by positivity)).trans_eq (show 2*Q*u*u=2*Q*u^2 by ring)); rw [hz,pow_one]
   have hg: ‖M‖ ≤ 2*Q:=by unfold M f'; rw [iteratedFDeriv_sub_apply (hh.smooth.of_le (Nat.cast_le.mpr (iA.length_le.trans hi))) L.contDiff.contDiffAt, sterile L _ (by omega), sub_zero]; exact (hh.pay _ (iA.length_le.trans hi)).trans (by linarith)
   exact (M.le_opNorm _).trans (mul_le_mul hg (hw.trans (pow_le_pow_of_le_one hy hu (by omega))) (prod_nonneg fun i _=> norm_nonneg _) (by positivity))
 rw [sum_const,card_univ,nsmul_eq_mul]; unfold clinicFee; simp only [mul_assoc]; exact mul_le_mul_of_nonneg_right ((Planned.AtomRegular.card_le_patterns hi).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
open Next Next.Fluctuations Precision Tree
variable {S:StepData (More m) (More n)}{T:Tube group S}{Y:Tree.Forest S.ratio}{x t t₁:ℝ}{J:S.Choices}
-- promises even shifted
lemma baton (M B':ℝ){B:BudgetPoint}{f:E→ tangD m}{g:E→tangD n}{y:E}{b:E→Prop}(h:Guide E b y f k u)(p:Guide E b y g k t₁)(hh:Tour T Y x J k r C)(ht:temp x ≤ u)(hu:u≤1)(hf:u≤r)(kC:0≤C) (m':Matins T Y B.power B' M)(ha:0≤B')(hy:t₁ ≤u)(hr:2≤k) (A:ℝ)(pA:0 ≤ A)(hp:clinicFee k C*u^2+t₁ ≤ A*(S.patch.L.val:ℝ)⁻¹^3*B.threshold)
 (X:Support (More n))(o:Seat n)(hx:∀ i≤k,∀ v:Fin i→E,(∀ j,b (v j))→ Limb B.power (S.ratio.parent o) (iteratedFDeriv ℝ i f y v) (B'*B.threshold)) :
 let Z:=display T Y x J true ∘ fun i=>(f i,g i)
 ContDiffAt ℝ (k:ℕ∞ω) Z y ∧ ∀ i≤k,∀ v:Fin i→E,(∀ j,b (v j))→ Promise 2 (M+A) ((S.patch.L.val:ℝ)⁻¹) B o X (iteratedFDeriv ℝ i Z y v):=by
 intro Z; let V(i):=(f i,g i); have hd: Guide E b y V k u:=h.duo (p.rise hy); let F:=display T Y x J true; have hz:=hh.costs true; let Φ:=mainStroke T Y true
 have he: ContDiffAt ℝ (k:ℕ∞ω) Z y:= ((hz.uniform (V y) (hd.size.trans hf)).smooth).comp (f:=V) _ hd.1
 refine ⟨he,fun i hi v hv=>?_⟩
 let w:=iteratedFDeriv ℝ i V y v; let D:=iteratedFDeriv ℝ i Z y v
 let x':=Heir.route T (iteratedFDeriv ℝ i f y v); let Y':=iteratedFDeriv ℝ i g y v
 have hx': ‖D-Φ w‖≤clinicFee k C *u^2:=by
    have hj:=(handle hz ht kC hu hf hd hr).2 i hi v hv; rw [show (display T Y x J true-⇑(mainStroke T Y true)) ∘ V= Z-(Φ∘ V) from rfl, iteratedFDeriv_sub_apply (he.of_le (Nat.cast_le.mpr hi)) ((Φ.contDiff.contDiffAt.comp y hd.1).of_le (Nat.cast_le.mpr hi)), Φ.iteratedFDeriv_comp_left hd.1 (Nat.cast_le.mpr hi)] at hj; exact hj
 have hl: Φ w=x'+Y':=by unfold w V; rw [iteratedFDeriv_prodMk h.1 p.1 (Nat.cast_le.mpr hi)]; rfl
 have h':‖D-x'‖ ≤clinicFee k C*u^2+t₁:=by rw [hl] at hx'; exact (norm_sub_le_norm_sub_add_norm_sub D (x'+Y') x').trans (add_le_add hx' (by rw [add_sub_cancel_left]; exact p.2 i hi v hv))
 change Promise _ _ _ _ _ _ D; rw [show D=x'+(D-x') by abel]; refine coal (m'.taper B X o _ rfl (hx i hi v hv)) ⟨by positivity,fun i=>?_⟩ pA (by positivity); have ht:0<B.threshold:= B.threshold_pos
 change _ ≤ _; calc
   _ ≤ clinicFee k C*u^2+t₁ := (norm_le_pi_norm (D-x') i).trans h'
   _ ≤ _ := hp.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right ht.le (spine_one ..)) (by positivity))
end YM.CF.Siete
