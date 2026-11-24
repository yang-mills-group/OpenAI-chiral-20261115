import YM.CF.Prism.Rock
import YM.CF.Matter.Mass
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
variable {n:Side}
open Scree
variable {B:RG.BudgetPoint}{X:Hub n}{h c:ℝ}{F:InkD n} (p: PressB B X F h c)
open PhysicalNext.JointLoad MultiNext.SignedSource AnalyticBridge.VerifiedReset Heir RG
set_option quotPrecheck false
local notation "o"=> X.val.1
local notation "Ω"=> X.val.2
abbrev meter(z:SU.Slot × SU.Slot)(b:Bool):= ‖fderiv ℝ (aull b z.1 z.2) 0‖
def coalT := (1:ℝ)+ ∑ i:SU.Slot×SU.Slot,(meter i true+meter i false)
lemma coalL :1 ≤ coalT:=le_add_of_nonneg_right (sum_nonneg fun i _=> add_nonneg (norm_nonneg _) (norm_nonneg _))
lemma payM (b:Bool)(i j:SU.Slot): ‖fderiv ℝ (aull b i j) 0‖ ≤ coalT:=by
 let f(k:SU.Slot × SU.Slot):=meter k true+meter k false; refine le_trans (b:= f (i,j)) ?_ ((single_le_sum (f:=f) (fun j _=> add_nonneg (norm_nonneg _) (norm_nonneg _)) (mem_univ _)).trans (le_add_of_nonneg_left zero_le_one)); cases b; exact le_add_of_nonneg_left (norm_nonneg _); exact le_add_of_nonneg_right (norm_nonneg _)
set_option linter.unusedSimpArgs false in
lemma hus(b:Bool)(u:SU.Slot)(i:SU.Slot) : ‖aull b u i 0‖ ≤ 1:=by cases b <;> by_cases h:u=i <;> simp [aull,gemT, Matrix.one_apply,h,- matter_matrix,cc_apply, show (1:UNI SU.Slot).val=(1:Op _) from rfl] -- tune
variable (i l:SU.Slot)(x y:Rock n) (k:Finset (Dwell n)→ℝ)
local notation "Q"=>crack k x y
abbrev tale (x:ℝ):=x*(B.threshold*(1+(Heir.breadth B Ω:ℝ))^B.power)
def fence (s:ℝ) := coalT*((Heir.breadth B Ω:ℝ)*tale (B:=B) (X:=X) s)
-- all X
variable (hk: ∀ i,0 ≤ k i)(ht:∀ U, BedP B U F X k)
local notation "R"=> Heir.breadth B Ω
include p hk ht
lemma tagT (s:ℝ)(v:tangD n)(he:Lyre.Sized s v B o)(h:Mom.screen Ω v∈Mom.Maps o Ω 1)(e:Axis)(hw:Nonwrapping Ω o)(hn:4 ≤ (More n).val)(hx:node x.1∈Ω)(hy:node y.1∈Ω): ‖fderiv ℝ (crib F x y i l ∘ increment 1) 0 (lap e v)‖ ≤ (Fintype.card SU.Slot:ℝ)*((Fintype.card SU.Slot:ℝ)*(2*fence (B:=B) (X:=X) s*Q)):=by
 obtain ⟨w,HH,hW⟩:=singleM s v he h e; let Z(t:ℝ):=increment 1 (t • lap e v); let L(a:Rock n): group.Color:=(-AnalyticBridge.VerifiedReset.coord o (node a.1) e) • w
 have ht'(t:ℝ)(a:Rock n): wip o e w t (node a.1)=group.lieExp (t • L a):=by unfold wip rollH L; rw [smul_smul,mul_neg,neg_mul]; -- tune
 let M:=crib F x y i l; let W(i j:SU.Slot):=crib F x y i j 1; have H : M ∘ Z=fun t:ℝ=>∑ d:SU.Slot,∑ j:SU.Slot,aull true i j (t • L x)*W j d*aull false l d (t • L y):=by
    funext t; unfold M crib Z; dsimp only [Function.comp_apply]; rw [p.term _ _ (formM v e w t hw hn HH),forge p,ht',ht', Matrix.mul_apply]; simp only [Matrix.mul_apply,Finset.sum_mul]; rfl
 let Ξ (b:Bool)(i j:SU.Slot)(u:Rock n):= fderiv ℝ (aull b i j) 0 (L u); have hp(b)(i j)(u):HasDerivAt (fun t:ℝ=> aull b i j (t • L u)) (Ξ b i j u) 0:=Push.side _ ((curr ..).differentiable (by simp) _) _
 let A(j):=aull true i j ((0:ℝ) • L x); let Y(d):=aull false l d ((0:ℝ) • L y); let D(d j:SU.Slot):= Ξ true i j x * W j d * Y d + (A j * W j d)* Ξ false l d y
 have he' : HasDerivAt (M ∘ Z) (∑ d:SU.Slot,∑ j:SU.Slot,D d j) 0:=by rw [H]; exact HasDerivAt.fun_sum fun d _=> HasDerivAt.fun_sum fun j _=> ((hp true i j x).mul_const _).mul (hp false l d y) -- tune lemma
 have he i l:= sent 1 k x y (ht 1) (ping_f B Ω) hk i l
 have ho': B.order≠0:=Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num) B.order_ge); have hw: DifferentiableAt ℝ (M ∘ increment 1) 0:=(he i l).paid.differentiableAt (by simp [ho'])
 rw [(Push.side _ hw (lap e v)).unique he']; let E0:=fence (B:=B) (X:=X) s
 have hx1(u:Rock n)(h:node u.1 ∈ Ω)(b:Bool)(i j:SU.Slot): ‖Ξ b i j u‖ ≤ E0 :=by
    apply ((fderiv ℝ _ _).le_opNorm _).trans; refine mul_le_mul (payM ..) ?_ (norm_nonneg _) (zero_le_one.trans coalL); unfold L; rw [norm_smul,Real.norm_eq_abs,abs_neg]; refine mul_le_mul ((small_coord ..).trans ?_) hW (norm_nonneg _) (by positivity); exact_mod_cast Heir.close_enough X.property (Finset.mem_union_left _ h)
 have hk'(i j):‖W i j‖ ≤ Q:=by simpa only [Function.comp_apply,Work.G07.at_zero_increment] using sig0 (he i j)
 have hQ:0≤Q:= (he i l).grade; have hp:0 ≤ E0:= (norm_nonneg _).trans (hx1 x hx true i i)
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> (Fintype.card SU.Slot:ℝ)*(2*E0*Q)) (fun d _=>?_)).trans (by simp [E0])); refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> 2*E0*Q) (fun j _=>?_)).trans (by simp [E0]))
 have ha:‖A j‖≤1:=by rw [show A j=_ from ?_]; exact hus true i j; unfold A; rw [zero_smul]
 have hb:‖Y d‖≤1:=by simpa only [Y,zero_smul] using hus false l d
 unfold D; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,norm_mul,norm_mul]; calc
    _ ≤ (E0*Q)*1+(1*Q)*E0:= by have ht:=hx1 x hx true i j; have hu:=hx1 y hy false l d; have hh:=hk' j d; gcongr
    _ = _:=by ring
lemma yarn(s:ℝ)(v:tangD n)(he:Lyre.Sized s v B o)(h:Mom.screen Ω v∈Mom.Maps o Ω 1)(hw:Nonwrapping Ω o)(hn:4 ≤ (More n).val)(hx:node x.1∈Ω)(hy:node y.1∈Ω): ‖fderiv ℝ (crib F x y i l ∘ increment 1) 0 v‖ ≤ (Fintype.card Axis:ℝ)*((Fintype.card SU.Slot:ℝ)*((Fintype.card SU.Slot:ℝ)*(2*fence (B:=B) (X:=X) s*Q))):=by
 have hh:=tagT p i l x y k hk ht s v he h; nth_rw 1 [←laP v,map_sum]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=>hh i hw hn hx hy)).trans (by simp))
end YM.CF.Prism
