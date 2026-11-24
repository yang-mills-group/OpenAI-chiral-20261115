import YM.CF.Siete.Bullet
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q v x:ℝ}{G:Gauge}{L:Side}
lemma portrait_zoom (n l:ℕ)(J:ℝ)(hD:0<J)(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(hn:2≤n)(hl:l≤18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1))(q:Chi)(Q:ℝ)(pQ:0<Q)(s:ℕ): ∃ z:ℝ,0<z∧∀ᶠ x in atTop, 0<gateX G P.L l (s*n+s*n) x z ∧ ∀{c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x →∀ (A:Stores S)(F:Forest S.ratio)(V:Config G c),sizedP G P K S T F→ A.flags=RG.flags (temp x) V → ∀ (k:S.Choices)(τ:ℝ), y G P.L x/2 ≤ τ → ∀ (I:Type) [Fintype I] [DecidableEq I] {X:Support f}{Y:Support c}(M:Museum F x A X Y I)(β':BudgetPoint),β'.power=s → β'.threshold=temp x →∀ o: Site c,(∀ i:I,separation o (incF M i) ≤ 7*(1+radiusB x)) →∀ B:Config G f,∀ Z:LogArray G (Active A x F),(∀ i∈coZ M,‖Z i‖≤gateX G P.L l (s*n+s*n) x z) →∀ g:Site c→G.El, Guide _ (β'.dirBound o) 0 (atoms T M τ k q (J*fiery G x P.L) l B Z g ∘ increment V) n (Q*fiery G x P.L / feeI x l (s*n)):=by -- typeclass Decidable explicit not inferred fix [ ]
 obtain ⟨C,h,H⟩:=turnsX n l J hD K P p hn hl W q
 obtain ⟨u,v,hv,A⟩:=shipped K P p n l hn hl W
 obtain ⟨X,hX⟩:= count G; obtain hy:= hX.1
 obtain ⟨z,hz,Y⟩:=tune_up (C*X) _ G P.L (half_pos pQ) (by positivity) l (s*n+s*n)
 refine ⟨z,hz,?_⟩
 filter_upwards [H,A,Y,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,spiritu (K:=X*u) (n:=s*n+s*n) (l:=l) (v:=v) (half_pos pQ) G P.L] with x H U ⟨hZ,Tn⟩ hi hv'
 refine ⟨hZ,fun S T hp A' F V he hf k τ hv I _ _ XX YY M B e v' o hx B' Z ht g=>?_⟩ -- tune
 obtain ⟨b,Hx,-⟩:= U.2.2.2 S T A' F hp he V hf k q (J*fiery G x P.L) (Folio.leaf A' F x B')
 have hy := ((H S T hp A' F V he hf k).jumps (Folio.leaf A' F x B')); rw [show S.patch=P from hp.got] at hy -- tune dependent
 have hh:= atomsG T M τ k q (J*fiery G x P.L) l B' Z g o _ B v' hx V b hi (flyP T M τ k q _ l B' Z V b hi Hx hy.2.2.2.2.1 h.le ht hZ.le) hX
 apply hh.rise; rw [e]; have hm:=Tn τ hv; generalize gateX G P.L l (s*n+s*n) x z=t at *
 change X*((u*_+|coupling τ| * (t*C))*feeI x l (s*n))≤Q*fiery G x P.L / feeI x l (s*n)
 have ht :0<feeI x l (s*n):=by unfold feeI; positivity
 rw [le_div_iff₀ ht]; unfold feeI at *; simp_rw [pow_add] at hm hv'; linarith only [hv',hm]
open Heir Skye Scree Cube
private lemma roomI{B: BudgetPoint}{X:Support L}(p:B.B≤2*radiusB x)(h:1000≤radiusB x)(t:ℕ): 2+(breadth B X:ℝ)≤ feeI x t 1*(1+(coverNumber B.B X:ℝ)):=by
 let d : ℝ:=coverNumber B.B X; let r : ℝ:= radiusB x
 have hh: (B.B:ℝ) ≤2*r:=by unfold r; exact_mod_cast p
 have hv:(breadth B X:ℝ)≤d*(8*r+2)+4*r+8:=by unfold breadth; push_cast; change d*_+_+8≤_; gcongr _*?_+?_+8 <;> linarith
 have ht: (0:ℝ) ≤t:=Nat.cast_nonneg _; have he:1000 ≤ r:=by unfold r; exact_mod_cast h
 have hd:0≤ d:=Nat.cast_nonneg _; unfold feeI; push_cast; rw [pow_one]; change _ ≤ (1+(7*(1+r)+(t+50:ℝ)*r))*(1+d); nlinarith only [he,mul_nonneg ht (show 0≤r by positivity),mul_nonneg hd (show 0 ≤ (t:ℝ)*r by positivity), mul_le_mul_of_nonneg_right he hd, hv,hd]
lemma foal {P B:BudgetPoint}{X:Support L}(p:B.B≤2*radiusB x)(h:1000≤radiusB x)(t:ℕ): heft n X P B ≤ feeI x t (P.power*n)*(1+(coverNumber B.B X:ℝ))^(P.power*n) :=by
 unfold heft feeI; rw [←pow_mul,←mul_pow (n:= P.power*n)] -- tune given synt
 exact pow_le_pow_left₀ (by positivity) (by simpa only [feeI,pow_one] using roomI (X:=X) p h t) _

lemma fee_looms (C q:ℝ)(G:Gauge)(L:Side)(n l s:ℕ): ∀ᶠ x in atTop,∀ P:BudgetPoint,P.power=s→P.threshold=temp x→ C*(loom P (Heir.reach x) q)^2 * feeI x l (s*n) ≤ fiery G x L:=by
 let K : ℝ := |C| * |q|^2
 have h:∀ᶠ x:ℝ in atTop, K*(temp x)^2*feeI x l (s*n+s*2) ≤ 1*fiery G x L:=by
    filter_upwards [spiritu (K:=K) (l:=l) (n:=s*n+s*2) (v:=1) zero_lt_one G L, Work.E01.radiusB_tendsto.eventually_ge_atTop 1000] with x hx hβ; apply le_trans _ hx; have ht:=Work.E04.temp_nonneg x; have hr: (1:ℝ) ≤ radiusB x:=Nat.one_le_cast.mpr (le_trans (by norm_num) hβ); unfold tideF blockF; gcongr _ * ?_ ^ 2 * _; rw [one_mul]; exact le_mul_of_one_le_left ht (one_le_pow₀ hr)
 filter_upwards [h,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000] with x hx hr P he ht; unfold loom; rw [he,ht]; rw [one_mul] at hx
 apply le_trans _ hx; have hh:0≤temp x:= (ht ▸ P.threshold_pos.le)
 have hy : 1+(Heir.reach x:ℝ) ≤ feeI x l 1:=by unfold Heir.reach feeI; push_cast; have hv:(0:ℝ)≤ l:=Nat.cast_nonneg _; nlinarith only [hv,mul_nonneg hv (Nat.cast_nonneg (α:=ℝ) (radiusB x)), show (1000:ℝ) ≤ radiusB x by exact_mod_cast hr, pow_one ((1:ℝ)+(7*(1+(radiusB x:ℝ))+(l+50:ℝ)*(radiusB x:ℝ)))] -- tune
 calc
   _ ≤ |C| *(|q| *temp x*(feeI x l 1)^s)^2 *feeI x l (s*n):=by
      rw [mul_pow (q*_),mul_pow q,←sq_abs q,mul_pow,mul_pow |q|]; gcongr; try first| exact le_abs_self C| unfold feeI; positivity -- tune
   _ = _ := by unfold K feeI; rw [pow_one,pow_add,pow_mul _ _ 2]; ring
end YM.CF.Siete
