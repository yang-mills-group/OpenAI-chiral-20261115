import YM.CF.Siete.Reach
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q v x:ℝ}{G:Gauge}{L:Side}
lemma portraitZ (n l:ℕ)(J:ℝ)(hD:0<J)(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(hn:2≤n)(hl:l≤18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1))(q:Chi)(Q:ℝ)(pQ:0<Q)(s:ℕ): ∃ z:ℝ,0<z∧∀ᶠ x in atTop, 0<gateX G P.L l (s*n) x z ∧ ∀{c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x →∀ (A:Stores S)(F:Forest S.ratio)(V:Config G c),sizedP G P K S T F→ A.flags=RG.flags (temp x) V → ∀ (k:S.Choices)(τ:ℝ), y G P.L x/2 ≤ τ → ∀ (I:Type) [Fintype I] [DecidableEq I] {X:Support f}{Y:Support c}(M:Museum F x A X Y I)(β':BudgetPoint),β'.power=s → β'.threshold=temp x →∀ o: Site c,(∀ i:I,separation o (incF M i) ≤ 7*(1+radiusB x)) →∀ B:Config G f,∀ Z:LogArray G (Active A x F),(∀ i∈coZ M,‖Z i‖≤gateX G P.L l (s*n) x z) →∀ g:Site c→G.El, Guide _ (β'.dirBound o) 0 (atoms T M τ k q (J*fiery G x P.L) l B Z g ∘ increment V) n (Q*fiery G x P.L):=by -- typeclass Decidable explicit not inferred fix [ ]
 obtain ⟨C,h,H⟩:=turnsX n l J hD K P p hn hl W q
 obtain ⟨u,v,hv,A⟩:=shipped K P p n l hn hl W
 obtain ⟨X,hX⟩:= count G; obtain hy:= hX.1
 obtain ⟨z,hz,Y⟩:=tune_up (C*X) _ G P.L (half_pos pQ) (by positivity) l (s*n)
 refine ⟨z,hz,?_⟩
 filter_upwards [H,A,Y,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,spiritu (K:=X*u) (n:=s*n) (l:=l) (v:=v) (half_pos pQ) G P.L] with x H U ⟨hZ,Tn⟩ hi hv'
 refine ⟨hZ,fun S T hp A' F V he hf k τ hv I _ _ XX YY M B e v' o hx B' Z ht g=>?_⟩ -- tune
 obtain ⟨b,Hx,-⟩:= U.2.2.2 S T A' F hp he V hf k q (J*fiery G x P.L) (Folio.leaf A' F x B')
 have hy := ((H S T hp A' F V he hf k).jumps (Folio.leaf A' F x B')); rw [show S.patch=P from hp.got] at hy -- tune dependent
 have hh:= atomsG T M τ k q (J*fiery G x P.L) l B' Z g o _ B v' hx V b hi (flyP T M τ k q _ l B' Z V b hi Hx hy.2.2.2.2.1 h.le ht hZ.le) hX
 apply hh.rise; rw [e]; have hm:=Tn τ hv; generalize gateX G P.L l (s*n) x z=t at *
 change X*((u*_+|coupling τ| * (t*C))*feeI x l (s*n))≤Q*fiery G x P.L
 linarith only [hv',hm]
end YM.CF.Siete
