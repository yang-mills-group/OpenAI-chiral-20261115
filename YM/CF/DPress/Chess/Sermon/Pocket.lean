import YM.CF.DPress.Chess.Flow.Cost
import YM.CF.DPress.Chess.Flow.Suit
import YM.CF.BPress.Envelope
import YM.CF.Girt.Lane
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
-- all-args payloads, in particular legible everywhere for the thinning & factoring
abbrev Stage (n:Side):= Pane n× Pane n -- true & Lift repair
abbrev HT (n:Side):= Stage n→ ReOp n
abbrev Ticket (K:Ratio n m):= Forest (ratio K)× Pane n
abbrev Tour (K:Ratio n m):= Stage m × (Pane n × Ticket K)
abbrev focus {u:Side}(D A:Support (More u)):Setoid (Stage u):= joins (Ties SU.group D) (Ties SU.group A)
abbrev νticket [Nonempty (Forest (ratio K))](P:Loom n)(x:Pane n): Measure (Ticket K):= (Bough.St (ratio K)).prod (Robe.τ P x)
abbrev Fold (K:Ratio n m)(R:Type*):= Tour K→ R
variable {V X:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][SecondCountableTopology V][MeasurableSpace V][BorelSpace V][Nonempty (Forest (ratio K))][MeasurableSpace X]
abbrev unc_N (D:Fold K V)(x:Stage m)(z:Pane n)(w:Ticket K):= D (x,(z,w))
noncomputable def sum_T (P:Loom n)(A:Fold K V) (x:Stage m)(z:Pane n):= ∫ t, unc_N A x z t ∂νticket P z
lemma tight (p:Measurable P)(x:Pane n): IsProbabilityMeasure (νticket (K:=K) P x):= letI:IsProbabilityMeasure (Robe.τ P x) := Robe.prob p x; inferInstance
lemma shelfK {D:Fold K V}(b:Envelope D)(x:Stage m)(z:Pane n):Envelope (unc_N D x z):=Env.along b (g:=fun t=>(x,(z,t))) (measurable_prodMk_left.comp measurable_prodMk_left)
lemma scoreH {A:Fold K V}(m0:Measurable P)(b: Envelope A): Envelope (uncurry (sum_T P A)):=by
 let f : (Stage m × Pane n)× Ticket K→ V := fun x=> A (x.1.1,(x.1.2,x.2)); let g (x: Forest (ratio K)× Ids n) (y:Stage m× Pane n):= f (y,(x.1,P (y.2,x.2))); have hf: Envelope (uncurry g):= Env.along b (g:=fun x:(Forest (ratio K)×Ids n) × (Stage m×Pane n)=>(x.2.1,(x.2.2,(x.1.1,P (x.2.2,x.1.2))))) ((measurable_fst.comp measurable_snd).prodMk ((measurable_snd.comp measurable_snd).prodMk ((measurable_fst.comp measurable_fst).prodMk (m0.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))))) ; have ht:= Env.marginal hf ((Bough.St _).prod (depot n));
 let F:=fun x:Stage m × Pane n=> ∫ y, g y x ∂(Bough.St _).prod (depot n); rw [show uncurry (sum_T P A)= F from ?_]; exact ht
 funext s; refine Eq.symm (expect (Prod.map id (fun y=>P (s.2,y))) ((MeasurePreserving.id (St (ratio K))).prod (Robe.lever m0 s.2)) (fun x:Ticket K=>f (s,x)) ?_); exact (shelfK b s.1 s.2).meas
noncomputable def guide (S:StepData (More n) (More m))(β:ℝ) (P:Loom n)(A:Fold K V) (x:Stage m):= ∫ z,sum_T P A x z∂ Ξ SU.group S β x.1
lemma housing {A:Fold K V}(p:S.patch.Branches S.kernel SU.group)(l: Measurable P)(b:Envelope A)(β:ℝ) : Envelope (guide S β P A):=by
 let J x:= Ξ SU.group S β x; let V₁(X:Stage m× Pane n):= S.density (G:=SU.group) β X.1.1 X.2; let H:=uncurry (sum_T P A); let w:=fun s:Stage m=>∫ x,V₁ (s,x) • H (s,x)∂ prior SU.group (More n); rw [show guide S β P A=w from funext (fun i=>Transit.card p ..)]; apply BPress.Law.marginalP (f:=fun i=> V₁ i • H i); exact Env.scale (Env.along (den_env (S.isKernel p β)) (g:=fun x:Stage m × Pane n=>(x.1.1,x.2)) (by fun_prop)) (scoreH l b)
end YM.CF.DPress.Chess.Sermon
