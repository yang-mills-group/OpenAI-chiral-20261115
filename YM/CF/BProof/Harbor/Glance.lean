import YM.CF.BProof.Harbor.Heal
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory ProbabilityTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Skye Regard Vogue Mesh Shore
open Wager
namespace Frost
variable {I E D:Type} [Fintype I][DecidableEq I]
variable {N:Side}{u:ℝ}{r q:ℕ}
variable {F:Orbit N→ Pane N}(Q:Quartz N q u r F)
attribute [local instance] measureVal billVal
def blook (T S:Support (More N))(f:PairD N→D) : Prop:= ∀ X Y:PairD N, Agrees (↑T) X.1 Y.1→ Agrees (↑S) X.2 Y.2→f X=f Y
lemma lookP (T S:Support (More N)){f:PairD N→ D}(p:blook T S f)(U: Pane N): LocalOn S (fun V=>f (U,V)):=fun V W h=>p (U,V) (U,W) (fun _ _ _=>rfl) h
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
include Q
lemma stop_h (T S:Support (More N))(g:halo r S⊆T){f:PairD N→ E}(p:Envelope f)(h:blook T S f): LocalOn (↑T) (heal F f):=by
 intro U V t; change meanS (depot N) (fun t=>(f ∘ Prod.mk U) (F (U,t)))= meanS (depot N) (fun t=>(f ∘ Prod.mk V) (F (V,t))); rw [warmP Q (f ∘ Prod.mk U) (Law.pull p measurable_prodMk_left) U,warmP Q (f ∘ Prod.mk V) (Law.pull p measurable_prodMk_left) V]; apply integral_congr_ae; filter_upwards with k; apply integral_congr_ae; filter_upwards with l; exact h (U,paint Q U k l) _ t (here Q _ _ g (fun z v=>rfl) t l)
end
private lemma ballot (A:Support (More N))(v:Root N)(U:Pane N){i j:Fin q}(h:Matches A (fun x (U:Pane N)=>Function.curry (Q.spice.P i U) x) (fun x (U:Pane N)=>Function.curry (Q.spice.P j U) x)) : Agrees (↑A) (paint Q U v i) (paint Q U v j):=by
 intro e u t; change _* Q.spice.P i _ e *_=_* Q.spice.P j _ e *_; have hx: Q.spice.P i (gauge v U) e= Q.spice.P j (gauge v U) e:=congrFun (congrFun (h u) (gauge v U)) e.2; rw [hx]
abbrev φr (U:Pane N)(f:Pane N→ℂ)(t:Root N):= meanS (paperMeas (Fin q)) fun i=> f (paint Q U t i)
variable {f g:Pane N→ℂ}
lemma φc (p:Envelope f)(U:Pane N): Envelope (φr Q U f):= by haveI:=Q.spice.ne; exact Wager.usualM (fun x:Fin q× Root N=>f (paint Q U x.2 x.1)) (Law.pull (q:=fun x: Fin q× Root N=>paint Q U x.2 x.1) p (measurable_snd.comp (joint_m ..))) _
lemma φregion (T S:Support (More N))(h:halo r S⊆T)(p:LocalOn S f)(U:Pane N):Push.GridApprox.Reads (↑T) (φr Q U f):=fun V W e=>integral_congr_ae (Eventually.of_forall fun i=>p _ _ (here Q _ _ h e (fun _ _ _=>rfl) _))
lemma boat (A B : Support (More N))(p: ∀ i∈A,∀ j∈B,r<separation i j)(u:LocalOn A f)(v:LocalOn B g)(U:Pane N) : φr Q U (f*g)=φr Q U f * φr Q U g:=by
 haveI:=Q.spice.ne; funext t; let F(k:Fin q):=paint Q U t k; obtain ⟨E,h⟩:= Q.spice.gap A B (fun i g j w=>Q.pay.trans_lt (p i g j w)); let μ:= paperMeas (Fin q)
 have ht: MeasurePreserving E (μ.prod μ) (μ.prod μ):=by unfold μ; rw [← Vogue.parcelPair]; exact Vogue.orderMP E
 refine Wager.shake μ (fun x=> f (F x)) (fun x=>g (F x)) E ht (measurable_of_countable _) (measurable_of_countable _) (fun x=>?_); exact congrArg₂ (·*·) (u _ _ (ballot Q A t _ (Regard.fromPen h x).1)) (v _ _ (ballot Q B t _ (Regard.fromPen h x).2.2.1))
include Q
lemma function_FD (A B C D:Support (More N))(pe:Disjoint C D)(a:halo r A⊆ C)(b:halo r B⊆ D)(p:∀ i∈A,∀ j∈B,r < separation i j) (u:LocalOn A f)(v:LocalOn B g)(tf:Envelope f)(tg:Envelope g)(U:Pane N) : meanS (depot N) (fun t=> f (F (U,t))*g (F (U,t)))=meanS (depot N) (fun t=> f (F (U,t))) *meanS (depot N) (fun t=>g (F (U,t))):=by
 haveI:=Q.spice.ne
 change meanS (depot N) (fun t=>(f*g) (F (U,t)))=_;rw [warmP Q (f*g) (Wager.company tf tg) _,warmP Q f tf _,warmP Q g tg _]; change (∫ i,φr Q U _ i∂rootM N)=(∫ i,φr Q U f i∂rootM N)*(∫ i,φr Q U g i∂rootM N); rw [boat _ _ _ p u v]
 have ht:=Push.GridApprox.pi_independent (X:=group.El) (μ:=group.probHaar) (φregion Q C A a u U) (φregion Q D B b v U) (by simpa [Finset.disjoint_left, Set.disjoint_left] using pe) (q:=fun _ _=>(1:ℂ)) (by simp) (fun _=> Girt.rite_c _) (φc Q tf U) (φc Q tg U)
 simp only [prod_const_one,one_mul] at ht; exact ht
lemma matrix_FD (A B C D:Support (More N))(pe:Disjoint C D)(a:halo r A⊆ C)(b:halo r B⊆ D)(p:∀ i∈A,∀ j∈B,r < separation i j){f g:Pane N→ Op I} (u:LocalOn A f)(v:LocalOn B g)(tf:Envelope f)(tg:Envelope g)(U:Pane N): meanS (depot N) (fun t=> f (F (U,t))*g (F (U,t)))=meanS (depot N) (fun t=> f (F (U,t))) *meanS (depot N) (fun t=>g (F (U,t))):=by
 refine factorM (Law.pull (q:=fun t=>F (U,t)) tf (Q.bill.comp measurable_prodMk_left)) (Law.pull (q:=fun t=> F (U,t)) tg (Q.bill.comp measurable_prodMk_left)) ?_; intro i j k; exact function_FD Q A B C D pe a b p (fun i' j' p=> congrArg (penny i k) (u i' j' p)) (fun i' j' p=>congrArg (penny k j) (v i' j' p)) (pane tf _ _) (pane tg _ _) U -- tune ..
end Frost
end YM.CF.BProof.Bide
