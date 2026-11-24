import GaugeFieldConstruction.Faing
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedVariables false
set_option maxHeartbeats 230000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes
variable {K b c d r v e a:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=> CSide m B
open Tenant
variable {q:Stamp m B→ Toll (Single (CSide m B))} {X:Stamp m B→ MSheet m B}{R:Stamp m B}{F G:MSheet m B}
abbrev tallβ(a K:ℝ):=(∑' i:ℕ, Real.exp (-a/2*i)*(quota*((i:ℝ)+1)^4))*K
local notation "Θ"=> helix Λ
lemma spend_P (h:AllM K n e R X q)(p:Ledger a q c)(g:0<a)(o:Seat Λ): hitE (a/2) (fun S=>ledgerV (q S)) o≤ tallβ a c:=by
 let b:= slotK Λ; let s:=sigK Λ; let f(S:Stamp m B)(i j:Model Λ):=q S ((Θ).symm i) ((Θ).symm j)
 have ht:∀ S,Ticket s s S (f S) (fun _=>0):=by
    intro S; refine ⟨fun _ _=>by simp,fun i j=> ⟨h.positive ..,?_,?_,?_, continuous_const⟩⟩
    · intro p; obtain ⟨t,_,y,z⟩:= (h S _ _).2 (show q S _ _≠0 from p); unfold aptK at y z; rw [Equiv.apply_symm_apply] at y z; exact ⟨t,y,z⟩
    · intro x; exact norm_zero.le.trans (h.positive ..)
    intro x y; change ‖(0:ℂ)-0‖≤ _; rw [sub_self,norm_zero]; exact mul_nonneg (h.positive ..) (b.pos ..)
 have he: Ledger a f c:=by refine ⟨p.posP,fun i=>?_,fun i=>?_⟩; exact (Equiv.sum_comp (Θ).symm (fun k=> saleM a q ((Θ).symm i) k)).trans_le (p.rows _); exact (Equiv.sum_comp (Θ).symm (fun k=> saleM a q k ((Θ).symm i))).trans_le (p.cols _)
 have hx:= tall ht he g (ample_slots Λ) (by unfold quota; positivity) o; refine le_trans (le_of_eq ?_) hx; refine congrArg (fun g:Stamp m B→ℝ=> hitE (a/2) g o) (funext (fun (S:Stamp m B)=>?_)) -- tune
 change ledgerV (q _) = ledgerV (f _); unfold f ledgerV; 
 symm; simp_rw [fun i=> (Equiv.sum_comp (Θ).symm (q S i))]; exact Equiv.sum_comp (Θ).symm (fun i=>∑ k,q S i k)
variable(i:V8 (CSide m B)) (T:tangD (CSide m B))(pT:‖T‖ ≤1)
abbrev HookP (i: V8 N)(t:tangD N):Prop:= ∀ j:V8 N,j≠i → t j=0
def coefM (X:MSheet m B)(x:Pantry m B): Op (Single Λ):= deriv (fun y:ℝ=> X (bud T x.1 y,x.2)) 0
private abbrev oval {I:Type}[Fintype I][DecidableEq I] (v w:I):Op I→L[ℝ] ℂ:=(⟨⟨fun x=>x v w,fun _ _=>rfl⟩, fun _ _=>rfl⟩: Op I→ₗ[ℝ]ℂ).toContinuousLinearMap
lemma PayDiff {I:Type}[LinearOrder I][Fintype I] (F:ℝ→Op I) (h:∀ i j,DifferentiableAt ℝ (fun x=> F x i j) 0): DifferentiableAt ℝ F 0:=by
 let f(x:ℝ)(i j:I):= F x i j; let A:(I→I→ℂ) →ₗ[ℝ] Op I:=⟨⟨fun x=>Matrix.of x,fun _ _=>rfl⟩,fun _ _=>rfl⟩
 have h:DifferentiableAt ℝ f 0:= differentiableAt_pi.mpr fun i=> differentiableAt_pi.mpr (h i)
 have he:= A.toContinuousLinearMap.differentiableAt.comp 0 h; exact he
lemma drop_Q {f:SheetT m B}{x:Pantry m B}(p:Ka K n e R f v) (u:x∈ Lobby m B e)(g: HookP i T) (hx: ¬ ends i ⊆ R): coefG T f x=0:=by -- f undeclared!
 let H(t:ℝ):=bud T x.1 t
 have he':Continuous H:= (bud_c T).comp (f:=fun t=> (t,x.1)) (continuous_id.prodMk continuous_const)
 have hf:∀ᶠ t in 𝓝 (0:ℝ),(H t,x.2)∈ Lobby m B e := ((he'.prodMk continuous_const).continuousAt).eventually (lobby_o.mem_nhds (by change (H 0,_)∈ Lobby m B e; unfold H; rw [bud_x,Prod.mk.eta]; exact u))
 unfold coefG; apply HasDerivAt.deriv; apply (hasDerivAt_const (𝕜:=ℝ) 0 (f x)).congr_of_eventuallyEq; filter_upwards [hf] with t v
 refine p.watch (H t,x.2) v x u ?_ (fun _ _=>rfl); intro j a b; change H t j=x.1 j; unfold H bud RG.increment; rw [Pi.smul_apply,g j (by intro e; subst j; apply hx; intro x h; rcases mem_insert.mp h with h|h; exact h ▸ a; exact mem_singleton.mp h ▸ b),smul_zero]; simp -- group lieExp zero
include pT
lemma TicketM.DPath {A:MSheet m B}{p:Toll (Single (CSide m B))}{Q V:Stamp m B}(h:TicketM b 7 e Q V A p)(hv:hud_T 7 c)(p0:c≤b)(x:Pantry m B)(g:x∈ Lobby m B e): HasDerivAt (fun y:ℝ=> A (bud T x.1 y,x.2)) (coefM T A x) 0 ∧ ∀ i j:Single Λ,coefM T A x i j= coefG T (fun z=> A z i j) x:=by
 let G(i:ℝ):=A (bud T x.1 i,x.2); have hp(i j:Single Λ):= Ka.coef_tone T pT hv (h i j).1 g p0; have he:= (PayDiff G (fun i j=> (hp i j).differentiableAt)).hasDerivAt
 exact ⟨he,fun i j=> ((oval i j).hasFDerivAt.comp_hasDerivAt 0 he).unique (hp i j)⟩
-- beware Ticket of coefM only measurable on Lobby. For supports keep equality component.Ticket changing to explicit coeff forming at every x. Key.D.
lemma TicketM.echo (V:Stamp m B) {A: MSheet m B}{p:Toll (Single (CSide m B))} (h:TicketM b 7 e V ∅ A p)(P:hud_T 7 c)(p0:c ≤ b)(ht:lin_T 7*c*K≤ b)(g:HookP i T): ∃ (A':MSheet m B), TicketM K 6 e V (ends i) A' (if ends i ⊆ V then p else 0)∧ ∀ x∈ Lobby m B e, HasDerivAt (fun t=> A (bud T x.1 t,x.2)) (A' x) 0:=by
 let Y(x:Pantry m B): Op (Single Λ):= Matrix.of fun j k=>coefG T (fun z=>A z j k) x
 have ht'(x:Pantry m B)(v:x∈Lobby m B e):HasDerivAt (fun t=> A (bud T x.1 t,x.2)) (Y x) 0:=by
    obtain ⟨p,q⟩:= TicketM.DPath _ pT h P p0 _ v; exact p.congr_deriv (Matrix.ext (fun i j=> q i j))
 by_cases w: ends i ⊆ V
 · rw [if_pos w]; exact ⟨Y,fun i j=>⟨Ka.coef_arr T pT P (h i j).1 p0 ht,fun k=> ⟨((h i j).2 k).1,w,((h i j).2 k).2.2⟩⟩,ht'⟩
 rw [if_neg w]; exact ⟨fun _=>0,fun i j=> ⟨Ka.zero_H,fun k=> (k rfl).elim⟩,fun x v=> (ht' x v).congr_deriv (Matrix.ext fun u l=> drop_Q i T (h u l).1 v g w)⟩
lemma PutM.pair_V (u:PutM b 7 e a d F)(P:hud_T 7 c)(l:c ≤ b): ∀ x∈ Lobby m B e, HasDerivAt (fun t=> F (bud T x.1 t,x.2)) (coefM T F x) 0:=by
 intro x v; obtain ⟨q,A,t,p,w⟩:= u; apply DifferentiableAt.hasDerivAt; let Z(y:ℝ):=(bud T x.1 y, x.2); have he:Continuous Z:= ((bud_c T).comp (f:=fun t=> (t,x.1)) (continuous_id.prodMk continuous_const)).prodMk continuous_const -- tune
 apply DifferentiableAt.congr_of_eventuallyEq ((HasDerivAt.fun_sum (u:=univ) (fun i _=> (TicketM.DPath T pT (t i) P l x v).1)).differentiableAt)
 filter_upwards [he.continuousAt.tendsto.eventually (lobby_o.mem_nhds (show Z 0∈ Lobby m B e from by unfold Z; rw [bud_x]; exact v))] with i p'; exact w _ p'
lemma offshore (h:PutM b 7 e a d F)(P:hud_T 7 c)(l:c≤ b)(t:lin_T 7*c*K ≤ b)(p:HookP i T)(g:0<a): HitM K 6 e (a/2) (tallβ a d) (ends i) (coefM T F):=by
 obtain ⟨q,A,u,s,w⟩:= h
 choose Y L k using fun V=> TicketM.echo i T pT V (u V) P l t p; refine ⟨fun V=> if ends i⊆ V then q V else 0,Y,L,?_,fun x v=> ?_⟩
 · have hx:= spend_P u s g i.1; apply le_trans _ hx
   unfold costM saleM; rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (f:=fun (i:Single Λ) (S: Stamp m B)=>_)] -- tune
   unfold hitE hit0; rw [sum_filter]; apply sum_le_sum; intro j hj; by_cases hy: ends i⊆j
   · simp_rw [if_pos hy]; rw [if_pos (show i.1∈j from hy (by simp [Skye.ends])), ledgerV]; simp_rw [←mul_sum]; rw [sum_comm (f:=fun x y=>q j y x)]
   simp only [if_neg hy,Pi.zero_apply,mul_zero,sum_const_zero]; split; exact mul_nonneg (rent_pos ..).le (sum_nonneg fun i _=> sum_nonneg fun k _=> u.positive j i k); rfl
 · let Z(y:ℝ):=(bud T x.1 y,x.2); have he:Continuous Z:= ((bud_c T).comp (f:=fun t=> (t,x.1)) (continuous_id.prodMk continuous_const)).prodMk continuous_const; apply HasDerivAt.deriv; apply (HasDerivAt.fun_sum (u:=univ) (fun z _=>k z x v)).congr_of_eventuallyEq
   filter_upwards [he.continuousAt.tendsto.eventually (lobby_o.mem_nhds (show Z 0∈ Lobby m B e from by unfold Z; rw [bud_x]; exact v))] with i p'; exact w _ p'
end YM.CF.XGarden
end
