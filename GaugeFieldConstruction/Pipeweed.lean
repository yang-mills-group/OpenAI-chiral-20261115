import GaugeFieldConstruction.Pilote
/- choose root derivative receipt Z_j on actual Λ with cap budget. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 130000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d t r u c h a b h0:ℝ}{j k:ℕ}{m B n:Side}
namespace MastTin
open Shield Echo Ledger Jet
local notation "GS"=> SU.group
local notation "Λ"=> CSide m B
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable (o:Seat n) {X:Hubber n}{p:BudgetPoint}
section
open Push.Mark Brace
variable (q:Clip)(o:Seat (CSide m B)) (l:Axis)
variable {Y:Side}{ho:Odd Y.val}{Z:Pricing j Y ho (Thread j)}(P: Grasp Z B d) (t':0<d)(H:Pearl P)(V:Stamped j Y ho Z)
abbrev reserveC(q:Clip):=(marks_budget q).choose
include H V
lemma G_Born(w:1≤j)(k:ℕ):∃ D D' a:ℝ,0≤ reserveC q∧0≤ D∧0≤D'∧0<a∧ ∀ {m:Side}(R:Loom (CSide m B)) {t u:ℝ},Roof (CSide m B) u t k R→ P.roundZ≤(CSide m B).val→1<(More (CSide m B)).val→∀(o:Seat (CSide m B))(e:Axis)(f:PlaqAxes)(p:BudgetPoint)(x h:ℝ), p.threshold≤u→ t<d→0<x→p.order≤6→ p.power≤3→ 1 ≤ x*p.threshold^2→ Envelope (hard q p x P (m:=m)) → ∃ F:Torches (CSide m B), Inscribe p o h a F (reserveC q) ((D+h^2*D')/(x*p.threshold)) ∧ F.1=isolate none (Gval o f p q x e) ∧∀ X:marker0 (CSide m B),untax (m:=m) (B:=B) o e X→ UnEcho (Ion F) X (hard q p x P)=0:=by
 obtain ⟨D,h,h',D0⟩:=(marks_budget q).choose_spec; let C:=reserveC q; obtain ⟨K,g,Hm⟩:= Chaff.larder 7; obtain ⟨a,C0,C1,K0,k0,k1,G⟩:= whole_29 P H V w K
 let R:= ρperk a k; let L:ℝ:= (Fintype.card inkMus:ℝ)*ρZ R*2^6*D; have hR:0<R:=perk_pos K0 _; have hl:0≤L:=by unfold L ρZ; positivity
 refine ⟨L*C1,L*C0,R,h,mul_nonneg hl k1,mul_nonneg hl k0,hR,@fun m A t u pA pn n o e f p x h hp hx hX W pP b HH=>?_⟩
 have hv(i:inkMus): ‖at_E o e (musk i)‖ ≤1:=by
    have hv: ‖musk i‖=1:= LeadK.orthonormal.1 i; rw [← pupq]; apply le_trans ((Pudge o e).le_opNorm _); rw [hv,mul_one]; apply Shield.puff
 have he(i:inkMus): HookP (o,e) (at_E o e (musk i)):=fun _ g=> Pi.single_eq_of_ne g _
 let T (i:inkMus):= G (m:=m) pn _ (hv i); let t0:Ids (CSide m B):=Classical.arbitrary _
 have hz(i:inkMus):= reactive (h:=h) o e i pA hx t0 Hm g hp W K0 ((T i).2 (o,e) (he i)).1 ((T i).2 (o,e) (he i)).2 (T i).1
 choose Pq P0 S using hz; let E(i):=GDecr o p e f x i; let F(i):=BridV o (E i) (Pq i); let K(i):=totalE o (Pq i); obtain ⟨K,tK⟩:= D0 o e f p x hX b W pP -- shadow
 let Z:Torches (CSide m B):= (isolate none (Gval o f p q x e), ∑ i,F i); let τ:=p.threshold; have ht:0<τ:=p.threshold_pos
 refine ⟨Z,⟨?_,?_⟩,rfl,fun X h=>?_⟩
 · exact track_p (moorage none True.intro _ K) (show (1:ℝ)*C≤_ from (one_mul _).le)
 · refine trace_p (trace_sum (p:=p) (h:=h) (a:=R) univ F _ fun i _=> BrideH o (E i) _ (P0 i) (tK i) hR.le) le_rfl ?_; rw [sum_const,card_univ,nsmul_eq_mul];
   let y:= C1+h^2*C0; let n:ℝ:= Fintype.card inkMus; change n*(ρZ R*(2^p.order*(D/(x*τ))*y))≤_; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ)^p.order≤2^6 from pow_le_pow_right₀ (by norm_num) W) (div_nonneg h' (mul_pos hX ht).le)) (show 0≤ y from (by unfold y; positivity))) (Real.exp_pos _).le) (Nat.cast_nonneg _)); apply le_of_eq; unfold L y τ ρZ; ring
 rw [show Ion Z=pasteM e f p q x o (fun i=>totalE o (Pq i)) from ?_]; exact unitM_u e f p q x P o _ X h (fun i=> receipt_env o _ (P0 i)) HH n S
 funext i; rw [grands_L e f p q x o _ hX.ne']; change marketD (isolate none (Gval o f p q x e)) i+totalE o (∑ a,F a) i=_; rw [report_S, Finset.sum_apply, publish]; simp_rw [show ∀ j:inkMus,totalE o (F j) i = E j i • totalE o (Pq j) i from fun j=>report_H ..]; unfold E GDecr; simp_rw [neg_smul,mul_smul,sum_neg_distrib]; rw [sub_eq_add_neg]; rfl -- tune
#print axioms G_Born
end
end MastTin
end YM.CF.XGarden
end
