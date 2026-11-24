import YM.CF.Mew.Pot
import YM.CF.Ione.Lean
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function NormedSpace Filter Metric Finset MeasureTheory
open Skye Scree Jet Vow Lattice Wilson RG Forge Cube Fock Tulip Scroll Spire Peaks Pastry Lat SU
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable{n:Side}{P: BudgetPoint}{I J:Type}[Fintype I][DecidableEq I]
local notation "Sh"=> Scree.Hub n
abbrev HA(P:BudgetPoint)(X:Scree.Hub n):Kine n P:=⟨Unit,fun _=>{V|pingS P.threshold X.val.2 V},fun _=>ping_o,fun _=>Finset.univ , X.val.1⟩ -- change
variable (G:Key I→ RegBudget n){h:ℝ}(hb:0<h)(W:Scree.Hub n→ J→ℝ)(t:∀ i j,0 ≤ W i j)(u:∀ i,∃ j,0 < W i j)(V:J→ℝ)
structure ForgeB (F: RegBudget n)(W:Scree.Hub n→J→ℝ)(P:BudgetPoint)(h:ℝ)(V:J→ℝ) : Prop where
 bit:∃ v:Scree.Hub n→ℝ,(∀ i,PressB P i (F i) h (v i)) ∧ ∀ j, ∑ i,W i j*v i ≤ V j
local notation "Q_" x=> (fun j: Sh × Finset (Dwell n) => HA x j.1)
variable (p:∀ i∈hill I, ForgeB (G i) W P h V)(w:∀ i:Scree.Hub n,∀ j,River (fun z:Key I=> G z i j))
lemma churn_Q {a:Side}(U: Pane a):gyrate Finset.univ U=increment U:= by funext i; change increment _ _=_; rw [show wakeB Finset.univ i=i from funext fun x=>by rw [Forge.steadyB,if_pos (mem_univ _)]]
local notation "TU" x:max K:max => tariff P x h K
include hb t u p w
lemma onset_t (l: List I): ForgeB (fun i j=>tipI (fun z=>G z i j) l) W P h V:=by
 let Y:= Q_ P
 let F(i: Sh × Finset (Dwell n))(z:Key I)(_:(Y i).Var)(x:Pane n):= crumb (G z i.1 x).val i.2
 let W'(i:Sh × Finset (Dwell n))(j:J):= W i.1 j*(TU i.1.val.1 i.2); have hx(i j):0<Scree.tariff (n:=n) P i h j:=by unfold Scree.tariff; positivity
 have he(z)(p':z∈hill I): Shady Y W' V (fun i=> F i z):=by
    obtain ⟨v,q,s⟩:= (p z p').bit; choose b B ht hP using fun i=> (q i).worth
    refine ⟨⟨fun j=> b j.1 j.2,fun i=>B _ _,fun i j V u=>?_,fun j=>?_⟩⟩
    · exact (show Signs P i.1.val.1 ((fun i'=>crumb (G z i.1 i').val i.2) ∘ Forge.gyrate Finset.univ V) (b i.1 i.2) from by rw [churn_Q]; exact ht _ _ u _)
    unfold W'; simp_rw [Fintype.sum_prod_type,mul_assoc,←mul_sum]; exact le_trans (sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hP i) (t ..)) (s j)
 obtain ⟨K,c,v,d⟩:= (shade_l Y W' (fun i j=>mul_nonneg (t ..) (hx _ _).le) (fun i=>by obtain ⟨j,hj⟩:=u i.1; exact ⟨j,mul_pos hj (hx _ _)⟩) V F he (fun i _ U _=> sc_V (w i.1 _) (chipV i.2)) l 0 roots).pay
 let G'(i:Sh)(U:Pane n):=tipI (fun z=>G z i U) l; let E(i:Sh)(V:Pane n):Key I→Cipher n:=fun z=>G z i V
 have hp(i hi j):= (p i hi).bit.choose_spec.1 j
 refine ⟨⟨fun i=>∑ k,tariff P i.val.1 h k*K (i,k),fun i=>⟨fun U V h=>(lace_C l (show Set.EqOn (E i U) (E i V) (hill I) from fun x hx=> (hp x hx i).term U V h) roots),fun V=> grainS _ _ _ (w i V) (fun _ t=>(hp _ t _).fitted V), pot_m _ (w i) (fun j p=>(hp _ p _).measureV) l 0 roots,fun U T=>?_ , (fun k=>K (i,k)), (fun k=>c (i,k)), ?_ ,le_rfl⟩,fun j=>?_ ⟩⟩
 · let X:= hueV (tradew n T)
   have ht:Set.EqOn (E i (Lattice.gauge T U)) (X ∘ (E i U)) (hill I):= fun x hx=> (hp _ hx i).gaugeV U T
   exact (lace_C _ ht roots).trans (sim_H (w i U) X l roots)
 · intro U p' k; change Signs P i.val.1 _ (K (i,k)); simp_rw [←leg_chip _ l k (w _ _)]; have ht:v=v:=rfl; have hd: Signs P i.val.1 (fun z=> tipI (fun w=> F (i,k) w () (Forge.gyrate Finset.univ U z)) l) (K (i,k)):=v (i,k) () U p'; rw [churn_Q] at hd; exact hd
 have hv:=d j; unfold W' at hv; rw [Fintype.sum_prod_type] at hv; simp_rw [mul_assoc,←mul_sum] at hv; exact hv
end YM.CF.Mew
