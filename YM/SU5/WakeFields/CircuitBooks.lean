import YM.SU5.WakeFields.Cyclorama
import YM.CF.Mew.Char
import YM.CF.Mew.Firth

/-! # Simultaneous Key-circuit ledgers. Extend `Mew.onset_t, insight_t`. -/
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
variable{n:Side}{P: BudgetPoint}{I J:Type}[Fintype I][LinearOrder I]
local notation "Sh"=> Scree.Hub n
variable (G:Key I→ RegBudget n){h:ℝ}(hb:0<h)(W:Scree.Hub n→ J→ℝ)(t:∀ i j,0 ≤ W i j)(u:∀ i,∃ j,0 < W i j)(V:J→ℝ)
local notation "Q_" x=> (fun j: Sh × Finset (Dwell n) => HA x j.1)
variable (p:∀ i∈hill I, ForgeB (G i) W P h V)(w:∀ i:Scree.Hub n,∀ j,River (fun z:Key I=> G z i j))
local notation "TU" x:max K:max => tariff P x h K
include hb t u p w
lemma earnChar :
    ∃ v:Scree.Hub n→ℝ,(∀ (L:Finset I) i,PressB P i (fun j=> gemI (fun z=>G z i j) L) h (v i)) ∧ ∀ j, ∑ i,W i j * v i ≤ V j:=by
 let Y:= Q_ P
 let F(i: Sh × Finset (Dwell n))(z:Key I)(_:(Y i).Var)(x:Pane n):= crumb (G z i.1 x).val i.2
 let W'(i:Sh × Finset (Dwell n))(j:J):= W i.1 j*(TU i.1.val.1 i.2); have hx(i j):0<Scree.tariff (n:=n) P i h j:=by unfold Scree.tariff; positivity
 have he(z)(p':z∈hill I): Shady Y W' V (fun i=> F i z):=by
    obtain ⟨v,q,s⟩:= (p z p').bit; choose b B ht hP using fun i=> (q i).worth
    refine ⟨⟨fun j=> b j.1 j.2,fun i=>B _ _,fun i j V u=>?_,fun j=>?_⟩⟩
    · exact (show Signs P i.1.val.1 ((fun i'=>crumb (G z i.1 i').val i.2) ∘ Forge.gyrate Finset.univ V) (b i.1 i.2) from by rw [churn_Q]; exact ht _ _ u _)
    unfold W'; simp_rw [Fintype.sum_prod_type,mul_assoc,←mul_sum]; exact le_trans (sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hP i) (t ..)) (s j)
 obtain ⟨K,c,v,d⟩:= charterTip Y W' (fun i j=>mul_nonneg (t ..) (hx _ _).le) (fun i=>by obtain ⟨j,hj⟩:=u i.1; exact ⟨j,mul_pos hj (hx _ _)⟩) V F he (fun i _ U=> sc_V (w i.1 _) (chipV i.2))
 refine ⟨fun i=>∑ k,tariff P i.val.1 h k*K (i,k), fun L i=>?_, fun j=>?_⟩; swap
 · have hv:=d j; unfold W' at hv; rw [Fintype.sum_prod_type] at hv; simp_rw [mul_assoc,←mul_sum] at hv; exact hv
 let l:= Cue I L
 let G'(i:Sh)(U:Pane n):=tipI (fun z=>G z i U) l; let E(i:Sh)(V:Pane n):Key I→Cipher n:=fun z=>G z i V
 have hp(i hi j):= (p i hi).bit.choose_spec.1 j
 refine ⟨fun U V h=>(lace_C l (show Set.EqOn (E i U) (E i V) (hill I) from fun x hx=> (hp x hx i).term U V h) roots),fun V=> grainS _ _ _ (w i V) (fun _ t=>(hp _ t _).fitted V), pot_m _ (w i) (fun j p=>(hp _ p _).measureV) l 0 roots,fun U T=>?_ , (fun k=>K (i,k)), (fun k=>c (i,k)), ?_ ,le_rfl⟩
 · let X:= hueV (tradew n T)
   have ht:Set.EqOn (E i (Lattice.gauge T U)) (X ∘ (E i U)) (hill I):= fun x hx=> (hp _ hx i).gaugeV U T
   exact (lace_C _ ht roots).trans (sim_H (w i U) X l roots)
 · intro U p' k; unfold gemI; change Signs P i.val.1 _ (K (i,k)); simp_rw [←leg_chip _ (Cue I L) k (w _ _)]; have ht:v=v:=rfl; have hd: Signs P i.val.1 (fun z=> tipI (fun w=> F (i,k) w () (Forge.gyrate Finset.univ U z)) l) (K (i,k)):=v L (i,k) () U p'; rw [churn_Q] at hd; exact hd
end YM.CF.Mew
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace YM.CF.Mew
open Function NormedSpace Filter Metric Finset MeasureTheory
open Skye Scree Jet Vow Lattice Wilson RG Forge Cube Fock Tulip Scroll Spire Peaks Pastry Lat SU
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable{n:Side}{P: BudgetPoint}{I J:Type}[Fintype I][LinearOrder I]
local notation "Sh"=> Scree.Force n
variable (G:Key I→ ForceBudget n){h:ℝ}(hb:0<h)(W:Scree.Force n→ J→ℝ)(t:∀ i j,0 ≤ W i j)(u:∀ i,∃ j,0 < W i j)(V:J→ℝ)
local notation "Q_" x=> (fun j: Sh × Finset (Dwell n) => HP x j.1)
variable (p:∀ i∈hill I, SanB (G i) W P h V)(w:∀ i:Scree.Force n,∀ j,River (fun z:Key I=> G z i j))
local notation "TU" x:max K:max => tariff P x h K
include hb t u p w
lemma earnFirth :
    ∃ v:Scree.Force n→ℝ,(∀ (L:Finset I) i,ForceB P i (fun j=> gemI (fun z=>G z i j) L) h (v i)) ∧ ∀ j, ∑ i,W i j * v i ≤ V j:=by
 let Y:= Q_ P
 let F(i: Sh × Finset (Dwell n))(z:Key I)(V:(Y i).Var)(x:Pane n):= crumb (G z i.1 (x,V)).val i.2
 let W'(i:Sh × Finset (Dwell n))(j:J):= W i.1 j*(TU i.1.val.1.val.1 i.2); have hx(i j):0<Scree.tariff (n:=n) P i h j:=by unfold Scree.tariff; positivity
 have he(z)(p':z∈hill I): Shady Y W' V (fun i=> F i z):=by
    obtain ⟨v,q,s⟩:= (p z p').bit; choose b B ht hP using fun i=> (q i).costP
    refine ⟨⟨fun j=> b j.1 j.2,fun i=>B _ _,fun i j V u=>?_,fun j=>?_⟩⟩
    · exact (show Signs P i.1.val.1.val.1 ((fun i'=>crumb (G z i.1 (i',j)).val i.2) ∘ Forge.gyrate (Rill.unrest i.1.val.2 P.B) V) (b i.1 i.2) from by have he:= ht i.1 (V,j) u i.2; simp_rw [Rill.padP] at he; exact he)
    unfold W'; simp_rw [Fintype.sum_prod_type,mul_assoc,←mul_sum]; exact le_trans (sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hP i) (t ..)) (s j)
 obtain ⟨K,c,v,d⟩:= charterTip Y W' (fun i j=>mul_nonneg (t ..) (hx _ _).le) (fun i=>by obtain ⟨j,hj⟩:=u i.1; exact ⟨j,mul_pos hj (hx _ _)⟩) V F he (fun i u' U=> sc_V (w i.1 (U,u')) (chipV i.2))
 refine ⟨fun i=>∑ k,tariff P i.val.1.val.1 h k*K (i,k), fun L i=>?_, fun j=>?_⟩; swap
 · have hv:=d j; unfold W' at hv; rw [Fintype.sum_prod_type] at hv; simp_rw [mul_assoc,←mul_sum] at hv; exact hv
 let l:= Cue I L
 let G'(i:Sh)(U:Orbit n):=tipI (fun z=>G z i U) l; let E(i:Sh)(V:Orbit n):Key I→Cipher n:=fun z=>G z i V
 have hp(i hi j):= (p i hi).bit.choose_spec.1 j
 refine ⟨fun U V τ ν a b=>(lace_C l (show Set.EqOn (E i (U,τ)) (E i (V,ν)) (hill I) from fun x hx=> (hp x hx i).values U V τ ν a b) roots),fun V=> grainS _ _ _ (w i V) (fun _ t=>(hp _ t _).fitted V), ?_ ,pot_m _ (w i) (fun j p=>(hp _ p _).measureV) l 0 roots, ?_, fun U τ T=>?_ , (fun k=>K (i,k)), (fun k=>c (i,k)), ?_ ,le_rfl⟩
 · intro h; funext v; let f(x:Key I):=G x i v; exact (lace_C l (f:=f) (g:=fun _=>0) (fun z hz=> congrFun ((hp z hz i).flagsV h) v) roots).trans (tip_0 l)
 · intro V t; by_contra he; apply t; exact (lace_C l (f:=fun z=>G z i V) (g:=fun _=>0) (fun z hz=> by contrapose! he; exact (hp z hz i).protect V he) roots).trans (tip_0 l)
 · let X:= hueV (tradew n T)
   have ht:Set.EqOn (E i (Lattice.gauge T U,threadG T τ)) (X ∘ (E i (U,τ))) (hill I):= fun x hx=> (hp _ hx i).gaugeV U τ T
   exact (lace_C _ ht roots).trans (sim_H (w i (U,τ)) X l roots)
 · intro U p' k; unfold gemI; change Signs P i.val.1.val.1 _ (K (i,k)); simp_rw [←leg_chip _ (Cue I L) k (w _ _)]; have ht:v=v:=rfl; have hd: Signs P i.val.1.val.1 (fun z=> tipI (fun w=> F (i,k) w U.2 (Forge.gyrate (Rill.unrest i.val.2 P.B) U.1 z)) l) (K (i,k)):=v L (i,k) U.2 U.1 p'; simp_rw [Rill.padP]; exact hd
end YM.CF.Mew
#print axioms YM.CF.Mew.earnChar
#print axioms YM.CF.Mew.earnFirth
