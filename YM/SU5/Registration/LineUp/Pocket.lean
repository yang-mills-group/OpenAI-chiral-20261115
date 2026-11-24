/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.LineUp.Forms
import YM.Work.C07
/-!
  # Move in finite label portfolios. (No Lie identities proved here.)
  adapts Work/C09 moving_eval. Not restricted now to its spins/table.
  Helps with arity-boost density estimates. Works for ragged finite costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Boundary Mink Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Algebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

namespace GearDeriv
local notation "MM"=> MultilinearMap ℂ (fun _ : Fin n=>V) ℂ
/-- differentiating even when the *costs* move; need derivative of each moving scalar from
 the functional, don't assert it in any cap-operator topology. the derivative u' of the scalar price T(t)(u) at fixed u as given. -/
theorem purchase (T:ℝ→MultilinearMap ℂ (fun _:Fin n=>V) ℂ) (T':MultilinearMap ℂ (fun _:Fin n=>V) ℂ) (f:ℝ→Fin n→V)(e:Fin n→V) (t:∀ v, HasDerivAt (fun x:ℝ=> T x v) (T' v) 0) (h:∀ i, GearDeriv (fun x=>f x i) (e i)): HasDerivAt (fun t:ℝ=> T t (f t)) ((∑ i,T 0 (update (f 0) i (e i)))+T' (f 0)) 0:=by
 classical
 choose k g c c' p hk he using h; let c₀(i:Fin n):= fun j:Fin (k i)=> c i j 0; let v:=f 0; let R:=(i:Fin n)→ Fin (k i); let A := (fun (P:R)(i:Fin n)=>g i (P i)); let Y := (fun (d:(i:Fin n)→ Fin (k i)→ℂ)(P:R)=> ∏ i,d i (P i)); have hh (S:MM) (d:(i:Fin n)→ Fin (k i)→ℂ) (v:Fin n→V)(h:∀ i,v i=∑ j, d i j • g i j) : S v=∑ P:R, Y d P*S (A P):=by
   conv_lhs=> rw [funext h]
   rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun P _=> S.map_smul_univ _ _
 have hcp (i:Fin n): v i= ∑ j, c₀ i j • g i j:= (hk i).self_of_nhds
 let E(P:R):= fun x:ℝ=> Y (fun i j=> c i j x) P
 have hp(P:R): HasDerivAt (E P) (∑ i, Y (update c₀ i (c' i)) P) 0:=by
   have hg (i:Fin n) : Y (update c₀ i (c' i)) P = (∏ j ∈ Finset.univ.erase i, c₀ j (P j)) • c' i (P i):=by
     unfold Y; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]; simp only [update_self,smul_eq_mul]; congr 1; exact Finset.prod_congr rfl fun k hk=>by rw [update_of_ne (Finset.mem_erase.mp hk).1]
   simp_rw [hg]; exact HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _=> p i (P i))
 have ht(i:Fin n): T 0 (update v i (e i))=∑ P:R, Y (update c₀ i (c' i)) P * T 0 (A P):=by
   refine hh _ _ _ (fun j=>?_); by_cases h:j=i
   · subst j; simp only [update_self]; exact he i -- tune subst
   simp only [update_of_ne h]; exact hcp j
 let ψ(P:R):= fun t:ℝ=> E P t * T t (A P); change HasDerivAt _ ((∑ i,T 0 (update v i (e i)))+T' v) (0:ℝ); simp_rw [ht,hh T' c₀ v hcp]; rw [Finset.sum_comm,← Finset.sum_add_distrib] -- g?
 have H : ∀ᶠ x in 𝓝 0,T x (f x)=∑ P:R,ψ P x:= (eventually_all.mpr hk).mono fun x he=> hh (T x) _ _ he
 apply HasDerivAt.congr_of_eventuallyEq ?_ H
 refine HasDerivAt.fun_sum fun P _=>?_
 simpa only [ψ, E, c₀, Finset.sum_mul] using! (hp P).fun_mul (t (A P))
/-- use the simple case -/
theorem charge (T:MultilinearMap ℂ (fun _:Fin n=>V) ℂ)(v:ℝ→Fin n→V)(e:Fin n→V)(t:∀ i,GearDeriv (fun x=>v x i) (e i)) : HasDerivAt (fun x=> T (v x)) (∑ i,T (update (v 0) i (e i))) 0:=by
 simpa using purchase (fun _=>T) 0 v e (fun w=>hasDerivAt_const (0:ℝ) (T w)) t
end GearDeriv
namespace GearContinuity
theorem paid {X:Type*}[TopologicalSpace X] (x:X) (T:X→MultilinearMap ℂ (fun _:Fin n=>V) ℂ)(v:X→Fin n→V)(p:∀ i,GearContinuity (fun w=> v w i) x)(h:∀ v,ContinuousAt (fun t=> T t v) x) : ContinuousAt (fun x=> T x (v x)) x:=by
 choose k g c e he using p; let R:=(i:Fin n)→ Fin (k i); let f(u:X):= ∑ P:R,(∏ i,c i (P i) u)*T u (fun i=>g i (P i)); apply ContinuousAt.congr_of_eventuallyEq (show ContinuousAt f x from (tendsto_finsetSum _ fun P _=> (tendsto_finsetProd _ fun i _=> e i (P i)).mul (h _)))
 refine (eventually_all.mpr he).mono (fun w hw=>?_); change T w (v w)=_; rw [show v w=(fun i=> ∑ j,c i j w • g i j) from funext hw,MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun i _=> (T w).map_smul_univ _ _
end GearContinuity
end YM.SatinWFixed
open YM.SatinWFixed
#print axioms GearContinuity.paid
#print axioms GearDeriv.purchase
#print axioms GearDeriv.charge
