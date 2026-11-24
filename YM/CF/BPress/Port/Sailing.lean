import YM.CF.BPress.Port.Toll
/-!
Direct exact Offers integral for arbitrary Bochner f (complex in use). Returns ∫ relative to another probability, with explicit bias, which must be used with B.Rpoint. No sector sum inside bias; f actual at bodyBase. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(κ y:ℝ)(A:BEnd X)(F:Fare X)(S:Seal X.Hcols)
variable {E: Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable (b: Offers X→E)
def callx (x: Offers X): E:= if S=pick X κ y x then b x else 0
abbrev swingV (v:Quarters X):=taxG X J y F S v.1 • callx X κ y S b (bodyBase X y F S v)
abbrev tollD (v:Quarters X):= detM X (F S) • swingV X J κ y F S b v
lemma tax_meas (u:LocalRatio J): Measurable (taxG X J y F S):= Finset.measurable_fun_prod _ fun i _=> measurable_const.mul (Measurable.exp (((log_meas B.D J y u).comp ((measurable_pi_apply i).comp (wjson_meas _))).add (show Measurable (hardHit X i) from by unfold hardHit; fun_prop))) -- tune
variable {X A F J y κ}{T:Sheet.Atlas}{P:Weave.Budget}(q: Afford J T P B.D κ y)(r:LocalRatio J)(e:Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(f:∀ S,Whole X S (F S) 1)(v:Integrable b (Rains X))(h:StronglyMeasurable b)
include q r e f v h
lemma plants : Integrable (callx X κ y S b) (Rains X):=by rw [show callx X κ y S b={x| S=pick X κ y x}.indicator b from ?_]; exact v.indicator (pick_meas X κ y S); ext x; by_cases h:S=pick X κ y x <;> simp [callx,h,Set.indicator]
lemma voyage : Integrable (tollD X J κ y F S b) (knell X y) ∧ (∫ x,callx X κ y S b x∂Rains X)=∫ v, tollD X J κ y F S b v∂knell X y :=by
 let T:= callx X κ y S b; let d:=detM X (F S); let M:= packRead (F:=F) y S T; let g:=fun x:Quarters X=> coast X J y S (wheel (F S) x) • M x; let f':= swingV X J κ y F S b; let p:∀ x, T x≠0→ S=pick X κ y x:= fun i x=> not_not.mp (fun v=> x (if_neg v)); obtain ⟨u,H⟩:= rollMove J κ y S e T r q (plants S b q r e f v h) (by convert! h.indicator (pick_meas X κ y S) using 1; ext x; by_cases h:S=pick X κ y x <;> simp [T,callx,h,Set.indicator]) p; have hx:g= fun x => coastV X y x • f' x:=by
   ext1 x; obtain ⟨a,c⟩:= x; obtain ⟨a,rfl⟩:= (offer X).surjective a; let v:=(offer X a,c); by_cases z: aware X κ y F S v; · change coast X J y S _ • T (bodyBase X y F S _) = _; rw [q.fares S r e (f S) a c z]; exact (mul_smul ..) -- tune order
   have hz:T (bodyBase X y F S v)=0:= if_neg fun b=> z b.symm; change _ • T (bodyBase X y F S v)=_ • (_ • T (bodyBase X y F S v)); rw [hz]; simp
 have hp:Integrable f' (knell X y):= by rw [read_volts]; apply (duty_int (coastV X y) (volts_meas X y) (volts_pos X y) (harbour X) _).2; exact (hx ▸ (show Integrable g _ from u)) -- tune
 refine ⟨hp.smul d,(show _ = d • ∫ x,g x∂harbour X from H).trans ?_⟩; rw [show (∫ v,tollD X J κ y F S b v∂knell X y)= d • ∫ v,f' v ∂knell X y from integral_smul _ _, read_volts,hx,duty_eq _ (volts_meas X y) (volts_pos X y)]
variable [CompleteSpace E]
-- Integral input over all, signed output, tag still external unchanged. no need Θ assumption
lemma seaTotals : (∫ x,b x∂Rains X) = ∑ S, ∫ v,tollD X J κ y F S b v∂knell X y:=by
 calc (∫ x,b x∂Rains X)=∫ x,(∑ S:Seal X.Hcols, callx X κ y S b x)∂Rains X:= integral_congr_ae (Eventually.of_forall fun x=>by simp [callx])
      _ = ∑ S:Seal X.Hcols,∫ x,callx X κ y S b x∂Rains X := integral_finsetSum _ (fun S _=> plants S b q r e f v h)
      _ = _:= sum_congr rfl fun S _=> (voyage S b q r e f v h).2
end YM.CF.BPress.Port
#print axioms YM.CF.BPress.Port.seaTotals
#print axioms YM.CF.BPress.Port.stamp_point
