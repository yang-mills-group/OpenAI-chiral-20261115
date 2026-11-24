import YM.SU5.Selected.ProofReader
/-! # Projection arithmetic for turnstile products of Players. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric
open CF.Buffered.Afterglow.Tower MeshClock Germ
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H : Hilbert} {Γ : AddSubgroup ℝ} {I : Type*} [DecidableEq I]
  (P : Alliance I Γ H) (t t' : List I)
local notation "R" x:max => (P.crew x).pi_c
local notation "U" u:max x:max => (P.crew u).play x
lemma empty_raw (u : I) (x : Γ) (h:u∉ t): P.raw t (Function.update 0 u x)=ContinuousLinearMap.id ℂ H.space:=by
 induction t with
 | nil=>rfl
 | cons i t ih=>simp only [List.mem_cons,not_or] at h
                rw [P.raw_step,Function.update_of_ne (Ne.symm h.1),Pi.zero_apply,(P.crew i).play_zero,ih h.2]; rfl
lemma spotlight {u : I} (h:t.Nodup) (p:u∈ t) (x:Γ) : P.raw t (Function.update 0 u x)=U u x := by
 induction t with
 | nil=>contradiction
 | cons i t ih=>
   obtain ⟨a,b⟩:= List.nodup_cons.mp h
   rcases List.mem_cons.mp p with rfl|p
   · rw [P.raw_step,empty_raw P _ _ x a,Function.update_self]; rfl
   rw [P.raw_step,ih b p,Function.update_of_ne (show i ≠ u from fun h=> a (h.symm ▸ p)),Pi.zero_apply,(P.crew i).play_zero]; rfl
lemma raw_spot {u : I} (h:t.Nodup) (p:u∈ t)(x: Γ) (v:I→Γ) :
    P.raw t (Function.update v u x)=(P.raw t (Function.update v u 0)).comp (U u x):=by
 rw [show Function.update v u x=Function.update v u 0+Function.update (0:I→Γ) u x from funext (fun i=>by by_cases hi:i=u <;> simp [Function.update,hi]), P.travelR,spotlight P t h p]
lemma overlay_all (p : t.Perm t') : P.stackS t=P.stackS t' := by
  induction p with
  | nil=>rfl
  | cons x _ ih=>rw [P.shel_step,P.shel_step,ih]
  | swap i j t=>rw [P.shel_step,P.shel_step,P.shel_step,P.shel_step, ← Alliance.just _ _ _, P.floatP j i]; rfl
  | trans _ _ t h=>exact t.trans h
lemma cover_step (u : I) (p:u∈t) : P.stackS t= (P.stackS (t.erase u)).comp (R u):=by
 rw [overlay_all P t (u::t.erase u) (List.perm_cons_erase p), P.shel_step, P.ground _ _ (fun i _ v=> P.floatZ i u v 0)] -- perm orientation
lemma permvest (l t : List I) (p:l.Perm t) (f:I→Γ) : P.raw l f = P.raw t f:=by
 induction p with
 | nil=>rfl
 | cons x _ ih=>rw [P.raw_step,P.raw_step,ih]
 | swap i j l=>rw [P.raw_step,P.raw_step,P.raw_step,P.raw_step,←Alliance.just _ _ _, P.cCom j i]; rfl
 | trans _ _ v t=> rw [v,t]
lemma stack_projection : P.stackS t=(P.aviator t).starProjection:=by
 ext1 x; symm; apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (P.planted _ _)
 intro y p; rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_right, P.symmetricstack,P.grounded t p,sub_self]
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.cover_step
#print axioms YM.SelectionAnalysis.spotlight
