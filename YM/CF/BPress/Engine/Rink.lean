import YM.CF.BPress.Engine.Actor
/-! Exact conditional outer complex exponential (with second shared, not integrated over choices). `γ₂` charges all-or-nothing clamped Force (actual `fuel_full` version). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Engine
open Function Filter NormedSpace MeasureTheory Finset Complex Lattice Branch Ledger Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Spin.Stride Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story
open Spark Cube Lat SU Spin.Paint Skye Girt Scree Tulip Tenant Pf.RealBook
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}
@[ext]
structure Shot(N:Side) where
 field : Orbit N
 f : Force N→ℂ
 j : Site N→ℂ
 inserts : Support N -- Desired pz mask for Lily.Vases
 stampX : Paint (More N) -- Desired K
structure Shot.inBudget (p:Shot N)(g:ℝ): Prop where
 st : ∀ i, ‖p.f i‖ ≤1
 sv : ∀ i,‖p.j i‖≤g
 sx : MatPlan p.stampX
variable (P:Form N D) [TopologicalSpace D] (G:Actor N D) (W:Pledge){F:GramM N}
variable {μ g ε r q h:ℝ} {T:Till P F} (x:D) (A:Shot N)
local notation "𝓞"=> Support (More N)
namespace Till
variable {P}
abbrev Memo (T: Till P F): Heat N→ℝ:= Spark.stamp (U:=T.gaze) (T:=T.line) g -- g implicit parameter
-- charges
abbrev fires(_T:Till P F)(u:ℂ):Heat N→ℂ:= issue_spin F A.field u A.f (G.KG x) A.stampX A.j A.inserts -- T dummy param
local notation "S_"=> Saga P F.p.B
abbrev PutLog (T:Till P F)(u:ℂ) :Support (More N)→ℂ := report (Saga P F.p.B) (T.e x) (T.fires G x A u) -- syntax dot
abbrev PutBill (T: Till P F)(g:ℝ):= taxes (Saga P F.p.B) T.γ (Memo T (g:=g))
abbrev Estimate (F:GramM N)(u:ℂ)(B:Pane N)(t:Support (More N)):= Ledger.lump (storyE F.p.B) (Vesper.digit (uB F B u)) t
abbrev rateE(T : Till P F):= Ledger.lump (storyE (N:=N) F.p.B) (fun i=>T.line i ∅)
abbrev logGas(T: Till P F)(u:ℂ)(t:Support (More N)):= T.PutLog G x A u t + Estimate F u A.field.1 t
def currencyGas (T: Till P F)(g:ℝ)(t:Support (More N)):= PutBill T g t+rateE T t
-- boiler
lemma Fires (T:Till P F)(u:ℂ)(h:‖u‖≤1){h_:ℝ}(V:Store P G W F h_ ε r g q μ T)(p:A.inBudget g) (i): ‖T.fires G x A u i‖ ≤ Memo T (g:=g) i:= stamp_le F A.field V.rit V.ent h _ p.st _ _ (V.prices x) p.sx _ p.sv _ i
end Till
open Till
variable {P G W} (V:Store P G W F h ε r g q μ T) (t:Support (More N))
namespace Store
include V
lemma ZScore : Cash (fun i=> (Saga P F.p.B).base i) (fun i=> ahead (Saga P F.p.B) ((Memo T (g:=g)) i) i (StarAmt W)) (δPort F.p.B) (highP (StarAmt W) g F.p.B q):= abroad P F.p.B V.right V.fg V.Tclock.he
lemma Zbudget (x:D)(U:Heat N→ℂ)(p:∀ i,‖U i‖ ≤Memo T (g:=g) i) : table (Saga P F.p.B) (T.e x) U=Complex.exp (∑ i:Support (More N),report (Saga P F.p.B) (T.e x) U i)∧ (∀ t:Support (More N), ‖report (Saga P F.p.B) (T.e x) U t‖≤ T.PutBill g t)∧ Cash id (PutBill T g) μ (logArc (W.rate/2) (highP (StarAmt W) g F.p.B q))∧∀ i:Support (More N),T.PutBill g i≠0→ Grove (Grid.field 4 (More N)) i:= issue (Saga _ _) (Memo T (g:=g)) T.γ V.Tclock.upl (by rw [add_halves]; exact V.pfo.weight) (ZScore V) U _ (fun i=> (V.pfo.help i).bounded x) p -- defeq Elimination
-- Why need inhabited x for cash.W/ use ZBudget? theorem `B_PfC` forces U etc, p0 easily zero but requires x if using T.e. all domains later use x inhabit (zero background). Could choose arbitrarily or edge all zero. remove assumption.
lemma empty_stamp (i:Heat N): ‖(0:ℂ)‖≤ (Memo T (g:=g)) i:=by rw [norm_zero]; rcases i with (i|(i|i)); exact mul_nonneg V.Tclock.he (Real.exp_pos _).le; exact V.right.bill ..; exact V.fg.bill ..
lemma Pbudget : Cash id (PutBill T g) μ (logArc (W.rate/2) (highP (StarAmt W) g F.p.B q)) ∧∀ i:Support (More N),PutBill T g i≠0→Grove (Grid.field 4 (More N)) i:= (issue (Saga _ F.p.B) (Memo T (g:=g)) T.γ V.Tclock.upl (show Enorm _ _ _ _ from (by rw [add_halves]; exact V.pfo.weight)) (V.ZScore) (fun _=>0) (fun _=>0) (fun i=>(show ‖(0:ℂ)‖=0 from by simp).le.trans (V.pfo.weight.f i)) (V.empty_stamp)).2.2
lemma EB : Cash id (rateE T) μ (aPort F.p.B (2*q)):= (Cash.lump (storyE F.p.B) (fun i=>T.line i ∅) (V.right.bill_empty) (hasSum_fintype _).summable).chill (V.Tclock.slow _)
lemma currencyPays: Cash id (currencyGas T g) μ (Perk.price W g q F.p.B):= V.Pbudget.1.plus V.EB
lemma currencyOn : currencyGas T g t≠0→ Grove (Grid.field 4 (More N)) t:=by
 by_contra! e; refine e.1 (show currencyGas T g t=0 from ?_); rw [currencyGas, show T.PutBill g t= 0 from by_contra (fun f=> e.2 ((V.Pbudget.2 t) f)),zero_add]; unfold rateE Ledger.lump; rw [tsum_fintype,sum_eq_zero]; intro i _; rw [if_neg (show t≠storyE F.p.B i from fun h=>e.2 (h.symm ▸ dorm_hit _ _ ⟨_,post0_ok ..⟩))]
variable {A} (u:ℂ) (h':‖u‖≤1)(x:D)
include h'
lemma estimateE (v: Pane N): ‖Estimate F u v t‖ ≤ rateE T t:= Ledger.lump_bound (storyE F.p.B) _ (Vesper.digit (uB F v u)) (hasSum_fintype _).summable (fun i=> regEmpty F V.rit h' v i) _
lemma Gas_bill (p:A.inBudget g): ‖T.logGas G x A u t‖ ≤ T.currencyGas g t:= (norm_add_le ..).trans (add_le_add ((V.Zbudget x (T.fires G x A u) (Fires G W x A T u h' V p)).2.1 t) (V.estimateE t u h' _)) -- order
local notation "L_"=>Op (Single N)
lemma lift_log (p:A.inBudget g)(ω: Phys N) (t:Pf.Top (mood (G.A x) (G.M x)) ω): wickO F A.field u A.f (G.KG x) A.stampX (G.A x) A.j A.inserts ω (G.seat x)=Complex.exp (∑ t: Support (More N), T.logGas G x A u t) :=by
 have pv:= V.Zbudget x (T.fires G x A u) (Fires G W x A T u h' V p); let e:= (V.key x).drum; have hp:= V.pfo; have he := shape_pays (C:= coupling (G.KG x)) (M:=G.A x) (A:= mood (G.A x) (G.M x)) (E:=TheoryP P) (T.e x) e (V.key x).proj t (hp.price x)
 unfold logGas; rw [sum_add_distrib,phaseO F _ u _ (G.KG x) A.stampX (G.A x) A.j A.inserts _ _ ω V.prom (V.prices x) _ (born_st ..) he]; change _ * ((Saga P F.p.B).table _ (T.fires G x A u))=_; rw [pv.1,Complex.exp_add,mul_comm]; apply congrArg; unfold Estimate; rw [lump_sum (storyE _) _ (hasSum_fintype _).summable,tsum_fintype]; -- tune `_` binder
end Store
end YM.CF.BPress.Engine
