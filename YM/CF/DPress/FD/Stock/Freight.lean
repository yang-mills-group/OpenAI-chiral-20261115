import YM.CF.DPress.FD.Stock.Gears
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory SU Lat Finset Wilson Laurent OrderF BasicIid Spoke Gear
open Cube (More Guard)
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{J:Type}[Fintype J][MeasurableSpace J][MeasurableSingletonClass J]{r d:ℕ}{u t:ℝ}
namespace Star
variable (X:Scout J n u t r) (f:ℕ→ℝ→J) (s:Seed.Stage n)
abbrev Yaw(n:Side):= Seat n→ Sweep n
abbrev yawP(n:Side):Measure (Yaw n) := Measure.pi fun _=> paperMeas _
abbrev Duo(n:Side):= Seed.Stage n × Yaw n
abbrev Pack(n:Side):Measure (Duo n):= (Seed.heightLaw n).prod (yawP n)
variable (M:Wheel n)
def seedτ (d:ℕ) (x:Seed.Stage n)(i:W M d):= f i.val.card (Seed.pick i.val x).val
variable (hf:∀ i,Measurable (f i)) (hv:∀ S:Wheel n,S.Nonempty→ MeasurePreserving (fun x=> f S.card (Seed.pick S x).val) (Seed.heightLaw n) X.V.c.PM)
include hv in
lemma seed_v(d:ℕ) : MeasurePreserving (seedτ f M d) (Seed.heightLaw n) (Measure.pi (fun _=> X.V.c.PM)):=by
 apply OrderF.abide (orb (fun _:Seat n=> (volume: Measure ↑Seed.ℐ))) (fun i:W M d=>i.val) (fun i x=> seedτ f M d x i) (fun i=>hv i.val (rawS i).1) _ (fun i j=>Gear.disjointΦ)
 intro i x y g; have ht:= BasicIid.key.mp (show few i.val x=few i.val y from g); unfold seedτ Seed.pick; dsimp only; rw [mastL _ (Seed.pri x) (Seed.pri y) (fun i t=>congrArg Subtype.val (ht t)),ht (mastP _ (rawS i).1 _).1]
private def focusP (d:ℕ) (k:W M d)(x:Duo n): Sweep n:= x.2 (greet k.val (Seed.pri x.1))
lemma yawτ (d:ℕ) :MeasurePreserving (fun x:Duo n=> (x.1,fun i=> focusP M d i x)) (Pack n) ((Seed.heightLaw n).prod (Measure.pi fun _:W M d=> paperMeas (Sweep n))) :=by
 refine BasicIid.skew (fun i j k=> focusP M d k (i,j)) ?_ ?_
 · refine measurable_pi_lambda _ ?_; intro i; let F(x:Seed.Stage n):=(greet (n:=n) i.val (Seed.pri x)); have hg:Measurable F:=(mastM _).comp (measurable_pi_lambda _ fun j=>measurable_subtype_coe.comp (measurable_pi_apply _)); exact mealM (F:=F ∘ Prod.fst) (fun j=> (hg.comp measurable_fst) (measurableSet_singleton _)) (G:=fun i (x:Duo n)=> x.2 i) (fun i=> (measurable_pi_apply _).comp measurable_snd)
 intro s; refine ears (fun i:W M d=>greet i.val (Seed.pri s)) ?_ (paperMeas (Sweep n)); intro i j v; by_contra z; let f(Q:W M d):=greet Q.val (Seed.pri s); exact disjointΦ z (f i) (mastP _ (rawS i).1 _).1 (f j) (mastP _ (rawS j).1 _).1 v
lemma Scout.w_cast {J:Type}[Fintype J] (X:Scout J n u t r)(s: Sweep n) : Deck.Chooses X.V.c (X.V_move s).symm :=fun i=>by have hv:= X.sgP s ((X.V_move s).symm i); rw [Equiv.apply_symm_apply] at hv; exact hv.symm
abbrev turn (d:ℕ)(t: W M d→Sweep n)(x:W M d→ J)(i:W M d):=(X.V_move (t i)).symm (x i)
def figs (d:ℕ)(s:Duo n) : W M d→J:= turn X M d (fun i=>focusP M d i s) (seedτ f M d s.1)
include hv
lemma amber (d:ℕ): MeasurePreserving (figs X f M d) (Pack n) (Measure.pi fun _:W M d=> X.V.c.PM):=by
 let A:=Pack n; let Y:= Measure.pi fun _:W M d=> X.V.c.PM; let G:= Measure.pi fun _:W M d=> paperMeas (Sweep n); let X0:=Seed.heightLaw n; let F:=figs X f M d
 have ht:= ((seed_v X f M hv d).prod (MeasurePreserving.id G)).comp (yawτ M d)
 have he:(MeasurePreserving (fun p: (W M d→Sweep n) × (W M d→J)=> (p.1,turn X M d p.1 p.2)) (G.prod Y) (G.prod Y)):= BasicIid.skew (f:=fun x y=>turn X M d x y) (measurable_of_countable _) (fun x=> (measurePreserving_pi (fun _=>X.V.c.PM) (fun _=>X.V.c.PM) (f:=fun i=>(X.V_move (x i)).symm) (fun i=> X.V.c.pm_P _ (Scout.w_cast X (x i))))) -- meas args
 exact measurePreserving_snd.comp ((he.comp Measure.measurePreserving_swap).comp ht) -- tune
omit hv
lemma X_rot (X:Scout J n u t r)(s:Sweep n)(i:J)(P:Pane n): mend (X.X i) s P= X.X ((X.V_move s).symm i) P:=by
 have ht:=X.sym s ((X.V_move s).symm i) P; rw [Equiv.apply_symm_apply] at ht; unfold mend; rw [←ht,revB]
end Star
end YM.CF.DPress.FD
