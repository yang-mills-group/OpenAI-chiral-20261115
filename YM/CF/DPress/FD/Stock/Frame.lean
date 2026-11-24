import YM.CF.DPress.FD.Stock.Freight
/-!
 Equality with the **single random map applied once at all components** law, through
 footprints and independence. Conditional on the field A and its unchanged gauge-site heights
 (site-group Haar tags used to form A; not conditional on real priorities). -/
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
variable (X:Scout J n u t r) (A:Pane n)
abbrev Crew (M:Wheel n)(d:ℕ): Type:= W M d→Pane n
-- Splices per component
def PanelM(u:ℝ)(A:Pane n)(d:ℕ)(F:Crew (RG.flags u A) d): Pane n:= fun i=> if p:(soup (RG.flags u A) d i).Nonempty then F ⟨soup (RG.flags u A) d i,recept p⟩ i else A i
lemma PanelO(u:ℝ)(A:Pane n)(d:ℕ) : Measurable (PanelM u A d):= by apply measurable_pi_lambda _; intro i; unfold PanelM; split; exact (measurable_pi_apply _).comp (measurable_pi_apply _); exact measurable_const
-- partial panel at each E
noncomputable def bundle (k:ℕ)(F:W (RG.flags u A) k)(j:J):Pane n:= fun i=> if soup (RG.flags u A) k i =F.val then X.X j A i else A i
def made (k:ℕ)(F:W (RG.flags u A) k→J):=PanelM u A k (fun i=>bundle X A k i (F i))
lemma made_v (k:ℕ)(F:W (RG.flags u A) k→J)(i:reach n): made X A k F i= if p:(soup (RG.flags u A) k i).Nonempty then X.X (F ⟨soup (RG.flags u A) k i,recept p⟩) A i else A i:=by unfold made PanelM bundle; split <;> simp
lemma panel_x (v:r≤d)(x:J): PanelM u A d (fun i=>bundle X A d i x)= X.X x A:=by
 funext i; rw [show PanelM _ A d _=made X A d (fun _=>x) from rfl, made_v]; split; exact rfl; next t=> exact ((Basic_more (X.basicF x) v).covers _ _ (not_not.mp ((pieV (RG.flags u A) d i).not.mp t))).symm -- ss simp
lemma budgetT (i:W (RG.flags u A) d)(p: r≤d): X.V.idT (bundle X A d i) (Quire i.val r):=by
 intro j x h; funext a; unfold bundle; split; swap; exact rfl
 next t=>
  by_cases v:Disjoint (RG.flags u A) (win r a); · rw [(X.basicF j).covers A a v,(X.basicF x).covers A a v]
  exact X.V_ear a A j x (X.V.le _ _ (worth _ v p t) j x h)
private lemma reg {E K I Z:Type*}[Fintype E][MeasurableSpace K][Fintype I][MeasurableSpace Z]{J':Type*}[MeasurableSpace J'](P:Measure J')[IsProbabilityMeasure P] {y:E→ E→Prop} (W: OrderF y P) (f:(I→ K)→Z) (g: I→ J'→ K) (h:Measurable f)(v:∀ i,Measurable (g i))(S:I→Finset E)(p:∀ i,W.concerns (g i) (S i))(t:∀ i j,i≠ j → Meeting y (S i) (S j)) : (Measure.pi fun _:I=>P).map (fun s=> f (fun i=>g i (s i)))=P.map (fun x=> f (fun i=>g i x)):=by
 let l(i:I):=P.map (g i); let D:=Measure.pi l; haveI hi(i):IsFiniteMeasure (l i):=by unfold l; infer_instance
 have ht:MeasurePreserving (fun x:I→ J'=>fun i=> g i (x i)) (Measure.pi (fun _:I=>P)) D:= measurePreserving_pi (f:=g) (fun _=>P) l (fun i=> ⟨v i,rfl⟩)
 have hv:= OrderF.supply W S g v p t
 exact Eq.trans ((Measure.map_map h ht.measurable).symm.trans (congrArg (Measure.map f) ht.map_eq)) (Eq.symm ((Measure.map_map h hv.measurable).symm.trans (congrArg (Measure.map f) hv.map_eq)))
-- compare visibility verified
lemma moon_p (v:100*r ≤d): (Measure.pi (fun _: W (RG.flags u A) d => X.V.c.PM)).map (made X A d) = X.V.c.PM.map (fun x=> X.X x A):=by
 have hv:= reg X.V.c.PM (OrderF.extend X.V) (PanelM u A d) (bundle X A d) (PanelO ..) (fun i=> measurable_of_countable _) (fun i=>Quire i.val r) (fun i=> budgetT X A i (by omega)) (fun i j t=> loft t v)
 exact hv.trans (congrArg (fun w:J→Pane n=> X.V.c.PM.map w) (funext (fun x=> panel_x X A (by omega) x)))
-- combine yaw measure preim
abbrev Masters(g: Seat n → E)(x:Duo n)(i:Seat n):Bone n:= ((x.1 i).val,x.2 i,g i)
variable (f:ℕ→ℝ→J)
lemma fig_U(k:ℕ)(x:Duo n)(g:Seat n→ E): glow X f k (A,Masters g x)=made X A k (figs X f (RG.flags u A) k x):=by
 funext e; rw [made_v]; unfold glow well; dsimp only; split_ifs with t; swap; exact rfl
 rw [X_rot]; rfl -- focusP private other file defeq? rfl can reduce private.
end Star
end YM.CF.DPress.FD
