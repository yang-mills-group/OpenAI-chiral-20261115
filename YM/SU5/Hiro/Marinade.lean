import YM.SU5.Hiro.Tablecloth
import YM.SU5.Hiro.Morsel
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 230000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Hiro Ballad Papal Regis.Head.Brecht
open Twah (DirSpin) -- adjust
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
namespace Spine
variable (P: Spine)(L G:DirSpin)(R:ℕ)(F D: PlaqAxes)(x y:Cover){k:ℝ}(p:0<k)(ζ:ℝ)(s:ℕ)
private lemma atlasZ (x:ℕ→ℂ){C:ℝ}(p:∀ i,‖x i‖≤C):∃ t:ℂ,‖t‖ ≤ C∧Tendsto x sceneL (𝓝 t):=by
 obtain ⟨y,v,u⟩:= IsCompact.ultrafilter_le_nhds' (s:=closedBall (0:ℂ) C) (isCompact_closedBall _ _) (f:=(Filter.hyperfilter ℕ).map x) (show ∀ᶠ i in sceneL,x i∈closedBall (0:ℂ) C from Eventually.of_forall fun i=> mem_closedBall_zero_iff.mpr (p i)); exact ⟨y,mem_closedBall_zero_iff.mp v,u⟩
abbrev kitchenB (R:ℕ):ℝ:= (prices_dice P.par.K.j (P.par.kJ.symm ▸ (by decide:1≤(4:ℕ))) R).choose
local notation "Y"=>P.kitchenB R
def taste (i j:ℕ):ℂ:= diced R x y L G (Papal.count P.run s (P.period i)) P.par.K.j (Papal.gram P.run s (P.period i) (P.cutoff j)).J.M
lemma kitchen_ready :0 < P.kitchenB R ∧ ∀ i j, ‖P.taste L G R x y s i j‖≤ P.kitchenB R:= by
 have h:= (prices_dice P.par.K.j (P.par.kJ.symm ▸ (by decide:1≤(4:ℕ))) R).choose_spec; exact ⟨h.1,fun i j=> h.2 (Vale.val_e ..) ..⟩
def innerTaste(i:ℕ):ℂ:= (atlasZ _ ((P.kitchen_ready L G R x y s).2 i)).choose
lemma inner_food (i:ℕ): ‖P.innerTaste L G R x y s i‖≤ Y∧ Tendsto (fun j=>P.taste L G R x y s i j) sceneL (𝓝 (P.innerTaste L G R x y s i)):= (atlasZ _ ((P.kitchen_ready L G R x y s).2 i)).choose_spec -- explicit witness
noncomputable def tastemaker := (atlasZ _ (fun i=> (P.inner_food L G R x y s i).1)).choose
lemma funds_food : ‖P.tastemaker L G R x y s‖≤ Y ∧ Tendsto (P.innerTaste L G R x y s) sceneL (𝓝 (P.tastemaker L G R x y s)):= (atlasZ _ (fun i=> (P.inner_food L G R x y s i).1)).choose_spec
variable (u:ℕ→ℕ)(r:ℕ→ℕ)(B C:ℕ→ Cover)
open Stationary (Gaia)
theorem food_moves {X:Gaia}(v:Tendsto r atTop atTop)(h:∀ i,0<r i)(t:Tendsto (fun i=> Onyx.riseX (r i) (B i-C i)) atTop (𝓝 X))(e:X≠0): Tendsto (fun i=> P.tastemaker L G (r i) (B i) (C i) (u i)) atTop (𝓝 (shotR L G (X:=X))):=by
 refine Metric.tendsto_nhds.mpr fun i ht=>?_; let e':= i/2; have he:=half_lt_self ht;
 filter_upwards [travel_feast P.par.K.j L G (P.par.kJ.symm ▸ (by decide: 1≤(4:ℕ))) r v h C B t e e' (half_pos ht)] with i t
 apply lt_of_le_of_lt _ he; apply le_of_tendsto ((P.funds_food L G (r i) (B i) (C i) (u i)).2.dist tendsto_const_nhds)
 apply Nat.hyperfilter_le_atTop; filter_upwards [((count_la P.run (u i)).comp (P.law.pick.grow_i.tendsto_atTop)).eventually t] with j p; exact le_of_tendsto ((P.inner_food L G (r i) (B i) (C i) (u i) j).2.dist tendsto_const_nhds) (Eventually.of_forall fun k=> p (Vale.val_e ..) _)
local notation "ρ" b:max=> Papal.museumV (P:=P.par) b
include p
private lemma flavorWin {ε:ℝ}(e:0<ε):∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),∀ s:ℕ,Layover (courseMenu F D x y (Papal.museumV (P:=P.par) s) p R L G (P.tastemaker L G R x y s)) (coaster F D x y p) P.run P.period P.cutoff s t ε:=by
 let h:1≤P.par.K.j:=P.par.kJ.symm ▸ (by decide:1≤(4:ℕ));
 filter_upwards [layoverMenu F D x y p R L G P.par.K.j h (P.kitchen_ready L G R x y 0).1.le e] with t g s'; obtain ⟨Z,xv,b⟩:=g
 let f(i:ℕ):= P.innerTaste L G R x y s' i; let κ:=P.tastemaker L G R x y s'; let π(i j:ℕ):= P.taste L G R x y s' i j; let Ng(i:ℕ):= Papal.count P.run s' (P.period i)
 refine Filter.Frequently.filter_mono ?_ Nat.hyperfilter_le_atTop
 apply Filter.Eventually.frequently; have hc:∀ᶠ i in sceneL,HaloTw P.par.K.j (Ng i):=Nat.hyperfilter_le_atTop ((((count_la P.run s').comp (P.law.pick.grow_i.tendsto_atTop)).eventually (ownsHalo h)).mono (fun i f=>f (Vale.val_e ..)))
 filter_upwards [hc,Metric.tendsto_nhds.mp (P.funds_food L G R x y s').2 (Z/2) (half_pos xv)] with i v u; refine Filter.Frequently.filter_mono ?_ Nat.hyperfilter_le_atTop; apply Filter.Eventually.frequently
 filter_upwards [Metric.tendsto_nhds.mp (P.inner_food L G R x y s' i).2 (Z/2) (half_pos xv)] with j p'; refine b _ v.1 ((P.kitchen_ready L G R x y s').2 i j) (Papal.museumV (P:=P.par) s') κ ?_; change dist κ (π i j) ≤ Z; rw [dist_comm]; refine (dist_triangle (π i j) (f i) κ).trans ((add_le_add p'.le u.le).trans_eq (add_halves Z)) -- tune
-- single menu compact born ok. Palm bound global *∀ε* schedule; use to philanthropic variance.
def jade (s:ℕ): P.Test:=P.tuneK (currentLabel F x (Papal.museumV (P:=P.par) s) R L p)
def JadeRate : P.Test:= P.tuneK (menuTag F D x y (Papal.museumV (P:=P.par) s) p R L G (P.tastemaker L G R x y s))
variable {P}{X:Supplier}{U:P.Register}{e v:ℝ}
variable (H:uniform P U X e v)
include H
omit p
private lemma slimBudget {j:Axis}{X: ℕ → Weaver}{K:Finset Cover}(u:∀ s:ℕ, Lamour.Bridge.Celeste.Voice (X s) K)(h:∃ C>(0:ℝ),∀ s:ℕ, amplitude C (X s)) (t:∀ ε>(0:ℝ),∃ ξ>(0:ℝ),∀ s:ℕ,Layover (X s) K P.run P.period P.cutoff s ξ ε) {d:ℝ}(w:0<d) :∀ᶠ s in atTop, ‖P.E s (P.tuneK (u s)).val‖ ≤ d ∧ (∫ x,‖P.singleState j s x (P.tuneK (u s))‖^2 ∂ (P.pillars j))≤ d:=by
 obtain ⟨a,hA,Z⟩:=h; obtain ⟨ε,e',hV,hD⟩:=small_bank Unit d w; obtain ⟨k,p,hk⟩:=t _ e'; obtain ⟨T,vv,r,C,D,q,hG,v⟩:=H.1.paper -- shadow u
 obtain ⟨T,p₀,hT⟩:=Papal.bigRegion P.run P.large P.law hG H.2 H.1.nerve p hA.le K j e' hV
 filter_upwards [hT] with s ht; let W := ht _ (u s) (Z s) (hk _); exact ⟨W.1.trans hD.1,(P.credit_delivers j (u s) s T p₀).trans (W.2.trans hD.1)⟩
include p
lemma thinBudget (d:ℝ)(w:0<d):∀ᶠ s:ℕ in atTop, ‖P.E s (P.jade L R F x p s).val‖≤ d ∧ (∫ x',‖P.singleState 3 s x' (P.jade L R F x p s)‖^2 ∂ (P.pillars 3))≤ d:=by
 let K:= platePin F (nodeC x); let v(s:ℕ):= currentLabel F x (Papal.museumV (P:=P.par) s) R L p
 obtain ⟨c,hZ,Q⟩:= afford_current F x R L p; refine slimBudget H v ⟨c,hZ,fun i=> Q _⟩ (fun e t=>⟨1,zero_lt_one,fun s=>?_⟩) w; unfold Layover; let h:1≤P.par.K.j:=P.par.kJ.symm ▸ (by decide:1≤(4:ℕ)); exact ((((count_la P.run s).comp (P.law.pick.grow_i.tendsto_atTop)).eventually (ownsHalo h)).mono fun i ht=> (Eventually.of_forall (fun k=> layoversingle F x _ p R L P.par.K.j h _ (ht (Vale.val_e ..)).1 t.le)).frequently).frequently
lemma thickBudget (d:ℝ)(w:0<d):∀ᶠ s:ℕ in atTop, ‖P.E s (P.JadeRate L G R F D x y p s).val‖≤ d ∧ (∫ x', ‖P.singleState 3 s x' (P.JadeRate L G R F D x y p s)‖^2 ∂ (P.pillars 3))≤ d:=by
 obtain ⟨b,v,Q⟩:= menuPower F D x y p R L G (P.kitchenB R) (P.kitchen_ready L G R x y 0).1.le; refine slimBudget H (P:=P) (fun s=> menuTag F D x y (Papal.museumV (P:=P.par) s) p R L G (P.tastemaker L G R x y s)) ⟨b,v,fun s=> Q _ _ (P.funds_food L G R x y s).1⟩ (fun e v=> ?_) w; exact ((Filter.Eventually.and (show ∀ᶠ z:ℝ in 𝓝[>] (0:ℝ),0<z from self_mem_nhdsWithin) (flavorWin P L G R F D x y p v))).exists
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.food_moves
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.thinBudget
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.thickBudget
