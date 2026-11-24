import YM.CF.Continuum.Sink
import YM.CF.Reflect.Pad

/-! Reflection frozen at a seamed classical gauge background. Does NOT
    assert after averaging. No auxiliary spin needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Lattice Wilson Lat SU Fock Phase Mir Cube Mir.Trip RP Reflect Finset
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder BoundedContinuousFunction Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B : Side}
local notation "N"=> CSide m B

lemma fibre_tile {n X : Type*} [LinearOrder n] [Fintype n] [TopologicalSpace X]
    (x : X){U : UNI n}{P S : Finset n}(h : twist U (cutM S)=cutM Sᶜ)(p : twist U (cutM Pᶜ)=cutM P){F:CSeat X n}(q : F ∈ Cloud U S X) : 0 ≤ F (x,x) P P :=by
  have hx : Continuous (fun F:CSeat X n=> F (x,x) P P) := by apply Continuous.matrix_elem; fun_prop
  apply closure_minimal (t:={y:CSeat X n|0 ≤ y (x,x) P P}) ?_ (isClosed_le continuous_const hx) q
  intro y e; change Faced U S y at e; change 0 ≤ y (x,x) P P; induction e with
  | square b f hf => rw [show tile U b f (x,x) P P=_ from theta_square P U p S h (f x) _ b (hf x) (hf x)]; apply star_mul_self_nonneg
  | zero => exact le_refl _
  | plus _ _ a b => exact add_nonneg a b
  | raise a ha _ e => exact smul_nonneg ha e

lemma frozen_exists {i:Axis}(u : Skin m B) (h:rayUK m B i u=u) : ∃ x:Pack m B, (tiedK m B i x x x).1=u := by
  let x:Pack m B:= (u,(cue_from u).choose); refine ⟨x,funext fun j=>?_⟩; rcases all_vars (m:=m) (B:=B) i j with e|e
  · rw [upU i x x x j e, ite_self]
  rw [downU i x x x j e]; split; rfl; exact congrFun h j

lemma reflector_heat {c : Foot m B}{i:Axis}{b:Bool} (u : Skin m B) (h:rayUK m B i u=u)
    (p : FC (Xmind m B)) (q : Sector (colony m B i) b p) (t : ℝ) (k : 0 ≤ t) : let H:= wiel m B (axisCut m B i c) u; 0 ≤ inner ℂ (linearB N) (acts (chord b • (theta (finger m B i) p*p)) (acts (quant (grow H t)) (linearB N))) := by
  obtain ⟨x,r⟩:= frozen_exists u h; intro H
  obtain ⟨W,hW,v⟩:= RP.accomplish (X:=Unit) i x (fun _=>x) continuous_const c t k
  let F :Unit→ᵇ FC (Xmind m B):= BoundedContinuousFunction.const _ p
  let C := tile (finger m B i) b F
  have he := rain_mul ((Faced.square b F (fun _=>q)).run) hW (movedCol ..)
  rw [← act_mul,bra_fix, ← show W ((),())=quant (grow H t) from (by rw [v]; simp only [r]; rfl)]
  exact fibre_tile () (movedCol ..) (slide_plus ..) he
lemma reflector_line {c : Foot m B}{i:Axis}{b:Bool} (u : Skin m B) (h:rayUK m B i u=u)
    (p : FC (Xmind m B)) (q : Sector (colony m B i) b p) (k:Safe (wiel m B (axisCut m B i c) u)) :
    let H:= wiel m B (axisCut m B i c) u; 0 ≤ inner ℂ (linearB N) (acts (chord b • (theta (finger m B i) p*p)) (acts (lineOp (projector H)) (linearB N))) := by
  intro H; let A:=chord b • (theta (finger m B i) p*p); let Y:=linearB N; let k': Safe H:= k
  let G : FC (Xmind m B)→ℂ := fun f=>inner ℂ Y (acts A (acts f Y)); have he: Continuous G:= continuous_const.inner ((acts A).continuous.comp (acts_cont.clm_apply continuous_const)); apply ge_of_tendsto (f:=fun t:ℝ=>G (heatSlice H t)) (he.continuousAt.tendsto.comp (late_flight k'))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t e; unfold G heatSlice; rw [act_smul _ (quant (grow H t)),map_smul,inner_smul_right]; exact mul_nonneg (inv_nonneg.mpr (flight_positive k' t).le) (reflector_heat u h p q t e)
end YM.CF.Window
