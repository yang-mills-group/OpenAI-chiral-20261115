import YM.SU5.Selected.Fixed

/-!
# Identify the Compact step of Tapestry.Exhibition EXACTLY with ground-history step D

When using Exhibit later, elect both on V same i k. Not an assertion all these particular
higher/lower period parameters match any older calendar, or an arbitrary tensor of the marks
factorizes. From timing and Exhibit.Exhibition's road (no new following paths), align the
operator norms of the coupons with the sharp transport in Coherent on every Swatch. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)

local notation "K" => tent Y H
open Tapestry

variable {Z : Rack Λ l} {P : Clay Λ l} (U : Exhibition Y H i k I E Z P)
local notation "W₀" S:max => wingspan Λ l S
lemma present_same (s t : ℕ) (S : Finset Cover) (x : Swatch S) :
    present Y H s t S x=distribute Y H s t (render S K x) := (present_send ..)
lemma buying_coupon (s t v : ℕ) (S : Finset Cover) (p : Spanned Y S s t v)
    (h : Tivoli (W₀ S) ((K).c (momentm Y t (s+1)))) (x : Swatch S) :
    render (W₀ S) K (coupon Y H S s t v x) = Tower.block Y H s t v S (render S K x) := by
  apply stationary_ext Y H (s+1) (W₀ S) t h.hosp (texture ..) (booked ..)
  rw [←present_same, onSpanned Y H S s t v p x,
    reserved Y H s S t v p.1 (texture ..) h, present_same]
  rfl
local notation "i₀" n:max=> i (a n)
local notation "k₀" n:max=> k (b n)
include Q U

lemma enlisted (s : ℕ) (S : Finset Cover) :
    Tendsto (fun n=> coupon Y H S s (i₀ n) (k₀ n)) atTop (𝓝 (P S s)) ∧
    ∀ᶠ n : ℕ in atTop, Spanned Y S s (i₀ n) (k₀ n) := by
  let f : ℕ → WedgeStage := fun n => ⟨a n,b n,(U.status _ _).1 (Q.gate n)⟩
  have ht : Tendsto f atTop followStage:= tendsto_comap_iff.mpr Q.growsA.tendsto_atTop
  exact ⟨(U.coneAdvance Y H S s).comp ht, ht.eventually (U.uniformRoad Y H S s)⟩

omit U Q in
lemma eval_cont (K' : Calibration) (S : Finset Cover) (m : Side) (y : Fields (K'.c m)) : Continuous (fun t : Swatch S=> render S K' t m y) :=
 (((LinearMap.proj y).comp (appear S K' m)).mkContinuous (spread S) (fun x=>renderLe S K' m x y)).continuous

omit U in
lemma handrail (s : ℕ) (S : Finset Cover) (x : Family (tent Y H)) (v:InTest K true S false x) (m : Side) (y : Fields ((K).c m)): Tendsto
    (fun r=> block Y H s (i (a r)) (k (b r)) S x m y) atTop (𝓝 (D s x m y)):=by
  obtain ⟨u,g⟩:=Journey.valuation Y H v; obtain ⟨_,_,hD⟩ := Q.implements s S
  have h:=pay_nonneg (show pay x u from g)
  apply Metric.tendsto_nhds.mpr; intro ε v'; let d:=ε/(u+1); have hp:0<d:=by unfold d; positivity
  filter_upwards [hD d hp] with r k
  rw [dist_eq_norm]; apply lt_of_le_of_lt ((k x v u g).2.2.1 m y)
  have ht:d*(u+1)=ε:=div_mul_cancel₀ _ (by linarith); nlinarith
lemma transfer_is (s : ℕ) (S : Finset Cover) (x : Swatch S) :
    D s (render S K x)=render (W₀ S) K (P S s x) := by

  funext m y
  let f (n:ℕ) := coupon Y H S s (i (a n)) (k (b n)) x
  obtain ⟨he,hu⟩ := enlisted Y H Q U s S
  let W := followBox (Λ:=Λ) (l:=l) S
  have hw : Tendsto f atTop (𝓝 (P S s x)):= cn_apply (Y:=Swatch W) (X:=Swatch S) he (tendsto_const_nhds (x:=x))
  refine tendsto_nhds_unique_of_eventuallyEq (handrail Y H Q s S (render S K x) (texture ..) m y) ((eval_cont K W m y).continuousAt.tendsto.comp hw) ?_
  apply (hu.and ((U.univ_.pick.grow_i.comp Q.growsA).tendsto_atTop.eventually (turning Y H (s+1) W))).mono
  exact fun i u=> congr_fun (congr_fun (Eq.symm (buying_coupon Y H s _ _ S u.1 u.2 x)) m) y

lemma seamless (s : ℕ) (F : Dome (tent Y H)) : (U.liftD Y H s F).val = D s F.val := by
  obtain ⟨S,h⟩ := findsBay K F
  obtain ⟨x,rfl⟩ := accolade K S F h
  rw [U.fromLocal]; exact (transfer_is Y H Q U s S x).symm
end YM.CF.Buffered.Afterglow.Tower.Selection
