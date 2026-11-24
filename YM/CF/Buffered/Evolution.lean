import YM.CF.Buffered.Layers
import YM.CF.Buffered.ScalarSplit

/-!
# Evolution layers in the sewn volume

`false` is the entry seam = gauge plane zero = the non-wrap seam (after the
change of basis to `axisCut`, which keeps the anticut in transverse
directions and puts the minus sign in axis i at the OPPOSITE plane), `true`
the exit/wrap seam. In the two-slab case we can simplify: use the channels
written as θ(negative side data)·(positive side data), even at the WRAP
seam, i.e., write the crossing in the **same** order as the non-wrap one.
Use FiniteGaugeData's `enter` and `exitK` channelizations to do this. Both include the
split gauge transport halves. This absorbs the minus sign from the wrap seam
in the CAR calculation (`end_energy` through `waking`). Costs are at fixed
cube, fixed heat parameter. These are the two slabs and the layers (n+1
layers indexed by n) used below for the trace calculation.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Gloss Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)

-- use chord normalization to absorb odd signs
def pairSquare {n : Type*} [LinearOrder n] [Fintype n]
    (U : UNI n) (b : Bool) (x y : FC n) : FC n := chord b • (theta U x * y)

abbrev Modes (m B : Side) := (Xmind m B ⊕ Xmind m B)

def aperture (i : Axis) (u : Bool) (x : Pack m B) :=
  if u then exitK m B i x.1 else enter m B i x.1

def channel (i : Axis) (u : Bool) (x : Pack m B) : Modes m B → FC (Xmind m B) := Sum.elim
  (fun j => remove (acts (aperture i u x) (basisKet j)))
  (fun j => create (acts (aperture i u x) (basisKet j)))

variable (i : Axis)

lemma aperture_local {u} {x y : Pack m B} (h : NorthOf m B i x y) : aperture i u x=aperture i u y := by
  cases u
  · exact enter_area i h
  exact exit_area i h
lemma channel_local {u} {x y : Pack m B} (h : NorthOf m B i x y) : channel i u x=channel i u y := by
  unfold channel; rw [aperture_local i h]
lemma channel_cont (a : Modes m B) (u) : Continuous (fun x : X => channel i u x a) := by
  have ht:Continuous (aperture (m:=m) (B:=B) i u) := by
    unfold aperture; cases u
    · exact (enter_cont i).comp continuous_fst
    exact (exit_cont i).comp continuous_fst
  cases a with
  | inl a => exact (create_cont.comp ((acts_cont.comp ht).clm_apply (continuous_const (y:=basisKet a)))).star
  | inr a => exact create_cont.comp ((acts_cont.comp ht).clm_apply continuous_const)
lemma channel_sector (a : Modes m B) (u) (x : X) : Sector (colony m B i) true (channel i u x a) := by
  have hh j : acts (Ledge m B i) (acts (aperture i u x) (basisKet j))=acts (aperture i u x) (basisKet j) := by
    rw [← act_mul]; cases u
    · rw [aperture, if_neg (by decide), enter_pos]
    rw [aperture, if_pos rfl, exit_pos]
  rcases a with a | a
  · exact (Sector.makeP _ (hh a)).contr
  exact Sector.makeP _ (hh a)

noncomputable def crossHop (u : Bool) (x : Pack m B) :=
  ∑ a : Modes m B, pairSquare (finger m B i) true (channel i u (Pbar m B i x) a) (channel i u x a)

def slabGen (c : Foot m B) (x : Pack m B) := dg (Ledge m B i * wiel m B (axisCut m B i c) x.1 * Ledge m B i)
lemma slabGen_cont (c : Foot m B) : Continuous (slabGen i c) :=
  dg_cont.comp ((continuous_const.mul ((wiel_cont _).comp continuous_fst)).mul continuous_const)
lemma slabGen_local (c : Foot m B) {x y : Pack m B} (h : NorthOf m B i x y) : slabGen i c x= slabGen i c y := by
  unfold slabGen; rw [sup_area i h]
lemma slabGen_sector (c : Foot m B) (x : Pack m B) : Sector (colony m B i) false (slabGen i c x) :=
  abs_dg ..
lemma crossHop_sewn (u : Bool) (x y z : Pack m B) : let U := tiedK m B i x;
    crossHop i u (U y z) = ∑ a : Modes m B, pairSquare (finger m B i) true (channel i u (U z z) a) (channel i u (U y y) a) := by
  intro U; unfold crossHop
  rw [show Pbar m B i (U y z)=U z y from sew ..,
      channel_local i (show NorthOf m B i (U z y) (U z z) from strum ..), channel_local i (show NorthOf m B i (U y z) (U y y) from strum ..)]
lemma crossHop_cont (u : Bool) : Continuous (crossHop (m:=m) (B:=B) i u) :=
  continuous_finsetSum _ fun a _ => (continuous_const (y:=chord true)).smul
    (((theta_cont (RP.finger m B i)).comp ((channel_cont i a u).comp ((slideM m i).convey B))).mul (channel_cont i a u))

set_option maxRecDepth 8000 in
lemma generator_parts_sewn (c : Foot m B) (x y z : Pack m B) : let a := tiedK m B i x y z
    dg (wiel m B (axisCut m B i c) a.1) = theta (finger m B i) (slabGen i c (Pbar m B i a)) + slabGen i c a +
      (crossHop i false a + crossHop i true a) := by
  intro a
  let U := tiedK m B i x
  rw [show Pbar m B i a=U z y from sew .., crossHop_sewn i false x y z, crossHop_sewn i true x y z,
    slabGen_local i c (show NorthOf m B i (U z y) (U z z) from strum ..), slabGen_local i c (show NorthOf m B i a (U y y) from strum ..)]
  -- keep both seam alphabets
  rw [waking i x c y z]
  have sum_splits (u):
      (∑ j:I,(pairSquare (finger m B i) true (channel i u (U z z) (Sum.inl j)) (channel i u (U y y) (Sum.inl j))+
        pairSquare (finger m B i) true (channel i u (U z z) (Sum.inr j)) (channel i u (U y y) (Sum.inr j)))) =
        ∑ j:Modes m B, pairSquare (finger m B i) true (channel i u (U z z) j) (channel i u (U y y) j) := by
    rw [sum_add_distrib, Fintype.sum_sum_type]
  exact congrArg (fun a => theta (finger m B i) (slabGen i c (U z z))+slabGen i c (U y y)+a) (congrArg₂ (· + ·) (sum_splits false) (sum_splits true))

lemma generator_parts (c : Foot m B) (x : Pack m B) :
    dg (wiel m B (axisCut m B i c) x.1) = theta (finger m B i) (slabGen i c (Pbar m B i x)) + slabGen i c x +
      (crossHop i false x + crossHop i true x) := by
  simpa only [Spark.truly] using (generator_parts_sewn i c x x (Pbar m B i x))

-- Evolution approximant on the actual fields
def hotEvol (c : Foot m B) (u : ℝ) (n : ℕ) (x : Pack m B) :=
  Trotter.evolution (u • theta (finger m B i) (slabGen i c (Pbar m B i x)))
    (u • slabGen i c x) (u • crossHop i false x) (u • crossHop i true x) n

def actualEvol (c : Foot m B) (u : ℝ) (x : Pack m B) :=
  exp (u • dg (wiel m B (axisCut m B i c) x.1))

lemma actualEvol_quant (c : Foot m B) (u : ℝ) (x : Pack m B) :
    actualEvol i c u x = quant (grow (wiel m B (axisCut m B i c) x.1) u) := (ferment (self_wiel ..) u).symm

open scoped BoundedContinuousFunction
lemma hotEvol_uniform (c : Foot m B) (u : ℝ) :
    ∃ (K : ℕ → CBox X I) (W : CBox X I), (∀ n x, K n x=hotEvol i c u n x) ∧
      (∀ x,W x=actualEvol i c u x) ∧ Tendsto K atTop (𝓝 W) := by
  let M : CBox X I := BoundedContinuousFunction.mkOfCompact ⟨slabGen i c, slabGen_cont i c⟩
  let N : CBox X I := BoundedContinuousFunction.mkOfCompact
    ⟨_, (theta_cont (finger m B i)).comp ((slabGen_cont i c).comp ((slideM m i).convey B))⟩
  let L (t:Bool) : CBox X I := BoundedContinuousFunction.mkOfCompact ⟨crossHop i t, crossHop_cont ..⟩
  let G := u • N + u • M + (u • L false + u • L true)
  refine ⟨Trotter.evolution (u • N) (u • M) (u • L false) (u • L true), exp G, ?_, ?_, Trotter.evolution_limit ..⟩
  · intro n x; unfold Trotter.evolution Trotter.layer hotEvol;
    rw [BoundedContinuousFunction.pow_apply, BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.mul_apply,
        BoundedContinuousFunction.mul_apply,Reflect.eval_exp,Reflect.eval_exp]; rfl
  intro x; rw [eval_exp, actualEvol, generator_parts]; simp_rw [smul_add]; rfl
lemma hotEvol_cont (c : Foot m B) (u : ℝ) (n : ℕ) : Continuous (hotEvol i c u n) := by
  obtain ⟨K, W, hk, _, _⟩ := hotEvol_uniform i c u
  rw [← funext (hk n)]; exact (K n).continuous
lemma actualEvol_cont (c : Foot m B) (u : ℝ) : Continuous (actualEvol i c u) := by
  obtain ⟨_, W, _, hw, _⟩ := hotEvol_uniform i c u
  rw [← funext hw]; exact W.continuous
end YM.CF.Buffered.Heat
