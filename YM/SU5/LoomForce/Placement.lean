import YM.SU5.LoomForce.StaffLimit
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
open Vale (hat)
/-!
Put the Staff fits in the actual cells. Results uniform over every period and
cutoff at each late rung as far as these support qualifications are concerned.
Not assuming the support reaches are small enough because it's true in a comparator.
-/
open EmberWind Lamour.Bridge.Celeste

def adjacent (u : Cover) (b : PlaqAxes) (g : Twah.DirSpin) : Staff where
  hub := nodeC u
  u := u
  face := (nodeC u,b)
  spin := g
  steps := []
  stop_at := rfl

omit P in
lemma adj_pays (u : Cover) (b : PlaqAxes) (g : Twah.DirSpin) {e r : ℕ} (p : 4 ≤ r) :
    (adjacent u b g).Pays r e := by
  constructor
  · exact Nat.zero_le _
  · intro i h
    change i ∈ visits (nodeC u) [] at h
    simp only [visits,List.mem_singleton] at h
    rw [h]; exact owns ..
  intro i h; exact pav_mono p (walk_pav (nodeC u) i (square b.val.1 b.val.2)
    (List.mem_toFinset.mp h))

omit P in
lemma inside_deck {u v : Cover} {a b : ℕ} (p : u ∈ skyDeck v a) :
    skyDeck u b ⊆ skyDeck v (a+b) := by
  intro i h; apply (pav_v ..).2; intro j; obtain ⟨x,y⟩:=(pav_v ..).1 p j
  obtain ⟨w,z⟩ := (pav_v ..).1 h j; omega

omit P in
lemma lift_tenant {W : Staff} {o : Cover} {a b : ℕ} (n : Side)
    (p : W.hub ∈ skyDeck o a) :
    W.tenancy n b Staff.clearance (a+(b+Staff.clearance+8)) (wrap (More n) o) := by
  change Lattice.halo _ _ ⊆ Lattice.halo _ _; rw [←wrap_pav,←wrap_pav]; exact image_subset_image (inside_deck p)

variable {A I : ℝ} (hA : 0 < A)
local notation "S" s:max => sPow (Spine.par P) s A
local notation "S₁" s:max => sPow (Spine.par P) s I
open Pressure Worth Worth.Pays BProof
omit hA in
lemma appointment_cost {u : ℕ → Cover} {x : Gaia} (h : Appoint P.par A u x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s : ℕ in atTop, nodeC (u s) ∈ skyDeck 0 ⌈C * S s⌉₊ := by
  let C := ‖x‖ + 1
  refine ⟨C,by unfold C; positivity,?_⟩
  have w := Tendsto.norm (show Tendsto _ _ _ from (h : Tendsto _ _ _)) -- tune
  have v : ‖x‖ < C := by unfold C; linarith
  filter_upwards [w.eventually (ge_mem_nhds v)] with s u'
  let p := riseX (S s) (nodeC (u s)); change ‖p‖ ≤ C at u'
  have he: 0 < S s := BProof.coin_pos ..
  apply (pav_v ..).2; intro j; have hf : |(↑(nodeC (u s) j):ℝ) / S s| ≤ C :=
    (PiLp.norm_apply_le p j).trans u'
  rw [abs_div, abs_of_pos he, div_le_iff₀ he] at hf
  have hy := abs_le.mp (hf.trans (Nat.le_ceil _)); change 0 - (↑_ : ℤ) ≤ _ ∧ _ ≤ 0 + (↑_ : ℤ)
  rw [zero_sub,zero_add]; exact_mod_cast hy

variable {u v : ℕ → Cover} {x y : Gaia} (U : Appoint P.par A u x)
    (V : Appoint P.par A v y)
include hA U V
local notation "ar" b:max g:max u:max => fun s : ℕ => adjacent (u s) b g
lemma fitting (f g : PlaqAxes) (i j : Twah.DirSpin) (h : A < I) {r : ℕ} (_p : 4 ≤ r) :
    ∀ᶠ s : ℕ in atTop, ∃ e : ℕ, (e:ℝ) ≤ S₁ s ∧
      ∀ n : Side, (adjacent (u s) f i).tenancy n r Staff.clearance e (wrap (More n) 0) ∧
        (adjacent (v s) g j).tenancy n r Staff.clearance e (wrap (More n) 0) := by
  obtain ⟨C,c,H⟩ := appointment_cost P (A:=A) (u:=u) (x:=x) U; obtain ⟨D,d,W⟩ := appointment_cost P (A:=A) (u:=v) (x:=y) V
  let Z := max C D
  let t := r+Staff.clearance+8
  have ht := Pays.plus (Pays.scale Z (Pays.whole 0 A 0))
    (Pays.merit (Pays.constant (1+(t:ℝ))) (Or.inr (Or.inl ⟨rfl,hA⟩)))
  filter_upwards [(turnover Λ).eventually (Pays.leap ht (Or.inr (Or.inl ⟨rfl,h⟩)) (q:=0)), H, W] with s hs hU hV
  let a := ⌈Z * S s⌉₊
  have hpos : 0 ≤ S s := BProof.coin_pos ..|>.le
  have he : 0 ≤ Z := c.le.trans (le_max_left ..)
  refine ⟨a+t, ?_,fun n => ⟨lift_tenant n ?_,lift_tenant n ?_⟩⟩
  · push_cast; refine le_trans ?_ hs; have hp : (a:ℝ) < Z * S s + 1 := Nat.ceil_lt_add_one (mul_nonneg he hpos)
    change (a:ℝ)+(t:ℝ) ≤ Z * S s + (1+(t:ℝ)); linarith only [hp]
  · exact pav_mono (show ⌈C*S s⌉₊ ≤ a from Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right (le_max_left ..) hpos)) hU
  exact pav_mono (show ⌈D*S s⌉₊ ≤ a from Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right (le_max_right ..) hpos)) hV


lemma fitting_pair (F G : PlaqAxes) (i j : Twah.DirSpin) (h : A < I) {r : ℕ} (p : 4 ≤ r) :
    PaidPair P I (ar F i u) (ar G j v) (fun _ => r) := by
  refine ⟨lt_trans hA h,?_⟩
  filter_upwards [fitting P hA U V F G i j h p] with s hs
  obtain ⟨e,t,w⟩ := hs
  apply Eventually.of_forall; intro n; obtain ⟨g,k⟩:=w (matterSide P s n)
  exact ⟨e,0,wrap (More _) 0,t,by simpa using (BProof.coin_pos ..|>.le), adj_pays _ _ _ p, adj_pays _ _ _ p,g,k⟩

omit hA U V P in
lemma rise_sub (b : ℝ) (u v : Cover) : riseX b u - riseX b v = riseX b (u-v) := by
  ext i; change ((u i:ℝ)/b) - ((v i:ℝ)/b) = (((u-v) i:ℝ)/b)
  simp only [←sub_div,Pi.sub_apply,Int.cast_sub]

local notation "PW" b:max i:max u:max t:max r:max s:max => weaving P A (adjacent (u s) b i) r s t
lemma visit_book (H : P.PhysicalWakeGram) {f : ℕ → ℕ} {β : ℕ → ℝ}
    (B : Pooling Γ (takenVolume P) (takenCutoff P) f β)
    (F G : PlaqAxes) (i j : Twah.DirSpin) {r : ℕ} (p : 4 ≤ r) (t : x ≠ y) :
    Tendsto (fun s => infiniteE P s (PW F i u β r s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (PW G j v β r s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (PW F i u β r s * PW G j v β r s) -
      infiniteE P s (PW F i u β r s) * infiniteE P s (PW G j v β r s)) atTop
      (𝓝 (wakeFee F G i j (x-y) (x-y))) := by
  have hy := sub_ne_zero.mpr t
  refine booked_ledger P hA H B (fitting_pair P hA U V F G i j
    (show A<A+1 by linarith) p) (fun _ => rfl) (fun _ => rfl) ?_ hy (fun _ => rfl) (fun _ => rfl) ?_ hy
  · have w := Tendsto.sub (show Tendsto (fun s => gaugeRise Λ s A (u s)) atTop (𝓝 x) from U) (show Tendsto (fun s => gaugeRise Λ s A (v s)) atTop (𝓝 y) from V)
    exact w.congr fun s=> rise_sub (S s) (nodeC (u s)) (nodeC (v s))
  have w := ((appoint_as Λ hA u x).mp U).sub ((appoint_as Λ hA v y).mp V)
  exact w.congr fun s => rise_sub (zoomR Λ A s) (u s) (v s)
#print axioms visit_book
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
