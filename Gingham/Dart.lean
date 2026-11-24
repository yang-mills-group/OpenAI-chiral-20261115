import Gingham.Ribbon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


lemma moon (r : Vantage) :
    V r = (𝓢).U (SEP 3 (foldSpace.symm r)) := by
  rw [P.uses_cart,eyes_toFace (x':= SEP _ _)]
  congr 2
  funext i
  change r i.val = (foldSpace.symm r - (foldSpace.symm r) (3:Axis) • basis 3) i.val
  simp [i.property]

lemma home_norm : inner ℂ ω₁ ω₁ = 1 := by
  rw [inner_self_eq_norm_sq_to_K,P.stone_norm]; simp


lemma home_basis : Ano 𝓢 ω₁ := by
  have h := P.heaven_hot 3 ξ
  refine ⟨h, SatinMacro.static _ _ (((𝓢).fixed _).2 h) (fun y => ?_)⟩
  rw [eyes_toFace 3 y,←P.uses_cart 3 ξ y.val.ofLp]
  exact P.cart_empty _ _ _

/-- perturb a real Euclidean position so every transverse axis sees
separation (since we start from an overlap in that sector no need for
all-rotation restoration to make this motion). -/
lemma fewest (u v : G) (q : OS.Cross 3)
    (e : inner ℂ u ((𝓢).U q v) ≠ 0) :
    ∃ z : Vantage, (∀ i : Axis,z i ≠ 0) ∧ inner ℂ u (V z v) ≠ 0 := by
  let z : Vantage := foldSpace q.val
  have he : V z = (𝓢).U q := by
    exact (P.uses_cart _ _ _).trans (congrArg (𝓢).U (eyes_toFace 3 q).symm)
  rw [← he] at e
  have hc : Continuous (fun z' => inner ℂ u (V z' v)) :=
      continuous_const.inner (P.caravan _ _ _ _ continuous_id continuous_const)
  let f (t:ℝ) (i:Axis) := if z i=0 then t else z i
  have t : Tendsto f (𝓝[>] 0) (𝓝 z) := by
    apply tendsto_pi_nhds.mpr
    intro i; by_cases h:z i=0

    · simp only [f,h,ite_true]; exact tendsto_id.mono_left nhdsWithin_le_nhds
    simp only [f,h,ite_false]; exact tendsto_const_nhds
  have g : ∀ᶠ y in 𝓝 z,inner ℂ u (V y v) ≠ 0 := hc.continuousAt.eventually_ne e
  obtain ⟨k,hk,ht⟩ := ((t.eventually g).and self_mem_nhdsWithin).exists
  exact ⟨f k,fun i=>by
      dsimp [f]; split
      · exact (show 0<k from ht).ne'
      assumption, hk⟩


/-- Useful price for both Eu and real. -/
def stood (X : (G).Op) (q : Vantage) :=
   shred ω₁ (V q (X ω₁))

lemma V_stood (X : (G).Op) (q:Vantage) :
    stood P x X q = V q (jut ω₁ X) := by
  have h : star (V q) ω₁=ω₁ := by
    rw [ContinuousLinearMap.star_eq_adjoint,P.cart_reverses,P.cart_empty]
  unfold stood jut
  rw [shred,shred,map_sub,map_smul,P.cart_empty,
    ←ContinuousLinearMap.adjoint_inner_left,
    ←ContinuousLinearMap.star_eq_adjoint,h]

/-- Fixed targets about which to place detectors in **both** conventions. -/
lemma dart {A B : ℝ≥0→(G).Op}
    (w : (𝓢).Covetails A) (c : (𝓢).Covetails B)
    {s t : ℝ≥0} (a:0<s) (b:0<t)
    (y:OS.Cross 3)
    (u: inner ℂ (jut ω₁ (A s)) ((𝓢).U y (jut ω₁ (B t))) ≠ 0) :
    ∃ r : ℝ≥0, ∃ p q:Vantage, 0<r ∧
      p 3= -(r:ℝ) ∧ q 3=r ∧ (∀ j, j ≠ 3→p j≠q j) ∧ 2*(r:ℝ)< |q 0 - p 0| ∧
      inner ℂ (stood P x (A r) p) (stood P x (B r) q) ≠ 0 := by
  obtain ⟨z,v,n⟩ := fewest P x _ _ y u

  let d : ℝ≥0 := ⟨|z 0|/2,(half_pos (abs_pos.mpr (v 0))).le⟩
  rw [P.uses_cart] at n
  obtain ⟨r,h,g,m⟩ := downshift 𝓢 ω₁ _ _ (home_basis P x) w c a b
      _ n d (show (0:ℝ) < d from half_pos (abs_pos.mpr (v 0)))
  let p(i:Axis) := if i=3 then -(r:ℝ) else 0
  let q(i:Axis) := if i=3 then (r:ℝ) else z i
  refine ⟨r,p,q,h,if_pos rfl,if_pos rfl,fun j t => ?_,?_,?_⟩
  · simp only [p,q,t,ite_false]; exact (v _).symm
  · change (r:ℝ) < |z 0|/2 at g
    simp only [p,q,show (0:Axis) ≠ 3 by decide,ite_false,sub_zero]; linarith -- fin simp neq
  rw [V_stood,V_stood]
  have ep : V p = ContinuousLinearMap.id ℂ (G).space := by
    rw [P.uses_cart]
    have ef : transverse 3 (fun i=>p i.val)=0 := by
      ext i
      by_cases g:i=3
      · subst i; rfl
      change _=(0:ℝ)
      simpa! only [p,g,ite_false] using
           transverse_eyes 3 (fun j=>p j.val) ⟨i,g⟩ --?
    rw [ef,(𝓢).uZero]
  rw [ep,ContinuousLinearMap.id_apply,P.uses_cart]
  have ef : (fun i:Trans 3=> q i.val) = fun i=> z i.val := funext fun i=> if_neg i.property
  rw [ef]; exact m

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
