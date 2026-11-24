import YM.Sextet.PaintPair
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
section Born
open Tapestry.Altitude Tapestry.Exhibition
variable (P:Spine) (j:Axis) (x:P.Spectrum0 j) (t:ℕ)

theorem birth_poly {f:P.Test} (h:P.birthF j t f) :
    pinhole _ t f∈P.reachable j t := by
  obtain ⟨b,rfl⟩:=h
  exact P.pointed j b

/-- Whenever we use `viewF` on a test with Birth ticket, this really is even
the vector of the corresponding priced resolution polynomial. -/
theorem birth_poly_word (K:P.Register) {f:P.Test} (h:P.birthF j t f) :
    P.operatorWord K j x ⟨pinhole _ t f,P.already j (P.birth_poly j t h)⟩=
      P.viewF j x t h := by
  refine (P.realizes K j x _ t (P.birth_poly j t h)).trans ?_
  refine P.usesFormula K j x (pinhole _ t f) _ (P.emmigrant j t h) ?_
  rw [P.documented j t h]
  exact ((vistaDressing _ _ (P.talks K)).outcrop (auxiliaryPad _) t _).symm

lemma birth_scale {f:P.Test} (p:P.birthF j t f) (a:ℂ) : P.birthF j t (a • f) :=
  (P.birthTicket j t).smul_mem a p

lemma view_scale {f:P.Test} (p:P.birthF j t f) (a:ℂ) :
    P.viewF j x t (P.birth_scale j t p a)= a • P.viewF j x t p := by
  have h:=map_smul (P.ticketView j x t) a ⟨f,p⟩
  exact h

lemma view_zero : P.viewF j x t (f:=0) (show P.birthF j t 0 from (P.birthTicket j t).zero_mem)=0 := by
  have h:=map_zero (P.ticketView j x t)
  exact h

variable (A:P.Apron) (f:Vantage→ℝ) (h:HasCompactSupport f)
   (W:Cover→ (P.ColorHil j x).space)
   (q:∀ p,P.grid t p∈tsupport f→ ∃ k:P.birthF j t (P.aimMark A t p),P.viewF j x t k = W p)
local notation "z" p:max => (f (P.grid t p):ℂ)
include q
lemma birth_pointweighted (p:Cover) :
    ∃ a:P.birthF j t (z p • P.aimMark A t p), P.viewF j x t a=z p • W p := by
  by_cases u:f (P.grid t p)=0
  · simp_rw [u,Complex.ofReal_zero,zero_smul]
    exact ⟨(P.birthTicket j t).zero_mem,P.view_zero j x t⟩
  obtain ⟨k,b⟩:=q p (subset_closure u)
  exact ⟨P.birth_scale j t k _, (P.view_scale j x t k _).trans (congrArg _ b)⟩

include h
lemma paint_via_birth :
    ∃ a:P.birthF j t (P.paintMark A t f),
      P.viewF j x t a = (P.macroTick t)^4 • ∑ᶠ p,z p • W p := by
  choose k b using P.birth_pointweighted j x t A f W q
  unfold paintMark; simp_rw [P.fine_sum t h]
  have g:=P.birth_sum j t _ k (P.fineSites t h)
  exact ⟨P.birth_scale j t g _,by
    rw [P.view_scale j x t g,P.sextet_view_sum j x t _ k]
    simp_rw [b]
    exact (algebraMap_smul (R:=ℝ) ℂ _ _)⟩
end Born

section Forward
variable (P:Spine) (x:P.Spectrum0 3) (Z:Lead.Clan) (s n t:ℕ)
    (f:Vantage→ℝ) (h:HasCompactSupport f) (a:s≤t)
local notation "ξ" => P.advocate 3 x 3
local notation "w" => P.transportWidth s n 3
local notation "A" => P.macroBody Z s n

/-- The reflected tests here begin as probes in the strict future with footprint -
this theorem identifies *their actual vector*, before opposition, at each grid. -/
theorem paint_forward (q:AfterWall 3 (P.transportWidth s n 3) 0 f) (h:HasCompactSupport f) (a:s≤t) :
    ∃ b:P.birthF 3 t (P.paintMark A t f),
      P.viewF 3 ξ t b=P.fineSense x Z s n 0 f t :=
  P.paint_via_birth 3 ξ t A f h (P.gridWall x Z s n 0 t)
    (fun i g=>P.gridWall_view x Z s n t i a ((P.transportWidth_pos ..).le.trans
      (sub_pos.mp (q _ g)).le))

theorem fineSense_turn :
    P.fineSense x Z s n 0 (turnSmear 3 f) t=P.fineSense x Z s n 0 f t := by
  unfold fineSense
  refine congrArg ((P.macroTick t)^4 • ·) <|
     finsum_eq_of_bijective _ (turnΩ 3).bijective (fun y=>?_)
  rw [P.oppose_grid,P.gridWall_turn];rfl

theorem realSense_turn :
    P.realSense x Z s n 0 (turnSmear 3 f)=P.realSense x Z s n 0 f := by
  let F:=fun y=> (f y:ℂ) • P.vectorWall x s n Z 0 y
  refine Eq.trans ?_ (turnΩ_integral 3 F)
  unfold F; simp_rw [P.vectorWall_turn];rfl

/-- Explicit strong convergence of realized grid vectors: an eventual *actual*
`viewF` representative (equivalently `operatorWord` on these resolution pins)
for each term, strong limit in this same representation. -/
theorem paint_walk (J:P.Ellis 3 x) (q:AfterWall 3 w 0 f) (p:Continuous f) (h:HasCompactSupport f) :
    (∀ᶠ t in atTop, ∃ b:P.birthF 3 t (P.paintMark A t f),
      P.viewF 3 ξ t b=P.fineSense x Z s n 0 f t) ∧
    Tendsto (P.fineSense x Z s n 0 f) atTop (𝓝 (P.enter 3 ξ (P.realSense x Z s n 0 f))) :=
  ⟨(eventually_ge_atTop s).mono (fun t a=>P.paint_forward x Z s n t f q h a),
   P.smoothed_motion x Z s n _ f J p h⟩
end Forward
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
