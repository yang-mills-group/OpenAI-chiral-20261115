import ZecaWavelet
import ZecaOspreys
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster





open _root_.YM.ZecaSky


/-- Extensions to the countable bill. -/
structure Flotsam where
 u:ℕ→ℕ→P.Spectrum0 3→ℝ
 c:∀ m r,Continuous (u m r)
 n:∀ i r x, 0≤u i r x
 ok:∀ i,Tendsto (fun r=>∫ x,u i r x∂P.pillars 3) atTop (𝓝 0)

def noneOut:P.Flotsam where
 u:=fun _ _ _=>0
 c:=fun _ _=>continuous_const
 n:=fun _ _ _=>le_rfl
 ok:=fun _=>by simp

/-- A.e. electable. -/
def Wrack (A:P.Flotsam)(T:ℝ): Prop :=
 ∀ g:ℝ→ℝ,Gait g →
  ∃ seq:ℕ→ℕ, P.Nepenthe seq x ∧
    (∀ i,Tendsto (fun j=>A.u i (seq j) x) atTop (𝓝 0)) ∧
    ∃ (d:ℕ)(K:ℝ),0<K ∧ ∀ i t,0<t →
         g (P.jetS (seq i)*t) ≤ g (P.jetS (seq i)*T) * K * spur d t

variable {C:ℝ}
 (W₀:5∣P.par.R.L.val)
 (A₀:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k)

include W₀ A₀
lemma elect_wrack (T:ℝ)(ht:0<T) (A:P.Flotsam):
 ∀ᵐ x∂P.pillars 3, P.Wrack x A T:=by
 haveI: Nonempty Plume_LocalFieldBounds:= ⟨⟨0,fun _=>1,by norm_num⟩⟩
 obtain ⟨B,b,y,f,q⟩:= P.seawall T ht
 obtain ⟨L₀,t⟩:=exists_surjective_nat (ℕ × Plume_LocalFieldBounds × Plume_LocalFieldBounds × Cover × Cover)
 let v(m):= P.bendMiss (L₀ m).1 (L₀ m).2.1 (L₀ m).2.2.1 (L₀ m).2.2.2.1 (L₀ m).2.2.2.2
 let d(i n:ℕ)(x):= A.u i (y n) x + v i (y n) x
 have go(i):Tendsto (fun n=>∫x,d i n x∂P.pillars 3) atTop (𝓝 0):=by
    have vo:Tendsto (fun r=>∫x,v i r x∂P.pillars 3) atTop (𝓝 0):=P.bending_go _ _ _ _ _ W₀ A₀
    have u:= ((A.ok i).add vo).comp f
    rw [add_zero] at u
    exact u.congr (fun n=>
     (integral_add ((A.c i _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
       ((P.mistake_live 3 z' _ _ _ _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm)
 have h:= waves (P.pillars 3) d
    (fun i n=> (A.c i (y n)).add <| P.mistake_live 3 z' (y n) _ _ _ _)
    (fun i n x=> add_nonneg (A.n ..) (norm_nonneg _))
    go
      -- need separate
 refine h.mono fun x hh g a=>?_
 obtain ⟨j,w,u,l⟩:= hh.groom (P.jetS ∘ y) (fun n=> P.jetS_pos _) ht b q g a
 refine ⟨_,⟨f.comp w,?_⟩,?_,l⟩
 · intro k p q c d₀
   obtain ⟨i,b'⟩:= t (k,p,q,c,d₀)
   have hi: Tendsto (fun n=>v i (y (j n)) x) atTop (𝓝 0):=
     squeeze_zero (fun n=>norm_nonneg _) (fun n=>le_add_of_nonneg_left (A.n _ _ _)) (u i)
   unfold v at hi
   rw [b'] at hi
   exact hi
 · intro i
   exact squeeze_zero (fun n=>A.n _ _ _) (fun n=>le_add_of_nonneg_right (norm_nonneg _)) (u i)
#print axioms elect_wrack
