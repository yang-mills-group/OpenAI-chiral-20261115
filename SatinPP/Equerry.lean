import SatinPP.Oats
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

local notation "H"=> P.ColorHil 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Δ"=> P.truck 3 ξ
local notation "ω"=> P.colorZero 3 ξ

variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:ℒ→ Prism)(g h:ℕ)
variable (T:P.HandleWith x c r A n)
local notation "W"=> P.soldTrumpet A c r n w
local notation "B[" a "," i "]"=> P.sold_birth x A c r n w a i T
local notation "η"=>P.enter 3 ξ

variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)
variable (b:Bool)(q:ℝ)(F:SampleDose)
local notation "Xᵦ"=>P.pastureGrid x A c r n w T b
local notation "ν"=>P.wave x V w b q
include R J
local notation "Ω₁"=> P.advocate 3 x 3
variable {d y z:ℝ}(df:0<d)(yp:0<y)(u:IsPaid b q F)(e:0<q)
 (Q:P.Flare x V w b q F d y z)

omit R J
/-- Strict norm pressure bounds for every combination on this side of the wall.
`clock` is the continuum unit used for original positions. -/
structure Thrust {I:Hilbert}(H':ℝ≥0→I.Op)(U:I.Op)(d l:ℝ)(v:I) :Prop where
 sideways:dist v (U v) ≤ l*((13/2)/d)
 depth: l*((27/4)/d) ≤ dist v (H' l.toNNReal v)
abbrev SpurRaw (t':ℕ)(j:Axis)(n':ℤ):=(Δ) (P.vtile t' (wheel j n'))
def HardRide (L:ℒ→H) (t':ℕ)(d ϵ:ℝ):Prop:=
 ∀j:Axis,j≠3→∀n':ℤ,0<P.gradeZ t' n' → P.gradeZ t' n' ≤ϵ → ∀m,fanSet m→
    Thrust (S).E (P.SpurRaw x t' j n') d (P.gradeZ t' n') (ounce m L)
def SoftRide (L:ℒ→G) (d ϵ:ℝ):Prop:=
 ∀j:Axis,j≠3→∀l:ℝ,0<l → l ≤ϵ → ∀m,fanSet m→
    Thrust (Θ).E (Γ (aglow j l)) d l (ounce m L)


lemma sweat {I:Hilbert}(H':OS.Semigroup I 3)(C:ℝ){d y:ℝ}(e:0<d)(g₁:0<y):
 ∃ ϵ>0, ∀ l:ℝ,0<l→l≤ϵ→∀v:I,‖v‖≤C→ 7*y≤dist v (H'.E (d*y).toNNReal v)→
   l*((27/4)/d) ≤ dist v (H'.E l.toNNReal v):=by
 have t:=bow (M:=C) H' (mul_pos e g₁) (show 0<(27/4)/d from by positivity) (show (27/4)/d<(7:ℝ)/d from div_lt_div_of_pos_right (by norm_num) e)

 obtain ⟨ϵ,p,u⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp t
 exact ⟨ϵ,p,fun l g h v₀ v₁ v₂ => u (a:=l) ⟨g,h⟩ v₀ v₁ ((show d*y*(7/d)=7*y from by field_simp).trans_le v₂)⟩
include R J df yp Q e
lemma hard_arch (vp:0<z) {r':ℝ}(f:0<r')(W':CanMove b F q r' f) :
 ∃ϵ>0, ∀ᶠ i in atTop,∀ t≥i,P.HardRide x (Xᵦ F i t) t d ϵ:=by
 obtain ⟨s,a,k⟩:=P.sharp_pitch x V A c r n w g h T R J b q F df e Q vp f W'
 obtain ⟨C,Z⟩:=P.hutch_hold x V A c r n w g h T R J b q F yp W'.wall e Q
 obtain ⟨δ,p,U⟩:= sweat S C df yp
 refine ⟨min s δ,lt_min a p,?_⟩
 filter_upwards [k,Z] with i km zm t t_i j j0 index hi le' m m_p
 let l:=P.gradeZ t index
 constructor
 · exact stable_div m _ (Xᵦ (bike (footfall j) F l) i t)
     (P.SpurRaw x t j index) hi (fun a =>P.harvest_bike x _ B[a,i] t b F j j0 index)
     (km t t_i _ hi (le'.trans (min_le_left ..)) j j0 m m_p)

 exact U l hi (le'.trans (min_le_right ..)) _ (zm t t_i m m_p).1 (zm t t_i m m_p).2

omit J
include u
lemma soft_arch (vp:0<z)(p:1≤q) :
 ∃ϵ>0,P.SoftRide x (P.wave x V w b 1 F) d ϵ:=by
 have eq:P.wave x V w b 1 F= ν F:= by
    funext a
    unfold wave DoseTravel.beam
    refine integral_congr_ae (Eventually.of_forall fun r'=>?_)
    by_cases g:F.val r'=0;· simp [g]
    have t:=u r' (subset_closure g)
    dsimp only [trails_LocalFieldBounds,morning];rw [max_eq_right (p.trans t),max_eq_right t]
 rw [eq]
 obtain ⟨C,c₀⟩:=hutch_cap (ν F)
 obtain ⟨ϵ,v,k⟩:=sweat (Θ) C df yp
 refine ⟨min ϵ (d*z),lt_min v (by positivity),fun j j' l p' z₀ m m₀=>?_⟩
 let Y:=ounce m (ν F)
 constructor
 · have h₀:=Q.spire j j' l p' (z₀.trans (min_le_right ..)) m m₀
   rw [P.wave_bike x V w b q R.cinema m e F j j' l, norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr p'),←dist_eq_norm,footfall,aglow_line,mul_one] at h₀
   exact ((inv_mul_le_iff₀ p').mp h₀).trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by norm_num:(11:ℝ)/2≤13/2) df.le) p'.le)
 · exact k l p' (z₀.trans (min_le_left ..)) _ (c₀ m m₀)
    ((mul_le_mul_of_nonneg_right (by norm_num : (7:ℝ)≤29/4) yp.le).trans (Q.swipe _ m₀))
#print axioms hard_arch
#print axioms soft_arch
