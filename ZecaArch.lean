import ZecaBud
import SatinThinMill
import ZecaGem
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
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)

local notation "ξ"=> P.advocate 3 x j
local notation "EH"=>P.physicalEnergy j ξ
local notation "M"=> P.ColorHil j ξ
local notation "Ω"=> P.colorZero j ξ
local notation "Μ"=> timeMesh P.par

variable (l: List Axis)
local notation "w"=>P.roseWide j s
local notation "Roof"=>P.rosePad j s
local notation "m" t:max=>P.gum w s t
local notation "ζ"=>P.roseRoot f s l
local notation "Y" t:max =>P.clockPlate s t ζ
local notation "zc" t:max => P.centeredQ x t (Y t)
local notation "D" t:max=> (P.basePlay x f t).pivot P l
local notation "X" t:max=> P.granPos f t l
local notation "R₀"=>P.roseHub f s l
/-- ruby, recentered so that true visit position in the cover = 0.
a,b are the padding distances referred to that zero. -/
abbrev crop(f t:ℕ)(l:List Axis)(a b:ℝ):=
 P.ruby j (P.advocate 3 x j) ((P.basePlay x f t).pivot P l)
    (-P.granPos f t l)
    (a-P.granPos f t l j) (b+P.granPos f t l j)

variable {a b:ℝ}
-- uniform manipulation (same linear contraction independent of t)
def angleRise(f s:ℕ)(l:List Axis)(a b:ℝ):=
 ((P.dazzle j (P.advocate 3 x j) (-P.roseHub f s l)).comp
   ((P.buff j (P.advocate 3 x j) (a-P.roseHub f s l j)
       (b-(P.rosePad j s - P.roseHub f s l j))).comp
   (P.coffer j (P.advocate 3 x j))))
lemma angle_pay (T:(P.ColorHil j (P.advocate 3 x j)).Op):
  ‖P.angleRise j x f s l a b T‖≤‖T‖:=by
 apply le_trans (P.dazzle_pay ..)
 apply le_trans (P.buff_pay ..)
 exact P.coffer_pay ..

lemma angle_map(h:f ≤ s)(d:s≤t)(p:Roof ≤ a)(q:Roof ≤ b):
  ∃ T, P.Fired j ξ t (m t) (zc t) T ∧
       P.angleRise j x f s l a b T=P.crop j x f t l a b:=by
 let I:= m t; let A:=D t
 obtain ⟨z,y,u,g⟩:=P.rose_align j l h d
 have v:A.s=t:=(P.basePlay x f t).pivot_s P l
 have w': A.realWidth P j=bell Μ t P.roomy:=by
    unfold A; rw [Apron.pivot_w];rfl
 have J: (A.zoom P t j:ℤ)=P.roomy:= le_antisymm
     ((bell_le Μ t ..).mp (le_of_eq ((A.zoom_bell P j t v.le).trans w')))
     ((bell_le Μ t ..).mp (le_of_eq ((A.zoom_bell P j t v.le).trans w').symm))
 let c:= P.meshPose t z j
 let o:=P.meshPose t z
 let T:= P.rawCat j ξ A (P.vtile t z) c (bell Μ t I - c)
 refine ⟨T,?_,?_⟩
 · rw [y, ← P.pivot_Fax x l z]
   exact A.fired_photo P j ξ v.le z (J.symm ▸ u) (by rw [J]; exact g)
 have m':bell Μ t I=Roof:=by
    unfold bell; rw [Int.cast_natCast]; exact P.gum_tick d
 have a₁:A.realWidth P j ≤ c:=by rw [w']; exact (bell_le ..).mpr u
 have a₂:A.realWidth P j ≤ bell Μ t I - c:=by
    rw [w']
    have e:= (bell_le Μ t (z j+P.roomy) I).mpr g
    rw [bell_add] at e
    change _ ≤ bell Μ t I - bell Μ t (z j)
    linarith only [e]

 have p₀:=P.roseHub_in (s:=s) (f:=f) j l
 have p₁: 0≤ a-R₀ j:= sub_nonneg.mpr (p₀.2.trans p)
 have p₂: 0≤ b-(Roof-R₀ j):=by linarith only [q,p₀.1]
 have hZ:R₀ = X t + o:=P.granPos_line l d z y
 have h₀:R₀ j = (X t) j + c:=congrFun hZ j
 unfold angleRise T
 rw [LinearMap.comp_apply,LinearMap.comp_apply,P.coffer_rawCat]
 have e:(a-R₀ j)+c=a-(X t) j:=by linarith only [h₀]
 have e':bell Μ t I-c+(b-(Roof-R₀ j))=b+(X t) j:=by
      linarith only [m',h₀]
 rw [P.ruby_large j ξ A _ _ e e' p₁ p₂ a₁ a₂,P.ruby_turn]
 have hb:-R₀ + P.laysM (P.vtile t z) = -(X t):=by
    change -R₀+o=_
    rw [hZ,neg_add,add_assoc,neg_add_cancel,add_zero]
 rw [hb]

/-- Operator prices for clovers, aligned to exactly the same position
relative to the vacuum's spacetime clocks. At positive heat. No interpolation. -/
lemma crop_buy {A C g:ℝ}{δ:ℕ→ℝ}{z:ℕ→ℕ}
 (K:lender A C s r v δ g z P)(h:f≤ s)(O:Odessa j ζ s w P)
 (N₁:P.NightCop)
 (p:Roof≤ a)(q:Roof≤ b):
 ‖P.crop j x f r l a b‖ ≤4*(fareMin P.par.R.L (r-s)*violet P.par s A) ∧
 ‖ (↑(zoomM P.par.R.L^(r-s)):ℂ) • ((g:ℂ) • P.crop j x f v l a b-
     P.crop j x f r l a b)‖ ≤4*violet P.par s A:=by
 obtain ⟨T,hT,u⟩:=P.angle_map j x l h K.treasury.price.le p q
 obtain ⟨V,hv,y⟩:=P.angle_map j x l h (K.treasury.price.le.trans K.treasury.step) p q
 have j':=P.fires_buy j x K _ O N₁ hT hv
 rw [←u,←y,←map_smul,←map_sub,←map_smul]
 exact ⟨(P.angle_pay ..).trans j'.1,(P.angle_pay ..).trans j'.2⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.crop_buy
