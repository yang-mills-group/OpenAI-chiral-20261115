import ZecaLaputa
import ZecaCP4
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

open DoseTravel Set

local notation "MH"=> Hierarchy.Seld.Zeca.Moment

open Hierarchy.Seld.Poin
open Boundary

structure Boom (seq:ℕ→ℕ)(Y:ℕ→P.Apron)
   (F:P.Nib 3 ξ)(scale:ℕ→ℂ):Prop where
 line:P.NibLine 3 (P.advocate 3 x 3) F Y 1
 grows: ∀ᶠ r in atTop,scale r ≠ 0
 sky:Tendsto seq atTop atTop
 soar:P.Mach x F scale seq

variable
 {K:P.Register} {c r:ℕ→ℕ}
 {R:P.Ellis 3 x} {i₀:ℕ}{F U:SampleDose}
 {Y:ℕ→P.Apron} {n:ℕ→ℕ} {w:Lead.Clan→Prism}
 {V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
 {f k:ℕ} {X:P.HandleWith x c r Y n} {D:P.Cilium x}

/-- small amount of extra data to keep out of election. -/
structure Lark (seq:ℕ→ℕ)(f k:ℕ)(Y:ℕ→P.Apron) : Prop where
 meshy:5∣P.par.R.L.val
 purple:P.Nepenthe seq x
 cinema: ∃ (A C:ℝ)(u:ℕ→ℕ)(y:ℕ→(ℕ×ℕ)→ℝ)(uf:StrictMono u)(z:ℕ→ Coalition),
       Y=P.cinema x f k u y z uf ∧ Skyways P f k A C (P.rewardK f k) u y

#print Lark

lemma spunUv {seq:ℕ→ℕ}
 (T:P.Shell K c r x R i₀ F U Y n w V f k X D) (h:P.Lark x seq f k Y)
 (B:P.Nib 3 (P.advocate 3 x 3))
 (l:P.NibLine 3 (P.advocate 3 x 3) B Y 1):
 ∃ scale, P.Boom x seq Y B scale:=by
 obtain ⟨W₀,sky,A,C,u,y,uf,z,rfl,p⟩:=h
 have i:=T.scores.incense
 have a0:P.NightCop:=i.2.2.2.2.2.2.1
 have j:=P.shoot_again x _ B (i.2.2.2.2.2.2.2.2 w).cinema l
 obtain ⟨scale,pos,nick⟩:=P.tileLess x B uf y z l p a0 j
 exact ⟨scale,l,pos,sky.sky,mach W₀ R sky
      (nick.loftIt l.bottle (P.inkLoss_zero A) sky.sky)⟩

#print axioms spunUv
