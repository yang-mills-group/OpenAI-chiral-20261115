import SatinPP.Logistic
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 320000
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
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)

local notation "ξ"=>P.advocate 3 x 3
local notation "G"=>P.ManyF 3 ξ
local notation "H"=>P.ColorHil 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "E" => (P.physicalEnergy 3 ξ).E
local notation "ε" => P.seasons 3 ξ
local notation "ℜ"=>Lead.Clan
variable (w:Lead.Clan→Prism)
 (V:∀j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j))
 (A:ℕ→P.Apron)(c s n:ℕ→ℕ)
local notation "W"=>P.soldTrumpet A c s n w
local notation "W₁" a:max i:max => ((W a i).kiss P 3)
local notation "st" i:max => c (n i)
variable (F U:SampleDose)
local notation "Φ" a:max t:max i:max=> P.prepared t (W₁ a i) F
local notation "Ψ" b:max t:max i:max=> P.prepared t (W b i) U
variable (l u q t μ:ℝ)
local notation "K₁" a:max i:max r:max => P.gridRun x r (W₁ a i) F l u
local notation "K₂" a:max i:max r:max => P.gridRun x r (W a i) U q t
variable (D:P.Concert x)(Y:Lead.Clan→Silk.Spool (P.ManyF 3 (P.advocate 3 x 3)))
local notation "V₁" a:max => P.leaderW x w D a F l u
local notation "V₂" a:max => P.laterW x w D a U q t
variable (g h:ℕ)

variable {P x A c s n w V D Y F U l u q t μ g h}
 {X:P.HandleWith x c s A n}
variable (J:P.Ellis 3 x)(B:P.ThinArmada x A c s n w X V g h)
variable (M:P.Matinee x D V A w)
local notation "b₀" a:max i:max=>P.sold_birth x A c s n w a i X
local notation "χ" a:max i:max=>P.cradleH x (W a i) (b₀ a i)

include J B
lemma ask_route (a:Lead.Clan) (e:0<μ)
 {d:Vantage→ℝ}(p:∀y, μ ≤ d y)(r:Continuous d):
 Routed (fun i k=>P.askW x d F k (χ a i))
        (P.readW x d F (P.profilesZ x V w a)) :=
   ask_out F p r e (B.energy a).1 J
       (P.illuminate_bank x A c s n w V g h X B a)
       (fun i=>χ a i) (fun i=>cradlePositive _ _) (B.heated_points a μ e).1



include M
lemma near_route (a:Lead.Clan) (r:Strict l u F)(lu:l<u):
 Routed (fun i k=>star (K₁ a i k) (ω)) (star (V₁ a) (Ω)):=by
 obtain ⟨z,e,_,j⟩:=strict_gap r lu
 let d(p:Vantage):=max z (u-p (3:Axis))
 have s:P.readW x d F (P.profilesZ x V w a) = star (V₁ a) (Ω):=by
    have k:=matNear M F a r 0
    rw [(P.seasons 3 ξ).eZero, ContinuousLinearMap.id_apply] at k
    rw [k]
    unfold readW DoseTravel.beam
    congr 1 with p
    by_cases v:p∈tsupport F.val
    · unfold nearP d; dsimp only; rw [max_eq_right (j p v).2]; simp
    simp [image_eq_zero_of_notMem_tsupport v]
 rw [←s]
 have D₀:= strict_ready r lu (P.invertWidth _ (B.slender a) 3)
 refine (ask_route (F:=F) J B a e (d:=d) (fun _=>le_max_left ..) (continuous_const.max
       (continuous_const.sub (continuous_apply _)))).transfer (D₀.mono fun i b k=>?_ )
 exact (run_asked (b₀ a i) (SetPanel.ofReady b)
   (D:=d) (fun p v=>max_eq_right (j p v).2)).symm

lemma far_route (a:Lead.Clan) (r:Strict q t U)(lu:q<t):
 Routed (fun i k=>(K₂ a i k) (ω)) ((V₂ a) (Ω)):=by
 obtain ⟨z,e,_,j⟩:=strict_gap r lu
 let d(p:Vantage):=max z (p (3:Axis)-q)
 have s:P.readW x d U (P.profilesZ x V w a) = (V₂ a) (Ω):=by
    have k:=matFar M U a r 0
    rw [(P.seasons 3 ξ).eZero, ContinuousLinearMap.id_apply] at k
    rw [k]
    unfold readW DoseTravel.beam
    congr 1 with p
    by_cases v:p∈tsupport U.val
    · unfold farP d; dsimp only; rw [max_eq_right (j p v).1]; simp
    simp [image_eq_zero_of_notMem_tsupport v]
 rw [←s]
 have D₀:= strict_ready r lu (B.slender a 3)
 refine (ask_route (F:=U) J B a e (d:=d) (fun _=>le_max_left ..) (continuous_const.max
       ((continuous_apply _).sub continuous_const))).transfer (D₀.mono fun i b k=>?_ )
 exact (run_ask (b₀ a i) (SetPanel.ofReady b)
   (D:=d) (fun p v=>max_eq_right (j p v).1)).symm


#print axioms near_route
#print axioms far_route
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
