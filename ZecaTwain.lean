import ZecaLatticeFieldEstimates
import YM.SU5.Aria.Wings
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E

variable (D:P.Apron)
local notation "ET" => (P.seasons j x).E
local notation "G" => P.ManyF j x


local notation "K"=>P.wealth j x
local notation "η"=>P.enter j x
local notation "C"=>P.cartage j x

section film
variable {U:Hilbert}{I I₀: Type*} {l:Filter I} {k:Filter I₀}
variable {f g:I→U.Op} {T A:U.Op}



lemma glaze_star {I:Type*}{l:Filter I}[l.NeBot]
 {U:Hilbert}{f:I→U.Op}{T A:U.Op}
 (h:Glaze_LocalFieldBounds U l f T)(p:Glaze_LocalFieldBounds U l (fun i=>star (f i)) A):A=star T:=by
 ext1 x
 change A x= ContinuousLinearMap.adjoint T x
 apply ext_inner_right ℂ
 intro y
 rw [ContinuousLinearMap.adjoint_inner_left]
 have a:= (p.seeks x).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=y))
 have b:= (tendsto_const_nhds (x:=x)).inner (𝕜:=ℂ) (h.seeks y)
 exact tendsto_nhds_unique a (b.congr (fun i=> (ContinuousLinearMap.adjoint_inner_left (f i) y x).symm))
open Casting
lemma ruby_twin (p:Vantage)(a b:ℝ):
 star (P.ruby j x D p a b)=
   P.ruby j x (D.kiss P j) (mirrorΩ j p) b a:= by
 have v:∀ t,star (ET t)=ET t:=(P.seasons j x).sym
 unfold ruby
 rw [star_mul,star_mul,P.lives_twin,v,v,mul_assoc,Apron.kiss_width]
lemma ruby_twin0 (a b:ℝ):
 star (P.ruby j x D 0 a b)=
   P.ruby j x (D.kiss P j) 0 b a:=by
 rw [P.ruby_twin,show mirrorΩ j (0:Vantage)=0 by ext i; simp [mirrorΩ]]
abbrev twinNib (F:P.Nib j x):P.Nib j x:=fun a b=>star (F b a)

namespace Iguana
variable {P j x} {F Z:P.Nib j x} {Y:ℕ→P.Apron}
lemma mk' (h:P.NibLine j x F Y 1)
 (q:P.NibLine j x Z (fun i=>(Y i).kiss P j) 1):
 P.Iguana j x F Y:=by
 refine ⟨h.pay,h.thin, fun a b p r => ⟨h.dyeOne p r,?_⟩⟩
 have hv:=h.dyeOne p r
 have g:Glaze_LocalFieldBounds (P.ManyF j x) atTop
        (fun i=>star (P.ruby j x (Y i) 0 a b)) (Z b a):=
    (q.dyeOne r p).congr' (Eventually.of_forall (fun i=>(P.ruby_twin0 j x (Y i) a b).symm))
 rwa [←glaze_star hv g]
lemma twin (h:P.Iguana j x F Y):P.NibLine j x (P.twinNib j x F) (fun i=>(Y i).kiss P j) 1:=by
 refine ⟨?_,h.thin,?_⟩
 · obtain ⟨p,d,g,u⟩:=h.pay
   exact ⟨p,d,g,fun t v f=>(norm_star _).trans_le (u t v f)⟩
 intro a b p q
 refine (h.dye b a q p).mir.congr' (Eventually.of_forall (fun i=>?_))
 simp only [Pi.one_apply,one_smul,P.ruby_twin0]
end Iguana
#print axioms Iguana.mk'
