import YM.CF.Scion.Buckle
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel
variable {L N Q B:Side}{j:ℕ}{o:Odd L.val}{e d:ℝ}{Y:Pricing j L o (Thread j)}(P:Grasp Y B e)(m:Male)
variable (G:Ratio (mid N B) (mid Q B))(H:Aim (mid Q B))(J:Aim (mid N B))(x:Rent0 G e)(U:Pane (mid Q B))(ψ:cro G d)(ATO: ψ.val=(unionP x.val,Tulip.profile U))(ho:Odd G.count.val)(O: Meter TailB G d)(V: Meter Grave G d)
-- single authentic Path valuation fertility
variable {K':Type*}(S:WG K')(R:K'→Male)(I:K')(W:R I=m)(t:S I (mid Q B) (Tulip.profile x.val.1)=H.den x.val.1)
variable (wk:IsStarProjection (spar j m U))(we:IsStarProjection (spar j m x.val.1))(wr:IsStarProjection (spar j (upMale L o m) x.val.2))(wd: chillF G d ψ=ψ)
variable (g:fulfills G ho d (j:=j) R S I O V ψ)(p:0<e)(hv:G.count=L)(u:P.roundZ≤ ((mid N B)).val)(hk:‖coatG L o j G m H.den x.val‖<1) -- tune order
local notation "Ω"=> spar j (upMale L o m) x.val.2
local notation "Δ"=> Budget L o H.den J.den G m j x.val
local notation "θ"=> partM L j o N B m J.den x.val.2
local notation "αZ"=> riteL (j:=j) m G x
local notation "αQ"=> issue (portX (switchG G).symm (postH G ψ ho O V wd univ))
-- linear wave at all actual fields
include t ATO wk we wr wd g u W p hv hk
-- unprojected rank weighted with I, charge cancels W.
variable (F: FC (Single (mid Q B)))(ℍ:GramM (mid Q B))(A:Scree.Loom (mid Q B))(Z:Orbit (mid Q B))(P':Pride (mid N B))
lemma wages_s (hM:ℍ.J.M=m)(hF:ℍ.J.P=H)(hS:A Z=U)(hz: acts F (Complex.exp (-pigment ℍ.J.I x.val.1) • nest P H m x.val.1)= Complex.exp (-pigment ℍ.J.I U) • nest P H m U) : let Y':=issue (portX (switchG G).symm (postH G ψ ho O V wd univ)); αZ (denZ ℍ P A Z)= Complex.exp (ℍ.H0 Z.1-Cour.shipA G P m H.den ℍ.J.I P' x.val-pigment P' x.val.2) • acts ((nursery Ω wr).eval (Y' (ℍ.board Z).val F * (exp (boat Δ)).val)) (nest P J (upMale L o m) x.val.2):=by
 intro C₀; rw [show denZ _ _ _ _ = Complex.exp (ℍ.H0 Z.1) • acts ((nursery _ wk).eval (ℍ.board Z).val * F) (Complex.exp (-pigment ℍ.J.I x.val.1) • nest P H m x.val.1) from ?_]; swap
 · rw [act_mul,hz,map_smul,smul_smul, ←Complex.exp_add,← sub_eq_add_neg]; unfold denZ GramM.betaL relV; rw [hM,hF,hS]; rfl
 rw [map_smul,map_smul,map_smul, show αZ (acts ((nursery _ wk).eval _ * F) _) = _ from beamT P m G H J x U ψ ATO ho O V S R I W t wk we wr wd g p hv u hk (ℍ.board Z).val F ((fineShape _).allP),smul_smul,smul_smul, ← Complex.exp_add, ←Complex.exp_add]; unfold Cour.shipA; congr 2; abel
end YM.CF.Scion
