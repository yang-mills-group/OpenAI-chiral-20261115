import YM.CF.Scion.Pier
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
abbrev riteL: Wave (Single (mid Q B))→ₗ[ℂ] Wave (Single (mid N B)) where
 toFun v:= fire (Thread j) G m (unionP x.val) (cartsL (switchG G).symm v)
 map_add' v w:=by unfold fire cartsL effectK; simp only [map_add, smul_add]
 map_smul' c v:=by unfold fire cartsL effectK; simp only [map_smul]; apply smul_comm
local notation "Ω"=> spar j (upMale L o m) x.val.2
local notation "Δ"=> Budget L o H.den J.den G m j x.val
local notation "θ"=> partM L j o N B m J.den x.val.2
local notation "αZ"=> riteL (j:=j) m G x
local notation "αQ"=> issue (portX (switchG G).symm (postH G ψ ho O V wd univ))
-- linear wave at all actual fields
include t ATO wk we wr wd g u W p hv hk
open Pastry
lemma beamT(X:FC (LeanV (Single (mid Q B)))) (T: FC (Single (mid Q B)))(v: spanP _ X): αZ (acts ((nursery (spar j m U) wk).eval X*T) (nest P H m x.val.1))=(Complex.exp (-(lush G P m H.den x.val))) • acts ((nursery Ω wr).eval (αQ X T * (exp (boat Δ)).val)) (nest P J (upMale L o m) x.val.2):=by
 let Z:=Δ; let C:=θ; let Y:=portX (switchG G).symm (postH G ψ ho O V wd univ); let A:=spar j m U; let D:=Ω; let H':=nest P H m x.val.1; let V':=changeM P x.val.2 (upMale L o m); have hu:= oZ P m G H J x U ψ ATO ho O V S R I W t wk we wr wd g p hv u hk
 exact glueT Y C Z A D wk wr (αZ) H' V' _ (tag_g _ wr) (hu [] []).1 (fun i j=> (hu i j).2) X T v
end YM.CF.Scion
