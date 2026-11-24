import YM.CF.Stake.Shepherd
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stake
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice RG -- Teller ambiguous
open Vale
variable {K:Pressure.Teller group}{Q:RG.Patch}{R:ChartRatio group}{N B P:Side}{W:Postal}{i:ℕ} -- simplify
-- actual history step receipts
local notation "G5"=>SU.group
variable(V:Grace K Q R)
local notation "d"=> More (CSide N B)
local notation "f"=> More (CSide P B)
open CF.Newt CF.Char
structure Punt (S: RG.StepData (More (CSide N B)) (More (CSide P B)))(T:Tube SU.group S)(v x:ℝ)(G:Ratio (CSide N B) (CSide P B)) :Prop where
 cert: Cert Q K S T x
 up : T.up.Bounds T.high K.top.width K.top.paths V.W.bar
 down : T.down.Bounds T.low K.below.width K.below.paths V.W.bar
 rareH:Rare T.up
 rareL:Rare T.down
 scaleP:S.ratio= ratio G
 bill: G.count=Q.L
 height:T.high=K.top.clip
 garden:T.low=K.top.clip
 fee : |v + SU.group.slopeConstant*Real.log Q.L.val|+1 ≤ K.top.drift
 sized(F:Forest S.ratio): sizedP G5 Q K S T F
 matchP(F:Forest S.ratio)(z:Vox N B→AxisChart SU.group F)(p: Critical F T.high T.up z): ClassicalMatch F T.high T.low T.up T.down z ∧ FiniteBound F T.up T.down T.high T.low v R z V.W.peak V.W.rise 1
lemma punt_g (i:ℕ) (h:(f).val=(d).val * Q.L.val)(G:Ratio (CSide N B) (CSide P B))(p:G.count=Q.L)(x:ℝ)(Y: V.W.n≤ (d).val)(t:100*(1+radiusB x)≤ (d).val): Punt V (V.L.op i h) (V.L.mint i h) (V.L.charge i) x G:=by
 refine ⟨V.L.cert i h Y x t,V.L.mood i,?_,V.L.ring i,V.L.ring (i+1),rat_eq (p.trans (V.L.lent_L i).symm),p,rfl,rfl,V.L.bound i,(V.L.sold i).existP _ _ _ Y ,fun F z u=>?_⟩
 · rw [V.L.below]; exact V.L.mood _
 exact ((V.L.sold i).all _ _ _ Y F).2 z u
end YM.CF.Stake
