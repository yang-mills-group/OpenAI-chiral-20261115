import YM.CF.BProof.Temple.Cup
set_option autoImplicit false
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
open Arbor
open Wager Frost Half Leg Rush Tulip Peaks TripD Scree Tap Haro ArborW RillW
namespace Gale
attribute [local instance] Wager.measureVal Wager.billVal
open Push.SectorMeasure Phase Brace Girt Vault Paige Drapes
variable {N P M C H L:Side}{R:Patch}{r l k j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e t:ℝ}
variable {U:Grasp Y H e}
local notation "Λ" => mid M H
local notation "Λ₁"=> mid C H
variable {F:Scree.Loom (mid M H)}{F₁:Scree.Loom (mid C H)}(i:Axis)(X:ClockD R r l k){α n:ℕ}{c z:ℝ}
variable {q:Chi}{G:Ratio (mid M H) (mid C H)} {T:StepData (Domain M H) (Domain C H)} {R':GramM (mid C H)}(E: Girt.BaseL U G R' F F₁ q z)
local notation "νβ"=> R'.beta
local notation "Pβ"=>R'.J.M
variable (L0:Roof (mid M H) c e l F) (Q:Vogue.Quartz (mid M H) α c l F) (p:T.patch.Branches T.kernel SU.group)(A: SpaceM) (h:T.ratio=ratio G) (hr:T.patch=R) (hu:G.count=R.L)
local notation "λS"=> integrated U F R' F₁ G T q z A.val
local notation "D_"=> stove U F R' F₁ G T q z A.val
variable {B:Body (mid M H)} (b:Soul i X B) (V:Rider (shade (mid M H) i true X.uF) (Leg.reach G (shade (mid M H) i true X.uF) k) i G j R'.J.M A)
namespace Soul
local notation "Λv"=>poleM i X G b V
local notation "Ωv"=> Travel i Λv * Λv
local notation "Ψ"=>wince G q z Ωv
local notation "ΛX"=>wince G q z Λv
local notation "βΓ"=> fuel T νβ F
local notation "κc"=> sqR i B
local notation "f_" x:max => (denZ R' U F₁ x)
-- wear in two parts. no assumption positivity.
variable (x:Orbit (mid M H))(y:Orbit (mid C H))
local notation "XT"=>poke F x
local notation "YT"=>F₁ y
private lemma column_cross (Ht:PairD (mid M H)): Leg.Cross G j A Pβ (sqR i B Ht) (Ωv Ht):= by
 let u:=V.fee (footW i X b Ht); let q:=(V.fee (footW i X b (flipK i Ht))).q; rw [Leg.mirQ] at q; exact Leg.Cross.mul q u.p
include E
private lemma columnG (Hx:PairD (mid M H))(Xo:Nom (mid M H) (mid C H))(hp:Peaks.JointB G Xo e)(p:Phys Λ₁):
  cupL (κc Hx) (Leg.prog G j Pβ A Xo p)= pass (Ωv Hx Xo.1) p:=by
 change beamZ _ (acts _ _)=beamZ _ (acts _ _); rw [column_cross i X A b V Hx Xo (Leg.furioso j Pβ G E.power E.size Xo hp E.pe E.wear),Leg.at_house j A Pβ G E.power E.size Xo hp E.pe] -- tune argorder
lemma furnace (f:Forest (ratio G)) : pass (κc (poke F x)) (Scree.carrier U F R' F₁ G T q z A.val f x y) = T.density νβ y.1 x.1 • pass (generalizeP G q z Ωv f (poke F x) YT) (denZ R' U F₁ y):=by
 let Xo:Nom Λ Λ₁:= (seine G f q z YT (F x), F x); have hx: Peaks.JointB G Xo e:= E.trial f (F₁ y) x
 change cupL (κc XT) (T.density νβ y.1 x.1 • Leg.prog G j Pβ A Xo _) = (T.density νβ y.1 x.1) • pass ((Travel i Λv*Λv) XT Xo.1) (f_ y); rw [map_smul]; exact congrArg (T.density νβ y.1 x.1 • ·) (columnG i X E A b V XT Xo hx _)

-- pointwise counts
variable [nG:Nonempty (Forest (ratio G))]
include nG
lemma point_r : pass (κc (poke F x)) (λS x y) = T.density νβ y.1 x.1 • pass (Ψ (poke F x) YT) (denZ R' U F₁ y):=by
 let f0(a:Forest (ratio G)):= Scree.carrier U F R' F₁ G T q z A.val a x y; let F':= cupL (κc (poke F x)); let D':= capL (denZ R' U F₁ y); let v:=T.density νβ y.1 x.1; let g(a: Forest (ratio G)):= generalizeP G q z Ωv a (poke F x) YT; let X':ℝ:= (Fintype.card (Forest (ratio G)):ℝ)⁻¹; have hz(a: Forest (ratio G)): F' (f0 a) = v • D' (g a):= furnace i X E A b V x y a
 change F' (X' • (∑ i: Forest (ratio G), f0 i))= v • D' (meanS (Arbor.grove _) g); rw [Arbor.likely,map_smul,map_sum,map_smul,map_sum]; simp_rw [hz,←smul_sum]; rw [smul_comm]
end Soul
end Gale
end YM.CF.BProof.Bide
