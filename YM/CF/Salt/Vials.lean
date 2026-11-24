import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(k:ℕ)(A:Eire.Ride S)(hp:Odd G.count.val) {r0 δ v d m r w:ℝ}(hx:0<δ)
local notation "D"=> (mid N B)
local notation "Y"=> (mid P B)
local notation "F"=> reSweep G f
variable (X:Rill.Arch G δ)(u:Seat (mid P B)→E)(C: Cipher (mid P B))(Z:FC (Single (mid P B)))(t:ℕ)(P0:Meter TailB G δ)(Q:Meter Grave G δ)
local notation "H"=>cala G S hp _ hx P0 Q
local notation "W"=>switchG G
local notation "U"=> castX f
local notation "β"=> f.charge
local notation "Yv"=> spinU β f.s
lemma seir(BBv:UNI (Single Y)) : (foot G BBv.val).submatrix (switchG G).symm (switchG G).symm=BBv.val:=by ext i j; unfold foot; simp -- tune
lemma eelZ (v:∀ i, Bisca G δ true true r0 w (heal G δ Q i))(y:∀ i, OccuS G δ true false t d m r (P0 i)):
 issue (H (Haro.herb G u X) k A) ((paintR false false (tradew Y u) C).val) (Gaze u Z)=lotY false false (tradew D (scaleG G u)) (issue (H X k A) C.val Z):=by
 let h:=town_P G δ u P0 (bring hx X) (gleans S k A) t y; have h0:=vibe_s G δ u Q (bring hx X) (gleans S k A) v; rw [←Haro.hover_G] at h h0
 exact (cloakK (switchG G).symm _ _ _ _ _ _ false false _ _ _ C.val (fineShape C|>.allP) Z (seir G _).symm h h0).symm
end YM.CF.Salt
