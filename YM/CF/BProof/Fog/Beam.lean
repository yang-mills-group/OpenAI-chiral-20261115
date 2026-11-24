import YM.CF.Continuum.Billhead
import YM.CF.Continuum.LaurelBeam
import YM.CF.BProof.Physical
/-!
 # Pressure bounds transfer, at the same pivot, and extensive alarms

 VOLUME_PROOF proof of Lem Absolute Fock uses entrywise row-sums then compression,
 for a trace-norm bound. Here we use the Project's `Billhead` formalization in which one
 instead *directly* estimates the compressed second-quantized matrix (on the VERY SAME
 row decompositions to the exterior creation algebra `Window.thermalCap`). Gives the same
 volume price, unlike some of the project's other norm bounds.
 Density difference in D-fit uses the smooth dependence of the board on **masked** hub
 & force inputs; we use the available `LaurelBeam` estimates (also taking differences on
 these same masks, with explicit bounds; do pay cutoff volume). Extend the constant to
 work also when budget-distance times volume isn't small. In either case we can retain an
 explicit bill with exponent extensive. No connection through a varying Gauge field or
 dropping the common offset prescription.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Graph Graph.Diff
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
namespace Unfit
variable {m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z β:ℝ}{P:Grasp Y B e}
variable (A U:GramM (mid m B))(S:Loom (mid m B))(Hm:P.roundZ ≤ (mid m B).val)(H:Roof _ u e n S)
local notation "Π" => mid m B
variable (he:U.path.Bounds U.funds μ D L')(hD:0≤D)(hw:0≤U.beta)(hp:U.beta≤β)(W:Ledger R v v r C U)(ht:0≤r)(tA:1≤R)(hC:0≤C)
include he hw hD hp Hm H W ht tA hC
abbrev volt (n:Side):ℝ:=(More n).val^4
def cost (n:Side)(p:BudgetPoint)(b v C D L':ℝ):=taxY (More n) b p.threshold D L'+flagBill n v v C
local notation "I" => (cost (mid m B) U.p β v C D L')
lemma upper (x:Orbit (mid m B)) : ‖BProof.ket₀ U P S x‖ ≤ Real.exp I :=by
 apply (extensive_price U S H P Hm W he ht tA hC hw x).trans
 rw [cost,Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by unfold taxY; apply add_le_add_left; apply mul_le_mul_of_nonneg_right hp; have ht:= U.p.threshold_pos; positivity)) (Real.exp_pos _).le
-- replenish
variable (V:Ledger R v v r C A)(x:Orbit (mid m B))(hU:A.J=U.J)(hV:A.p=U.p)(gf:A.path=U.path)(gh:A.funds=U.funds)(pp:A.beta=U.beta)(hv0:A.slip=0)(hu0:U.slip=0)(wκ:0≤k)(wX:ξX A U k R)(ev:0≤v)
include V hU hV gf gh pp hv0 hu0 wκ wX ev
lemma tract : ‖BProof.ket₀ A P S x - BProof.ket₀ U P S x‖ ≤ Real.exp I * (4*volt Π*k):=by
 let p:=past U x.1; have hg: past A x.1=p:=by unfold past p; rw [gf,gh,hV,pp]
 change ‖recX P A _ _-recX P U _ _‖ ≤ _; rw [porch,porch,hg,←(show p=past U x.1 from rfl),←smul_sub]; let C':=flagBill (mid m B) v v C; let E:=taxY (More (mid m B)) β U.p.threshold D L'; let T:=Real.exp C'
 have H'(A:GramM (mid m B)): IsStarProjection (spar j A.J.M (S x))∧ ‖changeM P (S x) A.J.M‖=1:= ⟨(P.broadness _ Hm A.J.M).projection _ (H.paid x),(sea_g Hm _ (H.paid x) _).2⟩
 let Fα:= beam A P S x; let Fβ:= beam U P S x; let L_:=mile j A S x - mile j U S x
 let B_:=cab A P S x; have hu:Fα-Fβ=acts L_ B_:=by unfold L_; rw [act_sub]; unfold Fα Fβ Graph.beam; rw [←hU]
 let T':=rankV Π k; have ht':0≤T':=by unfold T' rankV; positivity
 have he': ‖L_‖ ≤ T*(4*T'):=by
    by_cases hα:T'≤1/2
    · unfold L_; refine (mile_diff A U tA j hV hv0 hu0 hU V W S x wX hα (H' A).1 ht ev).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le); change 3*T'≤4*T'; linarith
    unfold L_; refine (norm_sub_le ..).trans ((add_le_add (extensive_mile V _ ht tA hC (H' A).1) (extensive_mile W _ ht tA hC (H' U).1)).trans ?_); change T+T≤T*_; have hT:0≤T:=(Real.exp_pos _).le; nlinarith
 have hQ: p ≤ Real.exp E:=by
    apply Real.exp_monotone; apply (neg_le.mp (energy_low _ _ _ he hw x.1)).trans; unfold E taxY; apply add_le_add_left; apply mul_le_mul_of_nonneg_right hp; have hh:= U.p.threshold_pos; positivity
 change ‖p • (Fα-Fβ)‖ ≤ _
 rw [hu,norm_smul,Real.norm_of_nonneg (show 0 ≤ p from (Real.exp_pos _).le)]
 refine (mul_le_mul hQ (show ‖acts L_ B_‖ ≤ T*(4*T') from (spentS _ _ _).trans (by rw [(show ‖B_‖=_ from (H' A).2),mul_one]; exact he')) (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_; rw [cost,Real.exp_add]; unfold E T C' T' rankV volt; ring
end Unfit
end YM.CF.Window
