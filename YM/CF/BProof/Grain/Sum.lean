import YM.CF.BProof.Grain.Pole
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Grain
open Bake Cupboard Cupboard.BasisSt Sour Tap Glyph Digit BondL Axial
open scoped YM.CF.Sour.Axial
variable {R:Patch} (P_:BudgetPoint){x:ℝ}(F G D H:ℝ→ℝ)(h A a b c d:ℝ)
local notation "Pz"=>hall_P P_ -- .B vs .radius
local notation "cnt" => cQ
-- feepad arithmetic rank2 & 1.Note variant takes |
local notation "gL"=> Scales.g SU.group R.L
local notation "zP"=> rainX R 1
local notation "zD"=> rainX R 2
open SupportP
lemma grow_x (u:0<h)(p:1≤h)(ha:0<A)(v_:ForceL P_ h A a b c)(ha0:0<a)(v0:a≤1)
 (hf:sizeK R.L 2 F)(hg:sizeK R.L 1 G)(hd:sizeK R.L 2 D)(hh:sizeK R.L 3 H)(hv:0<d)(ht:∀ᶠ x in atTop, d*dleaf R.L x ≤ D x ∧ D x ≤ F x):∃ (m: (x:ℝ)→Digit.Cash (hall_P P_ x)),sizeK R.L 1 (fun x=>(m x).Γr) ∧ (∀ x,(m x).κ=zD x)∧∀ᶠ x in atTop,G x ≤ (m x).sh/10 ∧ H x≤ (m x).sf/10 ∧ 0< (m x).Γr ∧ ∀ L:ℝ,Purse (hall_P P_ x) (m x) (winK P_ h A (F x)) (winK P_ h A (D x)) h A a b c (F x) (D x) L (lance P_ A*F x) (lance P_ A* D x):=by
 let V(x):= winK P_ h A x; let Z(x s:ℝ):= |feeΨ (Pz x) a (knot (V s) (τb b)) (knot (V s) (τb c)) h|
 have z(f)(h':sizeK R.L 2 f): sizeK R.L 2 (fun x=>Z x (f x)):= iFX (fee_f _ _ _ _ _ _ (h'.scale _)) -- inference
 let ε(x):=20*(Z x (F x)+ Z x (D x)); have hp:sizeK R.L 2 ε:=((z F hf).accrue (z D hd)).scale 20
 let Γ(x):= |10*G x+zD x*(10*H x)| + gL x; have hx:sizeK R.L 1 Γ:=(iFX ((hg.scale _).accrue (rockP 2 (hh.scale _)))).accrue (sizeK.main R.L); let E(x):=rentΦ (Pz x) (Γ x) (ε x); have h0:sizeK R.L 3 E:= pole_Q P_ Γ ε hx hp; let C'(x):= 10*G x+ Γ x+ zP x*(ε x+E x); let Θ(x):= |C' x|+gL x; have hK:sizeK R.L 1 Θ:= (iFX (((hg.scale _).accrue hx).accrue (rockP 1 (hp.accrue (h0.low (by omega)))))).accrue (sizeK.main _); let S(x):= tintK (Pz x) (E x) (Θ x) (zP x); have hu:sizeK R.L 3 S:= σΩ P_ Θ E hK h0
 let m(x:ℝ):Digit.Cash (hall_P P_ x):= ⟨zD x,10*G x,10*H x,ε x,zP x,Γ x,Θ x⟩; refine ⟨m,hx,fun x=>rfl,?_⟩
 let s (x:ℝ):= spanV (Pz x).B; have hm:=spg_B (R:=R) P_; have hw:0 < wΨ:=by norm_num [wΨ]
 filter_upwards [(hm.tint hx).spine.eventually (ge_mem_nhds zero_lt_one), ((hm.tint hp).low (k:=1) (by omega)).spine.eventually (ge_mem_nhds (show 0 < wΨ/4 from by positivity)), pill_R (k:=1) ε (show 0<wΨ/4 from by positivity) hp, tenor_Q (d/32) S (Litt.gain hu) (by positivity), (fee_Q P_ Θ hK).spine.eventually (Iio_mem_nhds zero_lt_one), spice_R (R:=R),buy_B P_ (2*P_.supportExponent*Fief.tileN 1) (show 0<a/2 from by positivity),buy_B P_ (2*(wu P_+2)*Fief.tileN 1) (show 0<a/2/2 from by positivity),ht,eventually_gt_atTop (0:ℝ)] with x b₁ pZ vZ hZ z' v l hl' hx hk
 obtain ⟨vd,t'⟩:=hx; have hu0:gL x≤ Γ x:= le_add_of_nonneg_left (abs_nonneg _); have hΓ:=v.2.2.trans_le hu0; have hΘ:0<Θ x:= add_pos_of_nonneg_of_pos (abs_nonneg _) v.2.2; let P:=Pz x; rw [pow_one] at vZ
 have hk':0 < D x:= (mul_pos hv (mul_pos v.2.2 (Work.E09.temp_pos hk))).trans_le vd
 refine ⟨Eq.le (by unfold m; dsimp; ring),Eq.le (by unfold m; dsimp; ring),hΓ, fun T=> ?_⟩ -- shadow v used forceL! rename
 refine pure_x (m:=m x) P_ h A a b c (F x) ha p v_ hk' t' ha0 v0 ⟨v.2.1,v.1, show 0≤ε x from ?_,(le_abs_self _).trans_lt (lt_add_of_pos_right _ v.2.2),hΓ.le,b₁, pZ.trans (by linarith), ?_,(le_abs_self _).trans (le_add_of_nonneg_right (v.2.2.le)),hΘ,z'⟩ l hl' (show S x ≤ D x/32 by linarith only [vd,hZ]) ?_ ?_ T -- hover
 · unfold ε Z; positivity
 · change s x* ε x ≤ _ at pZ; change ε x+s x*ε x* Γ x - (_ - s x*ε x)*Γ x<0; have ht: ε x< wΨ/4*Γ x:= vZ.trans_le (mul_le_mul_of_nonneg_left hu0 (by positivity)); have lt:=mul_le_mul_of_nonneg_right pZ hΓ.le; change 0< Γ x at hΓ; unfold wΨ at *; linarith only [ht,hΓ,lt]
 · exact (le_abs_self _).trans ((show Z x (F x)≤_ from by unfold m ε; dsimp only; linarith only [(show 0≤ Z x (D x) from abs_nonneg _)]))
 exact (le_abs_self _).trans ((show Z x (D x) ≤ _ from by unfold m ε; dsimp only; linarith only [(show 0≤ Z x (F x) from abs_nonneg _)]))
end Grain
end YM.CF.Py
