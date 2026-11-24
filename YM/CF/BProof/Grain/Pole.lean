import YM.CF.BProof.Epoch.Oven
import YM.CF.Song.Past
import YM.CF.Bloom.Screen
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
-- Rank upgrade. tiltB counts before λ. use only reserve scaling 4 r ; > variant due for both.
abbrev ForceL (P:BudgetPoint)(h A a b c:ℝ) := lobe (32*cQ*A) h (γ₀ P a (τb b) (τb c) 0 h) P
abbrev winK (P:BudgetPoint)(h A v:ℝ):ℝ:=8*tiltB A P/h^2*v
abbrev postK (P:BudgetPoint)(A:ℝ):=8*|u0 P| *cQ*tiltB A P
abbrev lance (P:BudgetPoint)(A:ℝ):= 4*(3+2*postK P A)
lemma post_nn (p:0<A):0≤ postK P_ A:=by have h:=cQ_p; have t:=desire P_ p; unfold postK; positivity
lemma lance_pos (p:0<A):0< lance P_ A:=by have h:=post_nn P_ A p; unfold lance; positivity
lemma bump_g (hA:0<A)(hf:1≤h)(p:ForceL P_ h A a b c)(t:0<d): let v:= winK P_ h A d; let x':= Pz x; Digit.board x' v h a (τb b) (τb c) ≤ d/16 ∧ yard x' v h≤ postK P_ A*d:=by
 have hν:=desire P_ hA; have hw:=cQ_p; have ht:0 < winK P_ h A d:=by unfold winK; positivity
 intro v x'; constructor
 · unfold Digit.board; change φcape (Pz x) a _ _ h ≤ _; unfold Axial.knot; rw [φc_Q]; let G:= γ₀ P_ a (τb b) (τb c) 0 h
   rw [show (cap2 P_ _ 1 a*h^2+cap2 P_ _ 1 a)*v=cQ* G *v from by unfold G γ₀ Glyph.cap2; ring]
   refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p hw.le) ht.le).trans_eq ?_
   rw [show tiltB (32*cQ*A) P_=32*cQ*tiltB A P_ from by unfold tiltB; ring]; unfold winK; field_simp; norm_num
 unfold Digit.yard; change cap1 (Pz x) _ _ ≤ _; rw [cap1_g]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self (u0 P_)) (mul_nonneg hw.le ht.le)) (sq_nonneg h)).trans_eq ?_; unfold winK postK; field_simp -- cost bound
variable {s:ℝ}
section
local notation "vφ"=> winK P_ h A d
local notation "vα"=> winK P_ h A s
lemma pure_x (hA:0<A)(hf:1≤h)(p:ForceL P_ h A a b c)
    (q:0<s)(t:s≤d)(y:0<a)(g:a≤1) {m: Cash (hall_P P_ x)} (l:m.Warrant) (n1:2*P_.supportExponent*Fief.tileN 1≤ a/2*(Pz x).B)(n2:2*(wu P_+2)*Fief.tileN 1 ≤a/2/2*(Pz x).B)(n3:m.Tr≤ s/32)(n4: feeΨ (Pz x) a (knot vφ (τb b)) (knot vφ (τb c)) h≤ m.d/20)(n5:feeΨ (Pz x) a (knot vα (τb b)) (knot vα (τb c)) h≤ m.d/20)(H:ℝ): Purse (Pz x) m vφ vα h A a b c d s H (lance P_ A*d) (lance P_ A*s):=by
 have hp(x:ℝ):0<x→ 0< winK P_ h A x:=by intro p; have he:=desire P_ hA; unfold winK; positivity; -- le
 have hc(x':ℝ): winK P_ h A x'=8*tiltB A (Pz x)*x'/h^2:=by unfold winK tiltB; rw [(let_X P_ x).2.1]; ring
 let T:=postK P_ A; have ht:0<d:= q.trans_le t
 obtain ⟨y1,y2⟩:= bump_g (x:=x) P_ h A a b c d hA hf p ht; obtain ⟨b1,b2⟩:= bump_g (x:=x) P_ h A a b c s hA hf p q
 have t1:=let_X P_ x
 have hm:=post_nn P_ A hA; have u:=mul_nonneg hm ht.le; have v:=mul_nonneg hm q.le; have ha:m.Tr ≤ d/32:= by linarith
 refine ⟨⟨⟨l,hp d ht,y,g,t1.2.2.symm ▸ n1,?_,n4⟩,hA,ht,hc d,y1,ha⟩, ⟨⟨l,hp s q,y,g,t1.2.2.symm ▸ n1,?_,n5⟩,hA,q,hc s,b1,n3⟩,?_,?_,?_,?_⟩
 · unfold wu; rw [t1.2.2]; exact n2
 · unfold wu; rw [t1.2.2]; exact n2
 · exact mul_le_mul_of_nonneg_left t (show 0≤8*tiltB A P_/h^2 by have he:=desire P_ hA; positivity)
 · unfold due lance; linarith only [u,ht,ha,y1,y2]
 · unfold due lance; linarith only [v,q,n3,b1,b2]
 unfold lance; linarith only [u,ht,y2]
end
end Grain
end YM.CF.Py
