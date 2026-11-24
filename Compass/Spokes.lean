import Compass.Poetry
import Compass.Reynolds
import Compass.Bullion
import YM.CF.Neon.Ten
import Compass.Hubs
import YM.CF.Ione.Jost
import Compass.Lode
import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
variable {Nq:Side}
open Ione
open scoped Mew
local notation "Ck"=> carriers Nq
abbrev staff(Nq:Side):Type:=↥(carriers Nq)
local notation "Z1"=> staff Nq
instance (Nq:Side):Fintype (staff Nq):= Fintype.ofFinite _
abbrev orbitT (v:staff Nq):= inspire v.val
lemma yu: Function.Injective (@Cube.node Nq):= fun x y h=> (assembly Nq).embed_injective (add_right_cancel (show _+(1:Site (More Nq))=_+_ from h))
lemma camaraderie(s t:Z1)(x:Site Nq): orbitT t (orbitT s x)=orbitT (s*t) x:=by
 apply yu; unfold orbitT; rw [node_inspire,node_inspire,node_inspire]; apply (boxA (s.val*t.val)).injective; rw [step_V, Equiv.apply_symm_apply,Equiv.apply_symm_apply]; exact (Equiv.apply_symm_apply (boxA (s.val*t.val)) _).symm
-- all call kind coherence across placements tax action. given bases X etc. representation
abbrev taxK(s: staff Nq):ℝ:= taxF s.val
lemma propK(s t:Z1):taxK (s*t)= taxK s*taxK t:=tax_prod ..
lemma prop1 (s:Z1): |taxK s|=1∧ taxK s*taxK s=1:=by unfold taxK taxF; split<;>norm_num
lemma transits (x:Site Nq)(y:Site Nq):(frames (orbitT (Nq:=Nq)) y x).Nonempty:=by
 -- use translation $ η in spin. Inspire s from s = (1,b,0) $ y=x-b? mills.Lift kernel.
 let u:Sweep Nq:=⟨1,x-y,false⟩; let t:Z1:=⟨u,Anchored.one⟩
 refine ⟨t,Finset.mem_filter.mpr ⟨mem_univ _, yu ?_⟩⟩
 unfold orbitT; rw [node_inspire,←sitU,sitA]; change affine 1 ((assembly Nq).root (-( (1:Signed)⁻¹.act (x-y)))) (Cube.node x)= Cube.node y
 rw [inv_one,Signed.act_one,map_neg,map_sub]; simp only [affine,Signed.act_one,Cube.node]; abel
abbrev backing (s:staff Nq): RegBudget Nq →ₗ[ℝ] RegBudget Nq where
 toFun:=base_Q s.val
 map_add' x y:= plus_k ..
 map_smul' a x:=by
    funext i y; change suit_Y _ (a • x _ _) = a • suit_Y _ (x _ _); exact map_smul ..
lemma port_θ(s t: Z1)(X:RegBudget Nq): backing s (backing t X)= backing (s*t) X:=by
 let u:=s.val; let v:= t.val; change base_Q u (base_Q v _)=base_Q (u*v) _
 funext i j; unfold base_Q; rw [←step_k u v]; exact congrFun (yard (X _) u v) j
abbrev cuspan(s:staff Nq): Cusp Nq →ₗ[ℝ] Cusp Nq where
 toFun:=force_V s.val
 map_add' x y:=by funext i j k; exact map_add (suit_Y s.val⁻¹) _ _
 map_smul' x y:=by funext i j k; exact map_smul (suit_Y s.val⁻¹) x _
lemma agenda (s t: Z1)(X:Cusp Nq): cuspan s (cuspan t X)=cuspan (s*t) X:=by
 let u:=s.val; let v:= t.val; change force_V u (force_V v _)=force_V (u*v) _
 funext i j V; unfold force_V turn_V; simp only [Function.comp_apply,hush_k,tape_B, yell_t,mul_inv_rev,moon_Y]
abbrev castPay(s:staff Nq): ℂ→ₗ[ℝ]ℂ:=(cast_B (wageZ s.val⁻¹)).toLinearMap
lemma wage_t (s:Z1)(x:ℂ): castPay s x=Spire.payZ s.val⁻¹ x:=castT ..
lemma seal_t (s t:Z1)(x:ℂ): castPay s (castPay t x)=castPay (s*t) x:=by
 let u:=s.val; let v:= t.val
 rw [wage_t,wage_t,wage_t]; change Spire.payZ u⁻¹ (Spire.payZ v⁻¹ x)= Spire.payZ (u*v)⁻¹ x; rw [mul_inv_rev]; -- commute
 rw [show Spire.payZ u⁻¹ (Spire.payZ v⁻¹ x)=Spire.payZ v⁻¹ (Spire.payZ u⁻¹ x) from ?_,warX]; unfold Spire.payZ; rw [sign_seq,sign_seq,Bool.xor_comm]
#check frames
end YM.CF.Compass
