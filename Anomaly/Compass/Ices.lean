import Anomaly.Apert.Sync
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
open Bake Lilt Rue Trees Taxi Moto Neon Haro Tap Py
open Hove Mew Larch
variable {N B:Side}
local notation "mH"=> mid N B
local notation "aH"=> Aura mH
variable (q:Sweep (mid N B))(g:q∈ Whirl (mid N B))(o:Site (mid N B))(V T:Copy (mid N B))(E:RegBudget (mid N B))(K:Cusp (mid N B))(A:ArcΦ)(t:ℂ)(u v w:ℝ)
variable (hi:∀ x:Orbit (mid N B),T (yellA q x)=suit_Y q (V x))
variable (hn:∀ i:Scree.Hub (mid N B),chose m P i→Nonwrapping i.val.2 i.val.1)(hx:4≤ (More (mid N B)).val)
variable (U:UNI SpinIdx)(ht:JetS q.s false (detX q.s) U)
local notation "W"=> dashK q K
local notation "Z_"=> dashF q E
local notation "C_"=> P.supportExponent+1+1
lemma iceLaw (z:0≤h)(u0:0≤u)(i:Ice m (mPath q o) P h u v w V E K t A)(hn:∀ i:Scree.Hub (mid N B),chose m P i→Nonwrapping i.val.2 i.val.1)(hx:4≤ (More (mid N B)).val)(g:q∈Whirl (mid N B))(U:UNI SpinIdx)(ht:JetS q.s false (detX q.s) U)(hi:∀ x:Orbit (mid N B),T (yellA q x)=suit_Y q (V x)): Ice m o P h (duty_Q P.order P.power*u) (strive_E P.order*v) w T (dashF q E) (dashK q K) (Spire.payZ q t) (arc_s q.s U A):=by
 -- choose
 refine ⟨turf_A m o P _ _ _ _ (mul_le_mul_of_nonneg_right (le_refl _) u0) (facetAx q g E A o i.axle z hn hx U ht), ?_,?_,?_,?_⟩ -- replace
 · rw [orbital_phase]; exact i.phase
 · intro x p
   let Y:=moldA q⁻¹ x; have he(u:Seat mH)(h:u∈Y.val): (boxA q⁻¹) u∈x.val:=Finset.mem_map_equiv.mp h
   have hp:node (mPath q o)∉ Y.val:=fun v=>p (by specialize he _ v; rw [nodeA,sitU,Equiv.symm_apply_apply] at he; exact he)
   funext D s; change suit_Y (q⁻¹)⁻¹ _=0; rw [show K Y=0 from i.stout _ hp,Pi.zero_apply]; exact map_zero _
 · obtain ⟨Q,hQ,fQ,vQ⟩:=i.grant; let L:=strive_E P.order; have hv:L ≤ L:=le_rfl; have hc: 0≤ L:= le_trans (by unfold L strive_E composeCost; positivity) hv; let J:= L • (zeal_F q⁻¹ Q)
   refine ⟨J,⟨fun x=>mul_nonneg hc (hQ.1 _),fun x D u p=>?_⟩,fun x=>?_,fun x p=>?_⟩
   · let E:=moldA q⁻¹ x
     have hk:= full_medal P x.val D q⁻¹ (inv_mem g) (hQ.2 E _ (map_nonempty.mpr u) (map_subset_map.mpr p)) z; exact hk.big (mul_le_mul_of_nonneg_right hv (hQ.1 E))
   · unfold J; rw [tall_s]; apply mul_le_mul_of_nonneg_left _ hc
     have h:=call_Q (k:=P.B) (a:=C_) q⁻¹ Q ((boxA q⁻¹).symm x); rw [Equiv.apply_symm_apply] at h; exact h.trans_le (fQ _)
   let T:=moldA q⁻¹ x; obtain ⟨hv,gx⟩:=vQ T fun q=>p (by change L*Q T=0; rw [q,mul_zero]); have hx:coverNumber P.B T.val= _:= glow_q q⁻¹ P.B x.val
   refine ⟨hx ▸ hv,?_⟩; have hp:(boxA q⁻¹) _∈ x.val:= Finset.mem_map_equiv.mp (show node (mPath q o) ∈ actY q⁻¹ x.val from gx); rw [nodeA,sitU,Equiv.symm_apply_apply] at hp; exact hp
 intro x p; let Z:=yellA q⁻¹ x; have he:yellA q Z=x:= by have h:= y_rev q⁻¹ x; rwa [inv_inv] at h
 have hp:= skew_V q⁻¹ x.1 _ p
 rw [←he,hi,i.wear Z hp, map_add,map_add]; simp only [suit_cost,map_one]; rw [show exponentL P _ _= _ from dash_Ek q Z E, dash_Ck] -- heavy

end YM.CF.Ione.Clock
