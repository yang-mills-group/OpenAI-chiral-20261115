import YM.CF.DPress.Plaque.Rope
import YM.CF.Taxi.Mile
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.DPress.Plaque
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
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
open AnalyticBridge.VerifiedReset
attribute [local instance] Gauge.frobInner
open Siete PhysicalNext.JointLoad.Heir Push.Local
local notation "Y"=> SU.group
variable (P:BudgetPoint) {n:Side}{o: Site (More n)}(u:Site (More n)) (i:Pane n) {X:Support (More n)}{a:ℝ}{k:ℕ}
-- uniform proof across coupling.H, λ, n. real part.Ang.Bar
variable (p:Taxi.DayT P.order a)(h:0≤a) (V:pingS P.threshold X i)(t:u∈ X) (e:separation u o ≤ k)
include p h V t e
abbrev Φ (P:BudgetPoint)(k:ℕ) (q:ℝ):ℝ:= (((1:ℝ)+((2:ℝ)+(k:ℝ)))^P.power)^P.order*(q*AnalyticBridge.VerifiedReset.faceCost Y P)
local notation "H"=> Φ P k a
private lemma fisc(j:Face (Per (More n)))(q:j∈Rings u) : Signs P o (fun x=> (Y).price (faceValue (increment i x) j)) ((Φ P k a)*P.threshold^2):=by
 let U:= fun x:Config Y (More n)=>pingS P.threshold X x; let K'(j:Face (Per (More n)))(x:Pane n):= (Y).price (faceValue x j)
 have he:AnalyticBridge.VerifiedReset.Bill P j.1 U (faceCost Y P*P.threshold^2) (K' j):= face_price j.1 j.2 P fun W (p:U W)=> by apply le_of_lt (p j (fun t'=> Finset.disjoint_left.mp t' t (mem_filter.mp q).2))
 let V':= p n P U j.1 _ _ he rfl i V; let T:=a*(faceCost Y P*P.threshold^2); let D:ℝ:= ((1:ℝ)+((2:ℝ)+k))^P.power; have hs: spine P.power j.1 o ≤ D:=by
    have hx:(separation j.1 o:ℝ) ≤ ((2+k:ℕ):ℝ):=by exact_mod_cast (separation_triangle j.1 u o).trans (Nat.add_le_add ((separation_comm ..).trans_le (WilsonStartup.visit_near j ((mem_filter.mp q).2))) e)
    refine pow_le_pow_left₀ (by positivity) ?_ _; push_cast at hx; linarith -- tune spine unfreeze
 rw [show Φ P k a*P.threshold^2 = D^P.order*T from (by unfold Φ D T; ring)]
 have hxT:0≤T:=V'.grade; refine ⟨mul_nonneg (by unfold D; positivity) hxT,V'.paid,fun x f i w=>?_⟩; exact (Siete.rise_i x (V'.token x f) i w).trans (mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_right₀ (spine_one ..) f) (pow_le_pow_left₀ (spine_pos ..).le hs P.order)) hxT)
-- require X contains C_o rather than u; for Bill.Price only u
abbrev BillQ(P:BudgetPoint)(k:ℕ)(q:ℝ):= (4:ℝ)⁻¹ *((Fintype.card PlaqAxes*4:ℕ)*Φ P k q)
lemma fiscal (q:qualify (More n) k): Signs P o ((feeW u) ∘ increment i) (BillQ P k a * P.threshold^2):=by
 let D:Signs P o (fun x=> ∑ j∈Rings u,(Y).price (faceValue (increment i x) j)) ((Fintype.card PlaqAxes*4:ℕ)*(Φ P k a*P.threshold^2)):=by
    rw [← knownC u (by unfold qualify at q; omega)]; simpa only [sum_const,nsmul_eq_mul] using Prism.haloI (f:=fun _=> Φ P k a*P.threshold^2) (S:=Rings u) (F:=fun j x=>(Y).price (faceValue (increment i x) j)) (fun j q'=>fisc P u i p h V t e _ q')
 change Signs P o _ _; have hl:= (Prism.skin D).smul ((4:ℝ)⁻¹); rw [abs_of_nonneg (by norm_num : (0:ℝ)≤(4:ℝ)⁻¹),←mul_assoc,←mul_assoc] at hl; apply Prism.skills; refine hl.mono (le_of_eq ?_); unfold BillQ; ring -- order.try
end YM.CF.DPress.Plaque
