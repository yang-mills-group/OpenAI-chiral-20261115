import YM.SU5.SatinWard.Resolution.Tarawa
import YM.SU5.SatinWard.Resolution.Oriole
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
open Ember Hove Lifted
variable (D:Division) {P T:SOp N} (E:Pattern P T r d a v)
variable (q:BudgetPoint)(t:Scree.Loom N){k m:ℕ}{g:ℝ} (C:Checked q t g d a k m)(H:4*q.B<N.val)
local notation "Z"=>SectorLayer
variable (x:Cover)
open Papyrus.Franc.SatinForce Papyrus.Franc.Loaves
-- record no capturing rank slots predicate.H.Refine.Entry.K-Frame paired. coefficient includes ℐ (important), normalization elsewhere.
abbrev DozeTrack(B:ℕ):= ℂ × (glassPair B→ ℂ)
local notation "Υ"=> DozeTrack q.B
noncomputable def datum (h:Axis) : DozeTrack q.B:=
 let T:=centHat D (wrap N x) E t q k (h,false) 1; ((Complex.I* beeC T),fun i=>curUnit x T i)
local notation "U" h:max=>datum (k:=k) D E q t x h
noncomputable def carton (B:ℕ)(L:DozeTrack B)(u v:landSheet B): Op I:= Matrix.of fun i j=> L.2 ((u,i), (v,j))
noncomputable def songTotal (B:ℕ)(L:DozeTrack B): Op I:= ∑ i:landSheet B,∑ j:landSheet B, carton B L i j
noncomputable def dietTotal (B:ℕ)(L:DozeTrack B): ℝ:= ‖L.1‖ + ∑ i:glassPair B,‖L.2 i‖
def hungerCap(B:ℕ)(L:DozeTrack B):Prop:=∀ i, ¬ plusLayer i→ L.2 i=0
local notation "Ω"=> LitCurrent.expiry (4*a) v
lemma spinQuest (h:Axis) : hungerCap q.B (U h) := fun i v=> nonstd q x _ i v -- implicit N and H
include H C
lemma awaken_life (h:Axis) : dietTotal q.B (U h) ≤ 3*LitCurrent.expiry (4*a) v:=by
 let V:= (wrap N x); let F:= grantJ D E (V, h,false); let T:= live t q k V F (1:Pane N); let e:=cutM (modesIn N (offsetMask q.B (wrap N x))); have p: moored (node V) F:= E.moorJ (V, h,false); have ht:e*T*e=T:=modes_pass (wrap N x) F C p (show Orbit N from (1,Classical.arbitrary _)) -- implicit pair parentheses.
 let v:= paintPrice q H x T ht; change ‖Complex.I * beeC T‖+ _ ≤ _; rw [norm_mul, Complex.norm_I,one_mul]; let Qx:= lakeLife D E q t C (1: Pane N) V (h,false); change frameR T≤ Ω at Qx; refine (add_le_add (chargeBee T) v).trans ?_; linarith only [Qx]
lemma compressed_price (h:Axis) : songTotal q.B (U h) = momenti D E q t k h:=by
 rw [coastMemory D E q t C H h, powerM, sum_product]; simp_rw [map_sum, smul_sum]; unfold songTotal; rw [Finset.sum_subtype _ (fun i=> (Iff.rfl : i∈ disM q.B ↔ i ∈ disM q.B))]; refine sum_congr rfl (fun i _=>?_); rw [Finset.sum_subtype _ (fun i=>(Iff.rfl: i ∈ disM q.B ↔ i∈disM q.B))]; refine sum_congr rfl (fun j _=>?_); ext p v; change curUnit x (centHat D _ _ _ _ _ _ _) ((i,p),(j,v))= _; rw [terrainB]; let b:= ((i.val,j.val):SectorLayer); let V:= (onPay D E q t h 0 k 1 b); rw [show lacquer ((shore N (x+i.val) (x+j.val)) (centHat D (wrap N x) E t q k (h,false) 1))=lacquer V from congrArg _ (centTrade D E q t C h x b)]; rfl -- p.Prop witness.No □
omit C H
lemma recordContinuity(B:ℕ) : Continuous (songTotal B) ∧ Continuous (dietTotal B):=by
 constructor
 · refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> ?_; let V:DozeTrack B →ₗ[ℂ] Op I:={ toFun p:=carton B p i j,map_add' x y:=rfl,map_smul' a x:=rfl }; exact V.continuous_of_finiteDimensional
 exact continuous_fst.norm.add (continuous_finsetSum _ (fun i _=>((continuous_apply i).comp continuous_snd).norm))
lemma nutrition (B:ℕ)(L:DozeTrack B): ‖L‖ ≤ dietTotal B L := by
 unfold dietTotal; rw [Prod.norm_def]; have hh:0 ≤ ∑ i:glassPair B, ‖L.2 i‖ := sum_nonneg fun i _=> norm_nonneg _
 refine max_le (le_add_of_nonneg_right hh) (le_trans ?_ (le_add_of_nonneg_left (norm_nonneg L.1))); apply (pi_norm_le_iff_of_nonneg hh).2; intro i; exact single_le_sum (fun i _=>norm_nonneg (L.2 i)) (mem_univ _)
lemma nutrition_under (B:ℕ)(A:ℕ→ DozeTrack B)(L:DozeTrack B)(p:Tendsto A atTop (𝓝 L))(t:∀ᶠ i in atTop,hungerCap B (A i)): hungerCap B L:=by
 intro i g; have hp:= ((((continuous_apply i).comp continuous_snd).tendsto L).comp p); exact tendsto_nhds_unique_of_eventuallyEq hp tendsto_const_nhds (t.mono fun i u=>u _ g)
#print axioms compressed_price
end AuroraX
end YM.CF.LitCurrent
