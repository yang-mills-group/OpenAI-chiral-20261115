import SatinThinPalm
import YM.CF.Vow.Face
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Salt Trees Ursell
variable (T:Sweep n) (X Y:Aura n)
local notation "Yc"=> moldA T
local notation "Λ"=> Salt.quill (boxA T)
local notation "Υ"=> actY T
variable {F:Pax n}{K W:Cusp n} (C:Cipher n→ₐ[ℝ]Cipher n) (V:Orbit n)
variable (t:Finset (Palot.Duo (More n)))
local notation "H"=> t.map (Luke T).toEmbedding
private lemma liftQ_rel : (H).toLeft=t.toLeft.map (moldA T).toEmbedding ∧ (H).toRight=t.toRight.map (moldA T).toEmbedding:=by
 constructor <;> ext x <;> simp only [mem_toLeft, mem_toRight, Finset.mem_map_equiv] <;> exact Iff.rfl
variable (Kb: Cusp n) (hQ:∀ i:Aura n,∀ D:Support (More n),D.Nonempty →D⊆i.val→ Kb (moldA T i) (actY T D) (yellA T V)=C (K i D V))
variable (Wb:Cusp n) (hW:∀ i:Aura n,∀ D:Support (More n),D⊆i.val→ Wb (moldA T i) (actY T D) (yellA T V)=C (W i D V))
include hQ hW
lemma rel_orbitD (p:D ⊆ X.val) : glowV Kb Wb (Yc X) (Υ D) (yellA T V)= C (glowV K W X D V):=by
 unfold glowV; rw [if_pos p,if_pos (show Υ D⊆(Yc X).val from Finset.map_subset_map.mpr p)]; unfold mintF; rw [Finset.sum_apply,Finset.sum_apply, _root_.map_sum]; rw [←Equiv.sum_comp (Luke T).finsetCongr]; apply sum_congr rfl; intro i v
 rw [gear_v,gear_v]; simp only [show (Luke T).finsetCongr i=i.map (Luke T).toEmbedding from rfl, filmC]; split; swap; · exact (map_zero _).symm
 rename_i g; simp only [(liftQ_rel T i).1,(liftQ_rel T i).2, Pi.mul_apply,Finset.prod_apply,prod_map]; rw [_root_.map_mul,_root_.map_prod, _root_.map_prod]; refine congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl ?_)<;> intro j t
 · change Kb (Yc j) (Υ D∩Υ j.val) _=_; rw [actY,actY,←map_inter]; exact hQ _ (D∩j.val) (stun_v X i g _ t).1 inter_subset_right
 change Wb (Yc j) (Υ D∩Υ j.val) _=_; rw [actY,actY,←map_inter]; exact hW _ (D∩j.val) inter_subset_right
lemma rel_gateV(Q:Force n): budgetR (glowV Kb Wb) (moveForce T Q) (yellA T V)= C (budgetR (glowV K W) Q V):=by
 let HG:=extraD Q; let I:=lordD Q; change _= C (bassH I • glowV K W I _ V); have hx: lordD (moveForce T Q)=Yc I:=rfl; have ht: bassH (lordD (moveForce T Q))=bassH I:=by rw [hx,bassH,bassH]; simp [moldA,actY] -- tune
 rw [map_smul,budgetR,ht,hx]; exact congrArg (bassH I • ·) (rel_orbitD T I C V Kb hQ Wb hW Q.property.2)
omit hW
variable (R Rb:Cusp n)(F1:Pax n)(pR:∀ i:Aura n,∀ D:Support (More n),D.Nonempty→D⊆i.val→ Rb (moldA T i) (actY T D) (yellA T V)= C (R i D V)) (F':∀ i,F1 (moldA T i) (yellA T V)= C (F i V))
variable {B:ℕ}{γ δ q:ℝ} {f:Aura n→ℝ}(h3:Ready Palot.stern B f c γ δ q)(he:1≤h)(hk:∀ i,Medal P i.val ∅ (F i) h (f i))(ht:0≤ c)
include pR F' h3 he hk ht
variable {e0 e1 e2 e3:ℝ}{B2:ℕ}(Q1:Aura n→ℝ)(Pv1:Ready Palot.stern B2 Q1 e0 e1 e2 e3)(hc1:0≤e0)(h1:∀ i,Medal P i.val ∅ (F1 i) h (Q1 i))
include Pv1 h1 hc1
lemma rel_valiant (Q:Force n) : budgetR (roomV P F1 Kb Rb) (moveForce T Q) (yellA T V)= C (budgetR (roomV P F K R) Q V):=by
 letI : NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _; refine rel_gateV T C V Kb hQ (boastV (FeeD P F1) Rb) (W:= boastV (FeeD P F) R) ?_ Q; intro i D v; unfold boastV; simp only [show (Υ D).Nonempty ↔_ from (map_nonempty: (Υ D).Nonempty ↔ D.Nonempty), map_sub,map_one,map_exp C C.toLinearMap.continuous_of_finiteDimensional]; split
 · rw [pR i D ‹_› v]
 rw [map_neg]; exact congrArg (fun x=> exp (-x) - 1) (rel_spinsE T i C V F1 F' h3 he hk ht Q1 Pv1 hc1 h1 0) -- tune ite right
end YM.CF.Vow
