import YM.CF.Vow.Face
import YM.CF.Vow.Palm
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
lemma voyageW {F1:Pax n}(p:∀ i,F1 (moldA T i) (yellA T V)=C (F i V)) (i:Tuple (Aura n) k):sta F1 (Yc X) m (⟨k,curlV T k i⟩) (yellA T V) = C (sta F X m ⟨k,i⟩ V):=by
 unfold sta; simp only [tideI,(moldA T).injective.eq_iff]; split; swap; · exact (map_zero _).symm
 unfold guava; simp only [Pi.smul_apply, Finset.prod_apply]; rw [patV,map_smul,map_prod]; refine congrArg _ ?_; apply prod_congr rfl; exact fun j _=> p _
variable {Q:Aura n→ℝ} {d1 d2 d3:ℝ}{M:ℕ}(Pv:Ready Palot.stern M Q c d1 d2 d3)(Ph:1≤h)(P_:∀ i,Medal P i.val ∅ (F i) h (Q i))(k_:0≤c)
variable {F1:Pax n}{Q1:Aura n→ℝ}(p:∀ i,F1 (moldA T i) (yellA T V)=C (F i V))(pW:Ready Palot.stern M Q1 c d1 d2 d3)(Q_:∀ i, Medal P i.val ∅ (F1 i) h (Q1 i))
include Pv Ph P_ k_ p pW Q_
lemma spinsEW(m:ℕ):spinD P (Yc X) F1 m (yellA T V)= C (spinD P X F m V):=by
 by_cases x: visible P X.val (∅:Support _) V.1; swap; · exact (if_neg (mt (yarnV T V X 0).2 x)).trans (by rw [show spinD P X F m V=0 from if_neg x, map_zero]) -- tune
 let J(i k:ℕ):= V; rw [spiritD (Yc X) _ _ _ pW k_ ((yarnV T V X 0).1 x) m,spiritD X V _ _ Pv k_ x]; all_goals first| exact P_| exact Q_|exact Ph|skip -- params
 let L:= C.toLinearMap.toContinuousLinearMap
 let A:=fun (s: Clusters (Aura n))=> sta F X m s V; obtain ⟨i,g,h⟩:=x; have hp:Summable A:=Summable.of_norm_bounded (glomM X Pv k_) (fun j=>by
    let K:=ponder X j Ph P_ m; unfold A; rw [K.same _ (i,V.2) h (fun _ _=>rfl)]; exact K.capF Ph _ g)
 let Y:= Equiv.sigmaCongrRight (fun m=> curlV T m)
 change _ = L (∑' (i:Clusters (Aura n)), A i); rw [←(L.hasSum hp.hasSum).tsum_eq] -- tune
 rw [← Y.tsum_eq]; exact tsum_congr fun s=> voyageW T X C V p s.2

omit Pv Ph P_ k_ p pW Q_
private lemma liftQW : (H).toLeft=t.toLeft.map (moldA T).toEmbedding ∧ (H).toRight=t.toRight.map (moldA T).toEmbedding:=by
 constructor <;> ext x <;> simp only [mem_toLeft, mem_toRight, Finset.mem_map_equiv] <;> exact Iff.rfl
variable {K1 W1:Cusp n}
variable (hQ:∀ i:Aura n,∀ D:Support (More n),D.Nonempty →D⊆i.val→ K1 (moldA T i) (actY T D) (yellA T V)=C (K i D V))
variable (hW:∀ i:Aura n,∀ D:Support (More n),D⊆i.val→ W1 (moldA T i) (actY T D) (yellA T V)=C (W i D V))
include hQ hW
lemma orbitDW (p:D ⊆ X.val) : glowV K1 W1 (Yc X) (Υ D) (yellA T V)= C (glowV K W X D V):=by
 unfold glowV; rw [if_pos p,if_pos (show Υ D⊆(Yc X).val from Finset.map_subset_map.mpr p)]; unfold mintF; rw [Finset.sum_apply,Finset.sum_apply, _root_.map_sum]; rw [←Equiv.sum_comp (Luke T).finsetCongr]; apply sum_congr rfl; intro i v
 rw [gear_v,gear_v]; simp only [show (Luke T).finsetCongr i=i.map (Luke T).toEmbedding from rfl, filmC]; split; swap; · exact (map_zero _).symm
 rename_i g; simp only [(liftQW T i).1,(liftQW T i).2, Pi.mul_apply,Finset.prod_apply,prod_map]; rw [_root_.map_mul,_root_.map_prod, _root_.map_prod]; refine congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl ?_)<;> intro j t
 · change K1 (Yc j) (Υ D∩Υ j.val) _=_; rw [actY,actY,←map_inter]; exact hQ _ (D∩j.val) (stun_v X i g _ t).1 inter_subset_right
 change W1 (Yc j) (Υ D∩Υ j.val) _=_; rw [actY,actY,←map_inter]; exact hW _ (D∩j.val) inter_subset_right
lemma gateVW(Q:Force n): budgetR (glowV K1 W1) (moveForce T Q) (yellA T V)= C (budgetR (glowV K W) Q V):=by
 let HG:=extraD Q; let I:=lordD Q; change _= C (bassH I • glowV K W I _ V); have hx: lordD (moveForce T Q)=Yc I:=rfl; have ht: bassH (lordD (moveForce T Q))=bassH I:=by rw [hx,bassH,bassH]; simp [moldA,actY] -- tune
 rw [map_smul,budgetR,ht,hx]; exact congrArg (bassH I • ·) (orbitDW T I C V hQ hW Q.property.2)
omit hW
variable {R1:Cusp n}{F1:Pax n}(R:Cusp n)(pR:∀ i:Aura n,∀ D:Support (More n),D.Nonempty→D⊆i.val→ R1 (moldA T i) (actY T D) (yellA T V)= C (R i D V)) (F':∀ i,F1 (moldA T i) (yellA T V)= C (F i V))
variable {B:ℕ}{γ δ q:ℝ} {f:Aura n→ℝ}(h3:Ready Palot.stern B f c γ δ q)(he:1≤h)(hk:∀ i,Medal P i.val ∅ (F i) h (f i))(ht:0≤ c)
variable {fA:Aura n→ℝ}(h3A:Ready Palot.stern B fA c γ δ q)(hkA:∀ i,Medal P i.val ∅ (F1 i) h (fA i))
include pR F' h3 he hk ht h3A hkA
lemma valiantW (Q:Force n) : budgetR (roomV P F1 K1 R1) (moveForce T Q) (yellA T V)= C (budgetR (roomV P F K R) Q V):=by
 letI : NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _; refine gateVW T C V hQ (W:= boastV (FeeD P F) R) ?_ Q; intro i D v; unfold boastV; simp only [show (Υ D).Nonempty ↔_ from (map_nonempty: (Υ D).Nonempty ↔ D.Nonempty), map_sub,map_one,map_exp C C.toLinearMap.continuous_of_finiteDimensional]; split
 · rw [pR i D ‹_› v]
 rw [map_neg]; exact congrArg (fun x=> exp (-x) - 1) (spinsEW T i C V h3 he hk ht F' h3A hkA 0) -- tune ite right
end YM.CF.Vow
