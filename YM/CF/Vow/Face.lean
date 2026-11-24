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
abbrev Luke (T:Sweep n): Equiv.Perm (Palot.Duo (More n)):= Equiv.sumCongr (moldA T) (moldA T)
variable (t:Finset (Palot.Duo (More n)))
local notation "H"=> t.map (Luke T).toEmbedding
-- amount claims lift through masks.B. support and clash exactly on SAME maps
private lemma broV : beatB H= Λ (beatB t):=by
 unfold beatB rhythm; rw [Finset.sup_map,_root_.map_finset_sup]; apply Finset.sup_congr rfl; intro i p; dsimp only [Function.comp_apply]; rw [Salt.runV]; cases i<;> rfl -- tune
private lemma lay_R(L: hook (Site (More n))): robe (L.map (moldA T).toEmbedding)=Υ (robe L):=by
 ext i; unfold actY; rw [Finset.mem_map_equiv]; constructor
 · intro p; obtain ⟨j,h,v⟩:= mem_biUnion.mp p; obtain ⟨x,q,rfl⟩:= mem_map.mp h; exact mem_biUnion.mpr ⟨x,q,mem_map_equiv.mp v⟩
 intro p; obtain ⟨x,q,v⟩:=mem_biUnion.mp p; exact mem_biUnion.mpr ⟨Yc x,mem_map_of_mem _ q,mem_map_equiv.mpr v⟩ -- tune namespace
private lemma fearD(L: hook (Site (More n)))(D:Support (More n)):raisedH (Υ D) (L.map (moldA T).toEmbedding) ↔ raisedH D L:=by
 constructor; · intro p i g v; exact p (Yc i) (mem_map_of_mem _ g) ((Finset.disjoint_map _).2 v)
 intro p i g v; obtain ⟨k,gx,h⟩:= mem_map.mp g; subst i; exact p k gx ((Finset.disjoint_map _).1 v)
private lemma ride_q(L:hook (Site (More n))): Palot.flow _ (L.map (moldA T).toEmbedding) ↔ Palot.flow _ L:=by
 constructor
 · intro p i g j v w; exact (Finset.disjoint_map _).1 (p (Yc i) (mem_map_of_mem _ g) (Yc j) (mem_map_of_mem _ v) ((moldA T).injective.ne w))
 intro p i g j v w; obtain ⟨i,g0,rfl⟩:= mem_map.mp g; obtain ⟨j,v0,rfl⟩:=mem_map.mp v; exact (Finset.disjoint_map _).2 (p i g0 j v0 (fun h=> w (congrArg _ h)))
private lemma liftQ : (H).toLeft=t.toLeft.map (moldA T).toEmbedding ∧ (H).toRight=t.toRight.map (moldA T).toEmbedding:=by
 constructor <;> ext x <;> simp only [mem_toLeft, mem_toRight, Finset.mem_map_equiv] <;> exact Iff.rfl
lemma filmC : lumpD H (Υ D) (Yc X)↔ lumpD t D X:=by
 unfold lumpD; rw [broV]; change _∧ Palot.mine (Υ D) H↔ _; rw [show beamH (Yc X).val=Λ (beamH X.val) from (Salt.runV ..).symm, (Salt.quill _).injective.eq_iff]; refine and_congr_right fun p=>?_; unfold Palot.mine; rw [(liftQ T t).1,(liftQ T t).2,broV, ride_q,fearD, lay_R,fearD, bayV,←map_inter]; refine and_congr_right fun _=> and_congr_right fun _=> and_congr_right fun _=>Finset.map_subset_map -- tune order
variable (hQ:∀ i:Aura n,∀ D:Support (More n),D.Nonempty →D⊆i.val→ K (moldA T i) (actY T D) (yellA T V)=C (K i D V))
variable (hW:∀ i:Aura n,∀ D:Support (More n),D⊆i.val→ W (moldA T i) (actY T D) (yellA T V)=C (W i D V))
include hQ hW
lemma orbitD (p:D ⊆ X.val) : glowV K W (Yc X) (Υ D) (yellA T V)= C (glowV K W X D V):=by
 unfold glowV; rw [if_pos p,if_pos (show Υ D⊆(Yc X).val from Finset.map_subset_map.mpr p)]; unfold mintF; rw [Finset.sum_apply,Finset.sum_apply, _root_.map_sum]; rw [←Equiv.sum_comp (Luke T).finsetCongr]; apply sum_congr rfl; intro i v
 rw [gear_v,gear_v]; simp only [show (Luke T).finsetCongr i=i.map (Luke T).toEmbedding from rfl, filmC]; split; swap; · exact (map_zero _).symm
 rename_i g; simp only [(liftQ T i).1,(liftQ T i).2, Pi.mul_apply,Finset.prod_apply,prod_map]; rw [_root_.map_mul,_root_.map_prod, _root_.map_prod]; refine congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl ?_)<;> intro j t
 · change K (Yc j) (Υ D∩Υ j.val) _=_; rw [actY,actY,←map_inter]; exact hQ _ (D∩j.val) (stun_v X i g _ t).1 inter_subset_right
 change W (Yc j) (Υ D∩Υ j.val) _=_; rw [actY,actY,←map_inter]; exact hW _ (D∩j.val) inter_subset_right
lemma gateV(Q:Force n): budgetR (glowV K W) (moveForce T Q) (yellA T V)= C (budgetR (glowV K W) Q V):=by
 let HG:=extraD Q; let I:=lordD Q; change _= C (bassH I • glowV K W I _ V); have hx: lordD (moveForce T Q)=Yc I:=rfl; have ht: bassH (lordD (moveForce T Q))=bassH I:=by rw [hx,bassH,bassH]; simp [moldA,actY] -- tune
 rw [map_smul,budgetR,ht,hx]; exact congrArg (bassH I • ·) (orbitD T I C V hQ hW Q.property.2)
omit hW
variable (R:Cusp n)(pR:∀ i:Aura n,∀ D:Support (More n),D.Nonempty→D⊆i.val→ R (moldA T i) (actY T D) (yellA T V)= C (R i D V)) (F':∀ i,F (moldA T i) (yellA T V)= C (F i V))
variable {B:ℕ}{γ δ q:ℝ} {f:Aura n→ℝ}(h3:Ready Palot.stern B f c γ δ q)(he:1≤h)(hk:∀ i,Medal P i.val ∅ (F i) h (f i))(ht:0≤ c)
include pR F' h3 he hk ht
lemma valiant (Q:Force n) : budgetR (roomV P F K R) (moveForce T Q) (yellA T V)= C (budgetR (roomV P F K R) Q V):=by
 letI : NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _; refine gateV T C V hQ (W:= boastV (FeeD P F) R) ?_ Q; intro i D v; unfold boastV; simp only [show (Υ D).Nonempty ↔_ from (map_nonempty: (Υ D).Nonempty ↔ D.Nonempty), map_sub,map_one,map_exp C C.toLinearMap.continuous_of_finiteDimensional]; split
 · rw [pR i D ‹_› v]
 rw [map_neg]; exact congrArg (fun x=> exp (-x) - 1) (spinsE T i C V F' h3 he hk ht 0) -- tune ite right
end YM.CF.Vow
