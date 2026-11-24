import YM.CF.Vow.Asset
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
open Trees Ursell Push.AbsoluteSums.Graph Gas
abbrev Aura(n:Side):=Palot.Y (More n)
abbrev Pax(n:Side):= Aura n→ Copy n
abbrev sta (F:Pax n)(x:Aura n)(m:ℕ)(p:Clusters (Aura n)): Copy n:= if x=tideU p ∧ m ≤ p.1 then guava gRule F p else 0
abbrev sepV (u:Aura n→ℝ)(x:Aura n)(m:ℕ)(p:Clusters (Aura n)):= if x=tideU p ∧ m ≤ p.1 then Ursell.clusters gRule u p.2 else 0
variable {F:Pax n}{Q:Aura n→ℝ}(Xq:Aura n)(p:Clusters (Aura n))(V:Orbit n)
lemma rimY(p:Clusters (Aura n))(x:SongQ p.1) : (p.2 x).val⊆(tideU p).val:=fun _ s=> Finset.mem_biUnion.mpr ⟨x,mem_univ _,s⟩
variable (hp:1≤h)(hQ:∀ i,Medal P i.val ∅ (F i) h (Q i))
include hp hQ
lemma ponder(m:ℕ) : Medal P Xq.val ∅ (sta F Xq m p) h (sepV Q Xq m p):=by
 unfold sta sepV; split_ifs with x; swap; · exact Medal.zeroT
 obtain ⟨rfl,e⟩:= x -- trouble subst p? x eq xq=tide
 unfold guava Ursell.clusters; rw [mul_div_right_comm]; -- tune
 have hx:= Medal.prodP (P:=P) (X:=(tideU p).val) (D:=∅) univ (fun i=>F (p.2 i)) (fun i=>Q (p.2 i)) (fun i _=> (hQ _).stretchB (rimY p i) (Subset.refl _) (by simp only [sdiff_empty]; exact rimY p i)) (zero_le_one.trans hp)
 refine Medal.big (hx.rum _) ?_; rw [norm_div,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity)] -- tune
variable {B:ℕ}{γ δ q:ℝ}(t:Ready stern B Q a γ δ q)(hb:0≤a)
omit hp hQ
abbrev funge (x: Aura n)(F:Pax n)(m k:ℕ):Copy n:= ∑ i:Tuple (Aura n) k, sta F x m ⟨k,i⟩
abbrev spinD (P:BudgetPoint)(x: Aura n)(F:Pax n)(m:ℕ) : Copy n:= lasting P x.val ∅ (funge x F m)
abbrev spanD (x: Aura n)(Q: Aura n→ℝ)(m:ℕ):ℝ:=∑' p:Clusters (Aura n), sepV Q x m p
include t hb
lemma glomM : Summable (sepV Q Xq m):=by
 obtain ⟨i,v⟩:= Xq.property; let G(X:Clusters (Aura n)):= if m≤X.1∧i∈(tideU X).val then Ursell.clusters gRule Q X.2 * currency B a (tideU X).val else 0; have ht: SumBudget G (γ*q^m*(1-q)⁻¹):=log_hit_tail _ _ _ testG t hb _ i
 refine ht.2.1.of_nonneg_of_le (fun i=>?_) (fun i=>?_); · unfold sepV; split; exact clusters_nonneg gRule t.2.2.2.2.1 _; exact le_rfl
 rename_i l; unfold sepV; split_ifs with s
 · unfold G; rw [if_pos ⟨s.2,s.1 ▸ v⟩]; exact le_mul_of_one_le_right (clusters_nonneg _ t.2.2.2.2.1 _) (Real.one_le_exp (mul_nonneg hb (by positivity)))
 exact ht.1 _
include hQ hp
lemma glenP (m:ℕ) : Medal P Xq.val ∅ (spinD P Xq F m) h (spanD Xq Q m):=by
 have hp':= glomM (m:=m) Xq t hb; unfold spanD; rw [hp'.tsum_sigma] -- tune
 simp_rw [tsum_fintype]; unfold spinD; apply vaut (fun i=> Medal.sumP _ _ _ (fun j _=> ponder Xq ⟨i,j⟩ hp hQ m)) _ hp; simpa using hp'.sigma
-- exact Vol.B.
lemma spiritD (s:visible P Xq.val ∅ V.1)(m:ℕ) : spinD P Xq F m V=∑' i:Clusters (Aura n), sta F Xq m i V:=by
 let W(i:ℕ):= funge Xq F m i; unfold spinD lasting zenS; rw [if_pos s]; obtain ⟨i,w,l⟩:=s
 have ht(p):‖sta F Xq m p V‖ ≤ sepV Q Xq m p:=by rw [(ponder Xq p hp hQ m).same V (i,V.2) l (fun _ _=>rfl)]; exact (ponder Xq p hp hQ m).capF hp _ w
 have hh:Summable (fun p=> ‖sta F Xq m p V‖):=(glomM Xq t hb).of_nonneg_of_le (fun i=> norm_nonneg _) ht
 rw [hh.of_norm.tsum_sigma] -- tune
 simp [funge]
omit hp hQ
include t hb
lemma thinX (o:Seat n)(m:ℕ) : ∑ i:Aura n with o∈i.val, spanD i Q m * Trees.currency B a i.val ≤ γ*q^m*(1-q)⁻¹:=by
 have he:=Ursell.log_hit_tail _ _ _ testG t hb m o; unfold spanD; simp_rw [←tsum_mul_right]; rw [← Summable.tsum_finsetSum]; swap; · exact fun i _=> (glomM i t hb).mul_right _
 apply le_trans _ he.2.2; apply le_of_eq; apply tsum_congr; intro z; by_cases h:o∈ unionOf stern z.2
 · rw [sum_eq_single (tideU z)]; · unfold sepV; split_ifs <;> simp_all [tideU] -- tune
   · intro i p w; rw [sepV,if_neg fun q=>w q.1,zero_mul]; -- tune
   exact fun v=> False.elim (v (mem_filter.mpr ⟨mem_univ _,h⟩))
 rw [if_neg fun q=> h q.2]; apply sum_eq_zero; intro j p; rw [sepV,if_neg (fun (k:j=tideU z ∧ m ≤ z.1)=> h (show o∈(tideU z).val from k.1 ▸ (show o∈ j.val from (mem_filter.mp p).2))),zero_mul]
end YM.CF.Vow
