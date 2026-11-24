import YM.CF.BPress.Huon.Primary
import YM.CF.BPress.Huon.Star
/-! Severe block tally.E.Price incl.S handles.Speck.Use positive polynomial cap only on flagged. Costs and ext estimates.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Along Spine Mosaic.Pulse Mosaic Palmer Contour Lilac.Stripe Ledger Push.AbsoluteSums
variable {R:Hangar (More N)} {H:Crew A}{T:GramM N}{τ k D ζ a C:ℝ}
variable (F: Recipe (A:=A) T) (p: Budgeting H F τ k D ζ a C)(u: Mangrove R H F.M)
variable (x:Visit A R H)(V:SlotT A R)
abbrev ice(x: Choir A R)(V:SlotT A R):= chipAt V (own A R) (House.Sread A R x)
def storm := ∑ i∈ ice x.val V, cold H F (fU x.val) i
abbrev cam(x: Choir A R):= House.Sread A R x
lemma shard_eq {i:A.Hcols}(h:i∈ cam x.val): own A R i∈ debts H x.val:= by apply Hazel.Reserve.hurt_m; exact Or.inl h
include p in
lemma stormC : storm F x V ≤ -(reward B.D H.κ H.y T.funds) * (ice x.val V).card:=by
 unfold Huon.storm; apply (sum_le_sum (fun i v=> p.upper_cold (party _ _ _ x) i (mem_filter.mp v).1)).trans_eq; rw [sum_const,nsmul_eq_mul,mul_comm]; rfl -- tune
include p in
lemma StormEq : (∑ i,cold H F (fU x.val) i) = ∑ i∈ Camp x.val H, storm F x i:=by
 let S:=cam x.val; have he:(Camp x.val H).biUnion (ice x.val)= S:=by
    unfold ice; rw [bask0 _ _ _ (fun i=>i)]
    rw [show (Camp x.val H).biUnion (fun i=>i)=_ from reconstruct ..]; ext i; exact Iff.intro (fun v=> (mem_filter.mp v).1) (fun v=> mem_filter.mpr ⟨v, fat_m x.val (shard_eq x v)⟩)
 refine part (ice x.val) _ _ univ (subset_univ _) (bits0 _ _ _ (fun i=> i) (different fan _)) (fun i _ q=>?_ ); rw [he] at q; exact if_neg q
include p u in
lemma seesCold (y:Visit A R H) (h:Along x.val y.val (Contour.station fan V)) : ice x.val V=ice y.val V∧storm F x V=storm F y V:=by
 have he: ice x.val V=ice y.val V:=by ext i; simp only [ice,chipAt,mem_filter]; exact and_congr_left fun v=> (h.controls i (estate0 v)).1
 refine ⟨he, (?_)⟩; unfold Huon.storm; rw [he]; exact sum_congr rfl fun i v=> u.coldRead p h i (fun k h=> mem_biUnion.mpr ⟨_, (mem_filter.mp v).2, stem_bay _ fixedR (stem_mid _ (by norm_num [fixedR] :3≤ fixedR) h)⟩) -- tune
end YM.CF.BPress.Huon
