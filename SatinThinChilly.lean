import YM.SU5.Regis.Hospitality
import SatinThinAngstrom
set_option autoImplicit false
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule
open Gleam Matrix Next.SectorChange Next.SectorChange.Gaussian
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {n c:Side}{r: Ratio c n}{G:Gauge}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β ε : ℝ}{T:Support c}{D:ChartRatio G}{Z:PathData G}{I J:Type*}


abbrev coldBill (m:ℕ):=(m+m+1)^4
lemma bounties (m:ℕ)(b:Finset (Cell n)): (univ.filter (fun i=>¬untouched (face_anchors b) m i)).card ≤ b.card*coldBill m:=by
 apply (card_le_card (show (univ.filter (fun i=> ¬untouched (face_anchors b) m i))⊆halo m (face_anchors b) from fun i p=> Classical.not_not.mp (mem_filter.mp p).2)).trans
 exact (Corona.halo_size ..).trans (Nat.mul_le_mul_right _ card_image_le)
lemma land_fee (A:Support c)(Z:Finset (Cell n)) (t:Odd r.count.val)(u:m ≤ r.count.val/2) : (univ.filter (fun i=> ¬ withinCore r A (face_anchors Z) m i)).card ≤ Fintype.card (Site c)* largerBill r.count.val m + A.card * r.count.val^4 + Z.card*coldBill m:=by
 let X:= univ.filter fun i:Site n=> ¬Safe r A m i; let Y:= univ.filter fun i=> ¬untouched (face_anchors Z) m i
 apply (card_le_card (show _⊆ X∪Y from ?_)).trans ((card_union_le ..).trans (Nat.add_le_add (cool_home t u) (bounties ..))) -- metavar scope
 intro x h; by_cases p:Safe r A m x; exact mem_union_right X (mem_filter.mpr ⟨mem_univ _,fun s=> (mem_filter.mp h).2 (show withinCore r A (face_anchors Z) m x from ⟨p,s⟩)⟩); exact mem_union_left Y (mem_filter.mpr ⟨mem_univ _,p⟩)
variable {T':Forest r}{F:Finset T'.Free}
lemma killed_number (A:Support c)(Z:Finset (Cell n)) (t:Odd r.count.val)(u:hallBill m ≤ r.count.val/2) : F.card-(cloak T' F A Z m).card ≤ 4*( Fintype.card (Site c)* largerBill r.count.val (hallBill m) + A.card * (r.count.val^4) + Z.card*coldBill (hallBill m)):=by
 let L:= hallBill m
 let S:= univ.filter fun i=> ¬withinCore r A (face_anchors Z) L i
 rw [← card_sdiff_of_subset (cover_c.trans (inner_part (a:=F)))]; let B:= F \ cloak T' F A Z m; let X:= (univ:Finset Axis); refine (card_le_card (s:=B.image Subtype.val) (t:=S ×ˢ X) ?_).trans ?_ |>.trans' ?_
 · intro x ht; obtain ⟨y,z,rfl⟩:= mem_image.mp ht; obtain ⟨v,g⟩:=mem_sdiff.mp z; exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,fun H=>g (mem_filter.mpr ⟨mem_filter.mpr ⟨v,H.1⟩,H.2⟩)⟩,mem_univ _⟩ -- type mismatch unresolved
 rw [card_product,mul_comm S.card, card_univ, show Fintype.card Axis=4 from Fintype.card_fin _]; exact Nat.mul_le_mul_left _ (land_fee A Z t u)
 rw [card_image_of_injective B Subtype.val_injective]
lemma cloak_growth {F':Finset T'.Free} {A:Support c} {Z:Finset (Cell n)} (g:F'⊆ F) : cloak T' F' A Z m ⊆ cloak T' F A Z m:= filter_subset_filter _ (filter_subset_filter _ g) -- tune
end YM.Regis.Head
#print axioms YM.Regis.Head.killed_number
