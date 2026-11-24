import YM.CF.BProof.Trek.Ripe
/-! Mark changes only in 𝒟. root coverage for \mathsf P and optional phases. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c a:Side} (Y:Yard (More s)) (g: Ratio c (More s))(r:ℕ)(B:Blocks Y c)
def eraseBit := univ.filter (fun x : Site s=> Y.Vic (tag Y (node x)) r (time (node x)) ∧ ¬ distant Y g B (node x) 6)
lemma erase_p {x:Site s}: x∈ eraseBit Y g r B ↔ Y.Vic (tag Y (node x)) r (time (node x)) ∧ ¬ distant Y g B (node x) 6:= by simp [eraseBit] -- tune
lemma pins_ne : Disjoint (Pins Y g B) (eraseBit Y g r B) := disjoint_left.mpr fun _ a b=> (erase_p ..|>.1 b).2 (pins ..|>.1 a).2
lemma eraseD (x:Site s)(h:¬dark Y (node x)): x∈ eraseBit Y g r B ↔ x∉Pins Y g B:= by have he:= Y.outside_gap _ r _ (mem_strip.mp (show node x∈Y.gap (tag Y (node x)) from gap_pick Y (node x) h)); simp only [erase_p,pins,h,not_false_eq_true,true_and,he]
lemma pad_sector(x:Site s)(u:x ∈ eraseBit Y g r B): ∃ a∈B, House.addr Y g (node x)∈ House.ray Y a 6 := by
 have hp:= ((erase_p ..).mp u).2; obtain ⟨y,z,h⟩:= Finset.not_disjoint_iff.mp hp; obtain ⟨p,t⟩:= (House.ray_spec ..).1 h -- g shadow!
 refine ⟨y,z,(House.ray_spec ..).2 ⟨?_,t.symm⟩⟩; rw [Grid.dist_symm]; exact p
lemma erase_budget (u:2*r+1<Y.long) : (eraseBit Y g r B).card ≤ ((Y.short+2*r+1)*g.count.val^3) * ((2*6+1)^4 * B.card):=by
 let T(b:House.Block Y c):= univ.filter fun x:Site (More s)=> House.addr Y g x=b∧ ∃ i,Y.Vic i r (time x)
 let F:=B.biUnion fun b=> House.ray Y b 6; let X:=eraseBit Y g r B; have h:X.card=(spot X).card:= (card_image_of_injective X Tenant.needle).symm
 have he:F.card≤ (2*6+1)^4 * B.card:= by
    apply card_biUnion_le.trans; apply le_trans (sum_le_sum (fun b _=> House.ray_pay Y b 6)); rw [sum_const,nsmul_eq_mul,mul_comm]; exact le_rfl
 apply le_trans (h.le.trans (card_le_card (t:=F.biUnion T) ?_)); swap
 · intro y hx; obtain ⟨x,w,rfl⟩:= spotsNN _ hx; obtain ⟨a,p,h⟩:= pad_sector Y g r B x w; apply mem_biUnion.mpr; refine ⟨_,mem_biUnion.mpr ⟨_,p,h⟩,mem_filter.mpr ⟨mem_univ _,rfl,_, (erase_p ..|>.mp w).1⟩⟩ -- Union args order
 apply card_biUnion_le.trans; refine ((sum_le_sum (fun x _=> House.senior Y g r x u)).trans ?_); rw [sum_const,nsmul_eq_mul,mul_comm]; gcongr; exact_mod_cast he

namespace Permit
variable {Y g r B}{u v d:ℝ}{H:Herald u v}{t:ℕ}{C:Sized t H.whole}{D:Script Y}{F U:Bkg (More s)}{δ:ℝ}{f:Ratio a (More s)}
variable (L: Pad Y H C g.count.val)(p:Permit D C U g B d)(T:4≤a.val)(W:f.count=H.whole) (e:Lamp C g B δ U F)(S:Sound Y H C d)
include p S T W L e
lemma erase_ok (p':C.nearM ≤ r)(x:Site s){i:Y.Index}(hx:node x∈ Y.band i)(h:x∉ eraseBit Y g r B): D.HH C g B F f (node x) 2=D.K i (node x) 2 := by
 let A:= node x; rcases Decidable.em (Y.Vic (tag Y A) C.nearM (time A)) with hp|hp <;> apply Eq.trans (b:=D.port C (node x) 2) _ (p.seatM D C U g B L hx)
 · rw [(p.expand_true L S T W e A (.inr ?_)).2.2] -- tune A defeq
   by_contra v; exact h ((erase_p ..).2 ⟨Y.vic_nearer _ _ _ r p' hp,fun u=> v (clear_weaker Y g B _ _ u (by decide : 3≤6))⟩)
 rw [(p.expand_true L S T W e _ (.inl hp)).2.2]
lemma continuityBudget{r':ℕ}(u:C.nearM ≤ r'){x:Site (More s)}{i:Y.Index}(h:x∈Y.band i)(hx: ¬Y.Vic (tag Y x) r' (time x)): D.HH C g B F f x=D.K i x ∧ D.XX C g B F f x=D.X i x∧ x∈ ChillF Y g B C.blockY:=by
 have he:=p.expand_true L S T W e x (.inl (fun p=> hx (Y.vic_nearer _ _ _ r' u p))); exact ⟨he.2.2.trans (p.noVac D C U g B L h (fun p=> hx (Y.vic_nearer _ _ _ r' (L.nearP.le.trans u) p))), he.2.1.trans (D.over_band i x h),he.1⟩
end Permit
end YM.CF.BProof.Trek
