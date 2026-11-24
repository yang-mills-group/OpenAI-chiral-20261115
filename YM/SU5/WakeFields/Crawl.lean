import YM.SU5.WakeFields.AnchorPrice

/-!
# Margin for a no-registration leg

Some vials (even though their operators aren't small pretilt or at top price) have TWO
separate *cool* supplies: relative to one AND birth relative to Q. May suppress all
principal-core reports by spending some of these gains, in the FULL dictionaries, not just
on Bra. No claim they can be read for free. Price on the same clock as other Shelf.
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson RG Scroll Fock Cadre Stax Mew Roots
open Push.AbsoluteSums Trees Ione MeasureTheory Finset
open Cube Lat Tulip Skye Scree Hake Jet Sault Vow Vow.TreasuryFog Rive Larch
open scoped Topology ContDiff BigOperators Classical YM.CF.Mew Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Palot Leaf Rill
namespace Crawl
variable {I:Type}[LinearOrder I][Fintype I]
variable {n : Side}{P:BudgetPoint}{h a b c d:ℝ}{q l:ℕ}(o: Seat n)
-- use >= l where l of order dilation L, gets past `chose`
abbrev width (l:ℕ) : ℕ:= 16*(l+1)
abbrev till (P : BudgetPoint) (l:ℕ) :ℕ:= width l * P.B
lemma nonhalo (l:ℕ) (B:Side)(x:Site B)(p:2*l≤ B.val) : ∃ y, separation x y=l:=by
 let F(i:Axis):ℤ:=l; let Y:=wrap B F
 have h:B.val>0 := B.property; have ht:Lattice.lift Y=F:= lift_eq_iff.mpr ⟨rfl, fun i=> by unfold F; omega⟩
 refine ⟨Y+x,?_⟩; rw [separation_comm x, separation,add_sub_cancel_right,pdist,ht]; unfold F -- cast
 apply le_antisymm
 · exact Finset.sup_le fun _ _=>Int.natAbs_natCast l|>.le
 simpa [Int.natAbs_natCast] using (Finset.le_sup (s:=univ) (b:= (0:Axis)) (f:=fun _=>(l:ℤ).natAbs) (mem_univ _)) -- tune simp may transform goal to True not simplify sup.Nat
abbrev bloomC (P:BudgetPoint)(l:ℕ)(o:Seat n) : Support (More n):= halo (till P l) {o}
lemma host (P:BudgetPoint)(l:ℕ) : o ∈ bloomC P l o:= halo_subset _ _ (mem_singleton_self _)
lemma bloomDist (P:BudgetPoint)(l:ℕ) (p:2*Crawl.till P l ≤ (More n).val): l ≤ coverNumber P.B (bloomC P l o) := by
 let G:= bloomC P l o; obtain ⟨y,t⟩:= nonhalo (till P l) (More n) o p; have ht: y ∈ G:=halo_spec.mpr ⟨o,mem_singleton_self _, t.le⟩
 have he: separation o y ≤ coverNumber P.B G*(4*P.B+2)+2*P.B:= Corona.extent _ P.B (host o P l) ht
 let Z:= coverNumber P.B G; have hx:P.B > 0:= P.B_pos; rw [t] at he; change width l* P.B ≤ Z* _+2* P.B at he; unfold width at he
 change l ≤ Z; suffices v:l* P.B≤ Z*P.B from Nat.le_of_mul_le_mul_right v hx
 nlinarith only [he,hx, Nat.zero_le Z, Nat.zero_le l]
variable (P)
def skyline (o:Seat n)(l:ℕ)(X:Aura n): Aura n:=⟨X.val∪bloomC P l o, o, mem_union_right _ (host o P l)⟩
def costLoss (l:ℕ)(w:ℝ):ℝ:= Real.exp (w*(((width l+ width l+1)^4:ℕ):ℝ))
lemma glaze (l:ℕ) (X:Aura n) (v:0 ≤ a) (q:o∈X.val) : tact a P.B (skyline P o l X) ≤ tact a P.B X*costLoss l a := by -- arg order
 let G:= X.val∪bloomC P l o
 have he: coverNumber P.B G ≤ coverNumber P.B X.val + coverNumber P.B (bloomC P l o):= Corona.meets_sum q (host o P l) P.B
 have hh:=Corona.tile o (width l) P.B P.B_pos; change coverNumber P.B (bloomC P l o)≤_ at hh
 have hs:=he.trans (Nat.add_le_add_left hh _); unfold tact costLoss; rw [←Real.exp_add, ←mul_add]; refine Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ v); unfold widthK; exact_mod_cast hs
variable {P} (w u:ℕ)
local notation "Ξ"=>skyline P
variable {K:Bag n}
def aurora (P:BudgetPoint)(o:Seat n)(l:ℕ)(K:Bag n) : Bag n:= fun X=> ∑ i∈ univ.filter (skyline P o l · = X), K i
lemma planted (g: Barrage P q ({o}:Support (More n)) h K a b c) (v:0≤a) :
 Barrage P q (bloomC P u o) h (aurora P o u K) a (costLoss u a*b) (costLoss u a*c):=by
 obtain ⟨f,t,x,k,z,r⟩:=g.price; let F(i:Aura n):= Ξ o u i
 let part(X:Aura n):= univ.filter (fun i=> F i=X)
 have hX(X:Aura n)(v:¬bloomC P u o⊆ X.val):part X=∅:=by
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun i t=>v ?_); rw [←(mem_filter.mp t).2]; exact subset_union_right
 let Y(f:Aura n→ℝ)(X:Aura n):= ∑ i∈part X,f i
 refine ⟨Y f,Y t,?_,fun i p=>?_,?_⟩
 · intro X; refine Flight.whole (part X) K f t (fun i v=>?_)
   rw [←(mem_filter.mp v).2]; exact (x i).mantle subset_union_left
 · have he:=hX i p; unfold Y; change ((∑ j∈part i,_)=0 ∧ _); rw [he]; simp
 let G:= costLoss u a
 have hr(t:Aura n→ℝ)(p:0≤t)(h:∀ i:Aura n,o ∉ i.val→ t i=0){b:ℝ}(q:voyageB t P.B a≤ b): voyageB (Y t) P.B a≤ G*b:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left q (Real.exp_pos _).le); unfold voyageB; rw [Finset.mul_sum, ←Finset.sum_fiberwise_of_maps_to (s:=univ) (g:=F) (t:=univ) (fun i _=>mem_univ _) (f:=fun x=>G*(t x*tact a P.B x))]
    unfold Y; apply sum_le_sum; intro j _; rw [sum_mul]; refine sum_le_sum fun i u=>?_ ; by_cases x:o∈i.val
    · rw [←(mem_filter.mp u).2]; exact (mul_le_mul_of_nonneg_left (glaze P o _ i v x) (p i)).trans_eq (by unfold G; ring)
    rw [h i x]; simp
 refine ⟨hr f (fun i=> (x i).tube.price) (fun i u=> (k i (by simpa using u)).2.1) z, hr t (fun i=>?_ ) (fun i u=> (k i (by simpa using u)).2.2) r⟩
 obtain ⟨j,h,-⟩:=(x _).forms; exact h.price
lemma sameModel (K:Bag n) : (∑ i:Aura n, aurora P o l K i)=∑ i:Aura n, K i:= by
 exact Finset.sum_fiberwise_of_maps_to (s:=univ) (t:=univ) (g:= skyline P o l) (fun i _=> mem_univ _) (f:=K) -- maybe direction
lemma rescue (p':2*Crawl.till P l ≤ (More n).val)(j:Aura n)(t: coverNumber P.B j.val < l): aurora P o l K j=0 := by
 apply sum_eq_zero; intro Y v; refine False.elim (Nat.not_lt_of_ge ((bloomDist o P l p').trans (Corona.cover_mono (show bloomC P l o ⊆ j.val from (mem_filter.mp v).2 ▸ subset_union_right) _)) t)
lemma retreatCore (A W: Support (More n)) (K:Bag n) (v:Barrage P q A h K a b c)(w:W ⊆ A):Barrage P q W h K a b c:=by
 obtain ⟨R,Q,x,t,s,h⟩:=v.price; exact ⟨R,Q,x,fun i v=>t _ (fun q=>v (w.trans q)),s,h⟩
end Crawl
end YM.CF.Sour
#print axioms YM.CF.Sour.Crawl.planted
#print axioms YM.CF.Sour.Crawl.rescue
