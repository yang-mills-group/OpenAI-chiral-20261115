import YM.CF.BPress.Mount.Mounting
/- deep decisions settle on all Rooted shell terms. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net Locale Push.AbsoluteSums -- ambiguity
variable {s m B N:Side} {D:BandWidth}(X:Bands s D)(i:X.Index)(r:ℕ)
def deep : Support s := (X.band i).filter fun i=> ¬ NearBlock X r i
lemma deep_sub : deep X i r⊆ X.band i := filter_subset ..
def abyss (S:Support s):Prop:= S.Nonempty∧ S⊆deep X i r
def currencyT (S:Support s) :Prop := ∀ i, ¬ abyss X i r S
lemma Abyss.uniqueX {i j:X.Index} {S:Support s}(q:abyss X i r S)(t:abyss X j r S): i=j:=by obtain ⟨x,v⟩:=q.1; exact Classical.byContradiction fun h=> Finset.disjoint_left.mp (X.band_disjoint h) (deep_sub X i r (q.2 v)) (deep_sub X j r (t.2 v))
lemma Abyss.foot {S:Support s}(p: Grove (field 4 s) S)(t:currencyT X r S): Locale.meets X r S:=by
 by_contra h; have ht(i:X.Index): Disjoint S (X.gap i):=by refine disjoint_left.mpr fun j q v=> h ⟨j,q,i,?_⟩; exact Wealth.time_zero X i _ ((Wealth.time_Zone ..).2 v) r
 obtain ⟨i,v⟩:= Wealth.pack_noGap X S p ht; exact t i ⟨ Grid.inhabited_grove p,fun i p=>mem_filter.mpr ⟨v p, fun x=>h ⟨_,p,x⟩⟩⟩
lemma Abyss.sum {I:Type*}[Fintype I][DecidableEq I](E:I→ Support s)(Q:I→ℂ): ∑ i,Q i= (∑ i:X.Index,(∑ j:I with abyss X i r (E j),Q j))+(∑ j:I with currencyT X r (E j), Q j):=by
 simp_rw [sum_filter]; rw [sum_comm, ←sum_add_distrib]; apply sum_congr rfl; intro j _; by_cases p:currencyT X r (E j); · rw [if_pos p,sum_eq_zero (fun i _=> if_neg (p i)),zero_add]
 rw [if_neg p,add_zero]; unfold currencyT at p; obtain ⟨x,h⟩:= not_forall.mp p; have ht:= not_not.mp h; rw [sum_eq_single x, if_pos ht]; intro i _ z; exact if_neg (fun p=>z (Abyss.uniqueX X r p ht)); simp -- tune capitalization
lemma Abyss.budget_at {I:Type*}[Fintype I] [DecidableEq I](E:I→Support s){Q:I→ℝ}{a b:ℝ}(h:Cash E Q a b)(g:0≤a)(T:Finset I) (S:Support s)(p:∀ i∈T, ∃ x∈S,x∈ E i): (∑ i∈T,Q i) ≤ (S.card:ℝ)*b:=by
 let F(i):= Ledger.score E Q a i; refine (sum_le_sum (g:=fun i=> ∑ t∈S, F t i) (fun i t=>?_)).trans ?_; · obtain ⟨x,w,u⟩:=p i t; refine (show Q i≤ F x i from (by unfold F Ledger.score; rw [if_pos u]; exact le_mul_of_one_le_left (h.pos ..) (Ledger.exp_one _ _ g))).trans (single_le_sum (fun j _=>(h.hits j).1 i) w) -- tune `_ g`
 rw [sum_comm]; exact (sum_le_sum (g:=fun _=>b) (fun i _=>budget_sum (h.hits _) _)).trans_eq (by rw [sum_const,nsmul_eq_mul])
lemma Abyss.budgetS {I:Type*}[Fintype I][DecidableEq I](E:I→Support s){Q:I→ℝ}{a b:ℝ}(h:Cash E Q a b)(g:0≤a): (∑ j:I with abyss X i r (E j), Q j) ≤ ((X.band i).card:ℝ)*b:=by
 refine budget_at E h g _ _ ?_; intro i' v; let w(i):= E i; have ht:= (mem_filter.mp v).2; obtain ⟨p,v⟩:= ht.1; exact ⟨_,deep_sub X i r (ht.2 v),v⟩ -- tune
end YM.CF.BPress.Mount
