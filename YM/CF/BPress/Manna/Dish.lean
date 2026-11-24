import YM.CF.BPress.Manna.Grains
/- integrated core ledger. No volume factor from unused blocks. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Manna
open Function Finset NormedSpace MeasureTheory Measure Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
attribute [local instance] Gauge.frobInner
variable {N:Side}{B:BandWidth}{A:Bands (More N) B} {R:Hangar (More N)}{H:Crew A}
open Huon Rates Env Mosaic
variable (K:Rates)
-- T core.Separate any D candidate. cost Middle. ballot count.
def towel (H: Crew A)(D Q: SlotT A R)(i: BlockY A R) (x: Realm B N R): ℝ:= if i∈D then Bad0 K H.y x else if i∈ NotT D Q then Good0 K x else 1
abbrev basket (H:Crew A)(D Q :SlotT A R)(x:Choir A R) := ∏ i∈ Q,towel K H D Q i (x i) -- used stamp datum
variable (D Q:SlotT A R)
lemma θ_pos (i:BlockY A R)(x:Realm B N R):0 ≤ towel K H D Q i x:=by unfold towel; split; exact bp ..; split; exact gp ..; exact zero_le_one
lemma θ_m (i:BlockY A R) : Envelope (towel K H D Q i):=by unfold towel; split; exact Bbe ..; split; exact Gbe ..; exact Law.fixedP _
lemma basket_pos (x:Choir A R):0 ≤ basket K H D Q x:= prod_nonneg fun i _=> θ_pos ..
lemma basket_env : Envelope (basket K H D Q):=by
 have he(S):Envelope (fun x:Choir A R=> ∏ i∈ S,towel K H D Q i (x i)):=by induction S using Finset.induction_on with|empty=> simp_rw [prod_empty]; exact Law.fixedP _|insert i s h ih=> simp_rw [prod_insert h]; exact (Env.along (θ_m ..) (g:=fun x:Choir A R=> x i) (measurable_pi_apply i)).mul ih
 exact he Q
variable {K D Q}
lemma NotTD : Disjoint D (NotT D Q):= disjoint_left.mpr fun i u v=> ((Finset.mem_sdiff.mp v).2) (petals u)
def Middle (D Q: SlotT A R) := Q \ (D∪NotT D Q)
lemma rejoin (p:D⊆Q) : (D∪ NotT D Q) ⊆ Q:= union_subset p Finset.sdiff_subset
lemma metag {M:Type*}[CommMonoid M](p:D⊆Q)(F:BlockY A R→M): ∏ i∈Q,F i=((∏ i∈D,F i)*(∏ i∈ NotT D Q,F i))*(∏ i∈Middle D Q,F i):=by rw [← prod_union NotTD,mul_comm]; exact (prod_sdiff (rejoin p)).symm
lemma torso {x: Choir A R}(S:SlotT A R) (v:Rates.admits H S x)(K:Rates):Real.exp (budgetP H K S x)≤ basket K H (debris H x S) S x:=by
 let D:=debris H x S; let G:=NotT D S; have hD:D⊆S:= inter_subset_right; rw [basket, metag hD]; let f(i):= towel K H D S i (x i); have ht:(∏ i∈G,f i)=Real.exp (-K.pay)^G.card:=by rw [←prod_const,Finset.prod_congr rfl (show ∀ i∈G,f i= Real.exp (-K.pay) from fun i h=> (?_ ))]; unfold f towel Good0; rw [if_neg (fun u=> disjoint_left.mp (NotTD (Q:=S)) u h), if_pos (show i∈ NotT D S from h),if_pos (show _ from (show curious (x i) from v i h))] -- tune
 let E:= Middle D S; let g:= fallout H x S; let Z:= Real.exp K.bad; let u:= Real.exp (-K.severe); let k:= ice x S; have he:(∏ i∈ E,f i)=1:= prod_eq_one fun i h=> by have he:= not_or.mp ((Finset.mem_sdiff.mp h).2 ∘ mem_union.mpr); unfold f towel; rw [if_neg he.1, if_neg he.2] -- tune
 have hY : Z^D.card*u^g.card ≤ ∏ i∈ D,f i:=by
    let q(i: BlockY A R):= if i∈g then u else 1; have hm : (∏ i∈ D,Z*q i)=Z^D.card*u^g.card:= by unfold q; rw [prod_mul_distrib,prod_const,←prod_filter,prod_const,filter_mem_eq_inter,Finset.inter_eq_right.mpr (show g⊆D from filter_subset ..)] -- tune
    rw [←hm]; apply Finset.prod_le_prod; · intro j _; apply mul_nonneg (Real.exp_pos _).le; unfold q; split; exact (Real.exp_pos _).le; exact zero_le_one
    intro i b; unfold q; rw [show f i=Bad0 K H.y (x i) from if_pos b]; simp only [g, fallout, show debris H x S=D from rfl,mem_filter,b,true_and]; exact relax K _ (debt_m x|>.1 ((mem_inter.mp b).1))
 change _≤ (∏ i∈ D,f i)*(∏ i∈ G,f i)*(∏ i∈ E,f i); rw [ht,he,mul_one]; apply le_trans _ (mul_le_mul_of_nonneg_right hY (by positivity)); unfold u Z; simp_rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_monotone; have hv:= mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr (spent_at (H:=H) x S)) K.yellow; unfold Rates.budgetP; change -(K.pay *(G.card:ℝ))+K.bad*(D.card:ℝ)-K.severe*k.card≤ _; change K.severe*(g.card:ℝ) ≤ K.severe*k.card at hv; linarith
lemma stars {v:Visit A R H→ℂ}{f: Choir A R→ℂ}(p:PaidQ Q K H v f)(x: Choir A R) : ‖f x‖ ≤ ∑ D ∈ Q.powerset, basket K H D Q x:=by
 by_cases b:f x=0; rw [b,norm_zero]; exact sum_nonneg fun _ _=> basket_pos ..
 apply le_trans ((p.budget _).trans (torso Q ((p.wake _ b).2) K)); exact single_le_sum (f:=fun D=> basket K H D Q x) (fun _ _=> basket_pos ..) (mem_powerset.mpr inter_subset_right)
end YM.CF.BPress.Manna
