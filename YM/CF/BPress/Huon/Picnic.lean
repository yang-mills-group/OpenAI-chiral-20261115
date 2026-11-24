import YM.CF.BPress.Huon.Chill
/-! Pointwise core support & pricetag of $RealXi$ factors. No time horizon in proofs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along
variable {m s N:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u b:ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Pilot
variable (B0: Born A R X Y) (P: Edition Y)(F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)(r:ℕ)
local notation "Ξ" => Visit A R H
variable {B0 P F Q r}
variable (L:Passports Y T G h P p3 q d ε t v)(K:ShortP X H R r)(w: Seer H R X k)
variable (x:Visit A R H)(Z:SlotT A R)
def leis(R:Hangar (More N))(B:BandWidth)(u:ℕ):ℕ:=R.L.val^3*(B.D+2*u+1)
def costη (R:Hangar (More N))(S:Pledge)(B:BandWidth)(u:ℕ):ℝ:= 2*(estate 29* leis R B u:ℕ)*S.price
include L K
lemma at_cost(i:Tenor η)(h:i∈ badcore x (fun i:Tenor η=>plan A R i.1) Z univ)(u:P.opfee i≠0)(g:Tiny A X r i.2):i.1∈clampS (Vista H x.val Z) (mcap X H r):=by
 exact fuel i.1 _ (mem_filter.mp h|>.2) (mem_filter.mp (Stripe.appointed L K i g u)|>.2.2)
lemma ζ_est(i:Tenor η) : ‖ζLeft B0 P F Q r x i‖≤ 2*P.opfee i:=by
 unfold ζLeft; split; next h=> unfold money; rw [if_pos h]; exact (norm_sub_le ..).trans ((add_le_add (L.known i _) (L.known i _)).trans_eq (two_mul ..).symm)
 next h=> rw [norm_zero]; exact mul_nonneg (by norm_num) (L.cruise.pos i)
lemma cost_story : ‖leftP B0 P F Q r x Z‖ ≤ ((debris H x.val Z).card:ℝ)*costη R p3 B (mcap X H r):=by
 let i:ℕ:= mcap X H r; let T:= badcore x (fun i:Tenor η=> plan A R i.1) Z univ; let V:= Vista H x.val Z; let g:= ζLeft B0 P F Q r x; let S:=T.filter fun i=>P.opfee i≠0∧Tiny A X r i.2; have he: ∑ i'∈T,g i'=∑ i∈ S,g i:= (sum_subset (filter_subset ..) (fun i p t=> (?_ ))).symm; swap
 · unfold g ζLeft; split; next f=> have he:P.opfee i=0:=Classical.byContradiction fun q=>t (mem_filter.mpr ⟨p,q,f⟩); unfold arts money; simp_rw [if_pos f,Stripe.due_iff L i he]; ring -- tune
   next h=>rfl
 let U: Seal (Site η):= clampS V i; have hp:=costη R p3 B i; let A':= Abyss.budget_at scaffold L.cruise p3.pos.le S U (fun i l=> let v:=mem_filter.mp l; ⟨i.1,at_cost L K x Z i v.1 v.2.1 v.2.2,L.point i v.2.1|>.2⟩)
 change ‖∑ i∈T,g i‖ ≤ _; rw [he]; refine (norm_sum_le ..).trans ((sum_le_sum (fun i l=> ζ_est (B0:=B0) L K x (F:=F) (Q:=Q) i)).trans ?_); rw [←mul_sum]; apply (mul_le_mul_of_nonneg_left A' (by norm_num : (0:ℝ)≤ 2)).trans; let u:=debris H x.val Z; have hx: U.card ≤ u.card * estate 29 * leis R B i:= (fuel_cost V (lowP K.μWide.le)).trans (Nat.mul_le_mul_right _ (vista_card ..)); refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) p3.bought.le) zero_le_two) ?_; push_cast; unfold costη; push_cast; unfold u i; exact le_of_eq (by ring) -- tune
include w in
lemma stories (y:Ξ)(h:Peel.Along x.val y.val (Contour.station Peel.fan Z))(v:Z∈Camp x.val H)(g: Z∈Camp y.val H):leftP B0 P F Q r x Z=leftP B0 P F Q r y Z∧ rightP B0 P r x Z=rightP B0 P r y Z :=by
 have ht:Vista H x.val Z=Vista H y.val Z:= paints_eq h; constructor
 · unfold leftP badcore; rw [← ht]; refine sum_congr rfl (fun i z=>?_ ); unfold ζLeft; split; next q=>
    by_cases b:P.opfee i≠0; swap; · unfold arts; rw [due_iff L _ (not_not.mp b),due_iff L _ (not_not.mp b)] -- tune
    apply congrArg (·- _); have he:=L.point i b; let V:=Peel.stem (plan A R i.1) 40; have hp:= shortBody (Abyss.foot A X.W.M he.1 q.1) he.1 q.2 K w.charter.port i.1 he.2 (by norm_num :7≤40); exact L.view i _ _ (hasP w hp (Peek.inner v g h (vista_demand ((mem_filter.mp z).2))) F Q)
   next h=> rfl
 unfold rightP Upper; rw [← ht]; apply sum_congr rfl; intro i v; apply congrArg _; exact (h.controls (porch A R i (Classical.arbitrary _)) (by rw [porch_own]; exact estate0 (show i∈ Z from (Finset.mem_sdiff.mp v).1))).2.1 -- tune owner `porch_own`
variable (pO:Even R.L.val)
structure Banner (B0: Born A R X Y)(h:ℕ)(c:ℝ) : Prop where
 fit :0<c
 shines(z:Fin 5): z≠0→ ShineZ B0 h c z
include F pO
lemma Bias_est {n:ℕ}(p:Banner B0 n C)(q:n≤ mcap X H r)(h:(B.D+2*mcap X H r+1:ℕ)*blur r p3≤ C/16)(v: Z∈ Camp x.val H): (rightP B0 P r x Z).re ≤ -(C/16)*(R.L.val:ℝ)^3 * (Upper H x.val Z).card:=by
 unfold rightP; rw [Complex.re_sum]; refine le_trans (sum_le_sum (g:=fun _=> -(C/16)*(R.L.val:ℝ)^3) ?_) ?_; · intro i l; rw [upper_l v] at l; obtain ⟨z,b⟩:= Finset.mem_sdiff.mp l; exact Lilac.Stripe.Qbias L _ (p.shines _ ((grade_t F x b).1 (pay_p x.val v z))) K q pO h i -- tune
 rw [sum_const,nsmul_eq_mul,mul_comm]
end Pilot
end YM.CF.BPress.Huon
