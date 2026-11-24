import SatinThinCircuitry
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
namespace Garland
open Etch
variable {I J:Type*} [Fintype I][Fintype J] {Q:ℝ} (z:PlaqAxes→ℝ) {Υ:MvPolynomial I ℝ}
-- Touring records ALL pose displacements on gauge sites (not yet requiring center nodes). Support checked later.
variable {k b':ℝ} {C':Etch G J} (T:Tour I n)(W:Etch G J)
variable {L:Type*} [Fintype L] (Φ: L→Tour I n) (ρ:ℝ)
-- derivative & mean receipts. Everything in GAUGE coordinates (More n used thereafter).
abbrev sunstroke (s:ℕ)(q:Clip)(ρ:ℝ)(W:Etch G J):ℝ:= (1+W.arc)^s*s* W.lensLimit q ρ
lemma sun_pos (s:ℕ)(q:Clip):0≤ sunstroke s q ρ W:=by unfold sunstroke; have ht:= W.arc_non; have he:= W.lensLimit_non q ρ; positivity
lemma sun_mono (s:ℕ) (h:|ρ|≤|κ|): sunstroke s q ρ W ≤ sunstroke s q κ W:=by
 unfold sunstroke lensLimit Etch.rays; have hl:=W.arc_non; gcongr

private lemma bound_group (t:L→Signed)(o:L→Site n)(x y:Altar G n)(h: Injective o) : (∑ i:L,|W.chalk q ρ (t i) (o i) x-W.chalk q ρ (t i) (o i) y|) ≤ W.lensLimit q ρ*Real.sqrt (Fintype.card L)*‖x-y‖:=by
 let X(i:L)(b:Signed)(j:J):= ‖cup (slotFace (skewSlot G (W.slot j) b) (o i)) (x-y)‖; let a:ℝ:= W.favor * Etch.rays q ρ; have he:0≤a:=by unfold a Etch.rays; positivity
 let K:=Real.sqrt (Fintype.card L); refine (Finset.sum_le_sum (g:=fun i=> a* (∑ b:Signed,∑ j:J,X i b j)) (fun i _=> (W.chalk_steady q ρ (t i) (o i) x y).trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun b=> ∑ j:J, X i b j) (fun b _=> sum_nonneg (fun j _=> norm_nonneg _)) (mem_univ (t i))) he))).trans ?_
 rw [← mul_sum, Finset.sum_comm]; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _=> Fintype.card J*(K*‖x-y‖)) ?_) he).trans_eq ?_
 · intro i _; rw [Finset.sum_comm]; refine (Finset.sum_le_sum (fun u _=> cup_sum o h (skewSlot G (W.slot u) i) _)).trans_eq (?_)
   simp [K]
 rw [sum_const,card_univ,nsmul_eq_mul]; unfold lensLimit a K; ring
lemma everywhere (h: Stationed Φ) (x: Altar G n) : ‖fderiv ℝ (accountGl W ρ Φ (q:=q)) x‖ ≤ sunstroke (Fintype.card I) q ρ W * Real.sqrt (Fintype.card L):=by
 let D:=Fintype.card I; let N:ℝ≥0:=⟨_,mul_nonneg (sun_pos W ρ D q) (Real.sqrt_nonneg (Fintype.card L))⟩; apply norm_fderiv_le_of_lipschitz ℝ (C:=N); refine LipschitzWith.of_dist_le_mul (fun x y=>?_)
 let C:=1+W.arc; have hc:1≤C:=le_add_of_nonneg_right W.arc_non; let V(i:L)(q':I):= W.chalk q ρ ((Φ i).orient q') ((Φ i).loc q')
 let U' (i:I):= ∑ j:L, |V j i x - V j i y|; rw [dist_eq_norm,dist_eq_norm,accountGl,accountGl,← sum_sub_distrib,Real.norm_eq_abs]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun i:L=> C^D*∑ j,|V i j x-V i j y|) (fun i _=>?_)).trans ?_)
 · have ht(t:Altar G n)(j):|V i j t|≤ C:= (W.chalk_bound ..).trans (le_add_of_nonneg_left zero_le_one); apply products_margin (A:=fun j:I=>V i j x) (E:=fun j=> V i j y) univ (ht x) (ht y) hc|>.trans_eq ; rw [card_univ]
 rw [←mul_sum,sum_comm]; refine (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun i=> W.lensLimit q ρ * Real.sqrt (Fintype.card L)*‖x-y‖) ?_) (by exact pow_nonneg (zero_le_one.trans hc) _)).trans_eq ?_
 · intro i _; exact bound_group W ρ (fun j:L=> (Φ j).orient i) (interest Φ i) x y (h i)
 rw [sum_const,card_univ,nsmul_eq_mul]; change _ = sunstroke D q ρ W * _ * _; unfold sunstroke C D; ring -- tune rw
abbrev visionCost := clouds B P (T.reading W ρ (q:=q))
-- copy & mean
variable (Hθ:Bid.Sworn H n G)
structure Copied(T:Tour I n)(W: L→Tour I n):Prop where
   copy(i:L):∃ s x, W i=T.moves s x
lemma Copied.turn (h:Copied T Φ)(u:Signed)(b:Site n): Copied T (fun i=>(Φ i).moves u b):=by refine ⟨fun i=>?_⟩; obtain ⟨a,t,h⟩:=h.copy i; exact ⟨u*a,affine u b t,by rw [h,Tour.rules]⟩
lemma vision_limit : |visionCost B P T W ρ| ≤ W.arc^Fintype.card I:=by
 rw [←Real.norm_eq_abs]; refine (norm_integral_le_of_norm_le (μ:=stdGaussian (stamen B P n)) (f:= fun i : (stamen B P n)=> T.reading W ρ (q:=q) i.val) (g:=fun _=> W.arc^Fintype.card I) (integrable_const _) (Eventually.of_forall fun i=>?_)).trans_eq ?_
 · rw [Real.norm_eq_abs]; exact T.reading_cost W ρ _
 simp
include Hθ L_
lemma vision_any (s:Signed)(b:Site n) : visionCost B P (T.moves s b) W ρ=visionCost B P T W ρ:= (cover_calms s b B P L_ Hθ _ _ ((T.smooth_read (q:=q) W ρ).continuous) fun i=> T.reads_here ..).symm
lemma vision_burst (h:Copied T Φ): plumeCost B P (accountGl W ρ Φ (q:=q)) t= (Fintype.card L:ℝ)*(t*visionCost B P T W ρ):=by
 let H':= stamen B P n; have hx(C':Tour I n): Integrable (fun i:H'=> C'.reading W ρ (q:=q) i.val) (stdGaussian H'):= Regis.bree _ _ (((C'.smooth_read (q:=q) W ρ).continuous.comp continuous_subtype_val).measurable) (fun i=> C'.reading_cost W ρ (q:=q) i.val)
 have h(i:L): (∫ x:H',(Φ i).reading W ρ (q:=q) x.val ∂ stdGaussian H')= visionCost B P T W ρ:=by obtain ⟨s,t,h⟩:=h.copy i; rw [h]; exact vision_any B P L_ T W ρ Hθ s t
 rw [plumeCost, cloud_turn (n:=n) B P _ ((show ContDiff ℝ 1 (accountGl W ρ Φ (q:=q)) from ContDiff.sum (fun i _=> (Φ i).smooth_read W ρ)).continuous)]; unfold clouds accountGl; rw [integral_finsetSum univ (fun i _=>hx _)]; simp_rw [h]; simp; ring
omit Hθ L_
-- binned miss counts. cost polynomial grows but takes arbitrary tiny κ.
variable (π:0 < k)
include π
abbrev podFee (x v Q:ℝ) (R:Rules G)(k:ℝ)(π:0<k):ℝ:= meritG z*((x*Q)^4/k)+(amaryllis z G k π).priceS R x v
local notation:max "Yk"=> amaryllis z G k π
local notation:max "lostC"=> costG z p.threshold ρ
local notation:max "Γs"=> Fintype.card I
local notation "ΣC" => podFee z ρ v p.threshold R k π
local notation "A2" => ((Yk).arc)
local notation "ΣF" i:max=>withinCore r A (face_anchors (misdemean p.threshold U)) (hallBill m) i
variable {X Y:Regis.Head.Dir G n}
lemma inside_plan(h: (Yk).payroll ≤ m)(g:∀ i:I, withinCore r A (face_anchors (misdemean p.threshold U)) (hallBill m) (T.loc i))(hp:12≤ hallBill m)(l:TrustLogs (X+Y) U r A v)(K:0 ≤ v)(d:v ≤ R.c)(f:0<β) (hb:ΣC≤1): let Z:=starFeed B P r A (face_anchors (misdemean p.threshold U)) m Y β X; |T.exhibit z ρ p.threshold U-T.reading Yk (ρ*coupling β) (q:=q) Z| ≤ (1 + lostC)^Γs *(Γs * ΣC):=by
 intro V; let W:=1+lostC; let Υ(i:I):= ((Yk).chalk q (ρ*coupling β) (T.orient i) (T.loc i) V); let P'(i:I):= garland z ρ p.threshold (T.orient i) (T.loc i) U; have ht:1≤W:=le_add_of_nonneg_right (by unfold costG meritG; positivity); have hh(i:I): |P' i|≤ lostC:= costG_le ..; have he(i:I): |P' i-Υ i|≤ΣC:= garland_match z B P R π h (T.orient i) (g i) hp l K d f -- arg z
 have hx(i:I): |Υ i| ≤ W:=by have hg:= norm_le_norm_sub_add (Υ i) (P' i); rw [norm_sub_rev,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs] at hg; exact hg.trans (add_le_add ((he i).trans hb) (hh i))
 change |(∏ i,P' i)- (∏ i,Υ i)|≤_; refine (products_margin univ (fun i=> (hh i).trans (le_add_of_nonneg_left zero_le_one)) hx ht).trans ?_; rw [card_univ]; exact mul_le_mul_of_nonneg_left ((sum_le_sum (fun i _=> he i)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])) (pow_nonneg (zero_le_one.trans ht) _)
-- 4-phase checks. Q.either.
lemma panorama_stipend (h: (Yk).payroll ≤ m)(h0:12≤ hallBill m)(l: Odd r.count.val)(u:hallBill m ≤ r.count.val/2)(hS:0 ≤ v)(e:v ≤ R.c)(d:0<β)(hb: ΣC ≤ 1)(hp: Stationed Φ) (cw:0≤ w) {ε:ℝ} (G': |t| *(lostC^Γs+ A2^Γs)*Γs ≤ 4*w) (Y0:Finset (Cell n)): ShelfScene B P p r m β v ε ( (1+lostC)^Γs * Γs * ΣC * |t| * Fintype.card L + w*(trap r m A+trap_s m Y0)) A Y0 t (panorama z ρ Φ p.threshold) (accountGl Yk (ρ*coupling β) Φ (q:=q)):=by -- ε bind later
 intro U V Y _ h' _ h1; let E:=univ.filter fun i:L=> ¬∀ j:I, withinCore r A (face_anchors Y0) (hallBill m) ((Φ i).loc j); let F:=starFeed B P r A (face_anchors Y0) m Y β V
 let T:=fun i:L=> (Φ i).exhibit z ρ p.threshold U - (Φ i).reading Yk (ρ*coupling β) (q:=q) F; let v':= lostC; let z':= v'^Γs + A2^Γs; have he:0≤v':=by unfold v' costG meritG; positivity
 let P':=Γs; let R:= (1+v')^P' * P' * ΣC; have ht:0≤R:=by
    have hf:0≤ΣC:= by unfold podFee; refine add_nonneg ?_ ((amaryllis z G k π).priceS_pos ..); unfold meritG; positivity -- tune
    unfold R; positivity
 have hB (i:L): |T i| ≤ R+if i∈E then z' else 0:=by
    split; next=> exact (abs_sub ..).trans ((add_le_add ((Φ i).exhibit_cost z ρ) ((Φ i).reading_cost ..)).trans (le_add_of_nonneg_left ht))
    rename_i hW; rw [add_zero]; have he:∀ j:I, withinCore r A (face_anchors Y0) (hallBill m) ((Φ i).loc j):= of_not_not (fun e=>hW (mem_filter.mpr ⟨mem_univ _,e⟩)); subst Y0; refine (inside_plan B P z (Φ i) ρ π h he h0 h1 hS e d hb).trans_eq ?_; unfold R v' P'; ring -- extra? name h₁ etc shadowing
 have hY: E.card ≤ Fintype.card I * (Fintype.card (Site c)* largerBill r.count.val (hallBill m)+A.card*r.count.val^4+Y0.card*coldBill (hallBill m)):=by -- c shadow
    let N(j:I):= univ.filter fun i:L=> ¬ withinCore r A (face_anchors Y0) (hallBill m) ((Φ i).loc j)
    refine ((card_le_card (show E ⊆ univ.biUnion N from ?_)).trans (card_biUnion_le ..)).trans (?_)
    · intro i p; obtain ⟨j,y⟩:= not_forall.mp (mem_filter.mp p).2; exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨mem_univ _,y⟩⟩
    have he(j:I): (N j).card≤ _:= (Eq.ge (card_image_of_injective (N j) (hp j))).trans ((card_le_card (show (N j).image (interest Φ j) ⊆ univ.filter (fun i=> ¬ withinCore r A (face_anchors Y0) (hallBill m) i) from ?_)).trans (land_fee A Y0 l u))
    · simpa using sum_le_sum (fun (j:I) (_: j∈univ)=>he j)
    intro i z; obtain ⟨k,p,rfl⟩:= mem_image.mp z; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩
 apply (sub_le_iff_le_add').1; unfold panorama accountGl; rw [←mul_sub, ←sum_sub_distrib]; refine (le_abs_self _).trans ?_; rw [abs_mul]; refine (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=> hB i))) (abs_nonneg _)).trans ?_; rw [sum_add_distrib,←sum_filter]; simp only [sum_const,card_univ,nsmul_eq_mul,filter_mem_eq_inter,univ_inter] -- tune; arithmetic
 let μ:ℝ:= Fintype.card (Site c)* (largerBill r.count.val (hallBill m):ℕ)+A.card*(r.count.val:ℝ)^4+Y0.card*(coldBill (hallBill m):ℕ)
 have hu:(E.card:ℝ) ≤ Γs * μ:= by refine (Nat.cast_le (α:=ℝ).2 hY).trans_eq ?_; unfold μ; push_cast; ring
 rw [show trap r m A+trap_s m Y0=4*μ from by unfold trap trap_s μ; ring]
 change |t| *((Fintype.card L:ℝ)*R+E.card*z')≤ R* |t| * Fintype.card L+w*(4*μ); have hp:0≤z':=by unfold z'; have _h:=(Yk).arc_non; positivity
 nlinarith only [mul_le_mul_of_nonneg_left hu (show 0≤ |t| * z' from mul_nonneg (abs_nonneg t) hp),mul_le_mul_of_nonneg_left G' (show 0 ≤ μ from (by unfold μ; positivity))]
end Garland
end YM.Regis.Head
#print axioms YM.Regis.Head.Garland.panorama_stipend
#print axioms YM.Regis.Head.Garland.vision_burst
#print axioms YM.Regis.Head.Garland.everywhere
