import GaugeFieldConstruction.Icing

/-! # Tax port in the switchboard through power heights. Keep a thick grey charge but without coarsening *every* tau defect out to those heights: drop only logarithmic halo near tau defects. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology ENNReal Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}


variable (B:Z.Bounds q η C S)
variable {L:Flaws n}

def abandons_A (v:fieldDir G n 1)(r:Ratio c n)(X:Support c)(L:Flaws n)(k:ℕ): Prop:=∀ b: Edge (Site n), collect G v b ≠ 0 → Brisk r X L (Sequest k+Sequest k) b.1
-- not keep base iff NEGLIGIBLE deep
private lemma silent_M (h:abandons_A X r A L m)(p:¬ heldHigh r A L m b)(f:Cell n)(t:separation b.1 f.1 ≤ m) : faceCurl f X=0:=by
 have he:= grantFace (X:=X) (k:=f) (m:=4) (o:=f.1) (v:=0) (fun u v=> ?_) (by simp); · exact norm_le_zero_iff.mp (he.trans_eq (mul_zero _))
 rw [show collect G X u=0 from ?_, norm_zero]; by_contra he; apply p; apply (h u he).shift; unfold Sequest; rw [separation_comm]; apply Nat.add_le_add_right (k:=m+4) ?_; exact (separation_triangle ..).trans ((Nat.add_le_add t v))

include B
private lemma price_Va (D:ℕ→G.Color)(h:∀ i:ℕ, let k:= (Z.row b.2 i).2.length; ‖D i‖≤ v * Real.exp (η*k))(p:0 ≤ v) : let F:ℕ→G.Color:= fun i=> (Z.row b.2 i).1 • D i; Summable F ∧ ‖∑' i,F i‖ ≤ C*v:=by
 intro F; let Ψ:= (fun i=> |(Z.row b.2 i).1| *Real.exp (η*(Z.row b.2 i).2.length)); have ht:= B.rows b.2
 have he (i:ℕ): ‖F i‖ ≤ Ψ i*v:=by unfold F Ψ; rw [norm_smul,Real.norm_eq_abs,mul_right_comm]; exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))|>.trans_eq (by ring)
 have hf : Summable fun i=> Ψ i * v:= ht.2.1.mul_right _; have hx:Summable (fun i=> ‖F i‖):=hf.of_nonneg_of_le (fun _=>norm_nonneg _) he; exact ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he hf).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 p))⟩
private lemma lean_M (h:ProbeBox X v)(w:0≤v) : ‖ellLine Z b X‖ ≤ C*(4*v):=by
 apply (price_Va B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) _ (by positivity:0 ≤ 4*v)).2; intro i k; have hr:=B.width; exact (all_probe h _).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))

omit B in
private lemma tail_M {q:ℕ}(hm:m<q)(he:0 ≤ η): 1 ≤ trail η m * Real.exp (η*(q:ℝ)):=by unfold trail; rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hm.le) he]
lemma lost_M (g:ProbeBox X v)(h:abandons_A X r A L m)(t:¬ heldHigh r A L m b)(w:0 ≤ v): faceCurl b X=0 ∧ ‖ellLine Z b X‖ ≤ C*(4*v*trail η m):=by
 refine ⟨silent_M h t _ (by simp),?_⟩; have hp:0 ≤ 4*v*trail η m:=by unfold trail; positivity
 refine (price_Va B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) (fun i=>?_) hp).2
 intro k; let F:=(Z.row b.2 i).2; by_cases l:k ≤ m
 · have he:separation b.1 (slotFace F b.1).1 ≤ m:= (Work.E04.slot_separation F b.1).trans l; change ‖faceCurl (slotFace F b.1) X‖≤ _; rw [silent_M h t _ he,norm_zero]; exact mul_nonneg hp (Real.exp_pos _).le
 refine (all_probe g _).trans (le_trans (le_mul_of_one_le_right (by positivity:0 ≤4*v) (tail_M (lt_of_not_ge l) B.width.le)) (le_of_eq ?_)); ring

def recruit (Z:PathData G) (q:Clip) (r:Ratio c n)(A:Support c)(L: Flaws n)(m:ℕ)(b:Cell n)(X Y:fieldDir G n 1): ℝ:= if heldHigh r A L m b then research Z q b (X+Y) else research Z q b X
omit B in
private lemma arpa {x y : G.Color}{D d:ℝ}(p:‖x-y‖≤D)(h:‖y‖≤d) : ‖y‖^2 ≤ ‖x‖^2 + (2*D*d):=by
 rcases le_total ‖y‖ ‖x‖ with h1|h1
 · refine le_trans (pow_le_pow_left₀ (norm_nonneg y) h1 _) (le_add_of_nonneg_right ?_); have he:0 ≤ D:= le_trans (norm_nonneg _) p; have hp :0≤d:= (norm_nonneg _).trans h; positivity
 have he: 0≤D:=(norm_nonneg _).trans p; have hw: ‖y‖-‖x‖ ≤ D:= (norm_sub_norm_le y x).trans ((norm_sub_rev ..).trans_le p)
 have hz:=mul_le_mul_of_nonneg_left hw (show 0 ≤ ‖y‖+‖x‖ from by positivity)
 nlinarith only [hz,mul_le_mul_of_nonneg_right h1 he,mul_le_mul_of_nonneg_right h he]

-- spend jointly. Z includes tau at threshold; b∈ L is STRICT.
omit B in
lemma baseReserve (T:ℝ)(ht:p.threshold ≤ T) : (if b∈misdemean p.threshold U then q.linear*p.threshold^2/2 else 0) + (if b∈misdemean T U then q.linear*p.threshold*T/2 else 0) ≤ Z.baseTerm q p U b:=by
 let d:=G.chord (faceValue U b); have hp:=p.threshold_pos; have he:=q.tail_pos; have hx:0 ≤ q.linear*p.threshold:= mul_nonneg he.le hp.le
 by_cases h:b∈misdemean T U
 · have h':T ≤ d:= ((mem_filter.mp h).2.le) -- tune
   have h₁:b∈misdemean p.threshold U:= mem_filter.mpr ⟨mem_univ _,ht.trans_lt (mem_filter.mp h).2⟩
   apply le_trans (b:=PathData.clipped q p.threshold d); swap; · unfold PathData.baseTerm; apply le_add_of_nonneg_right; split; positivity; rfl
   rw [PathData.clipped, if_neg (not_le_of_gt ((mem_filter.mp h₁).2)), if_pos h, if_pos h₁]
   linarith only [mul_le_mul_of_nonneg_left h' hx, mul_le_mul_of_nonneg_left (ht.trans h') hx]
 rw [if_neg h, add_zero]; apply le_trans _ (@base_malaise ..)
 split
 next l=> exact half_le_self (mul_nonneg he.le (sq_nonneg _))
 next l=> exact le_rfl

lemma tax_A (T₀:ℝ)(ht:p.threshold ≤ T₀)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v) (w:abandons_A X r A (misdemean p.threshold U) m) (l:EnoughMark q p m)(p':0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C) : recruit Z q r A (misdemean p.threshold U) m b X Y + (if b∈misdemean p.threshold U then q.linear*p.threshold^2/2 else 0) + (if b∈misdemean T₀ U then q.linear*p.threshold*T₀/2 else 0) ≤ Z.baseTerm q p U b + Δ₁ R q v m η C:=by
 let t:=p.threshold; let k:=insideB r (broken r t U) m b; let d:= G.chord (faceValue U b); have d0:0 ≤ d:= G.chord_nonneg _; have h0:=p.threshold_pos; have hL:=q.quadratic_pos
 have hδ : 0 ≤ faceCutError R v:=by unfold faceCutError; have h:=G.colorScale_pos; have xv:=R.positive; positivity
 let F:= acry R v m η C; have he:0 ≤ acry R v m η C:= acry_zero hv p'
 have v0:0≤ C*(4*(2*v)):=by positivity
 unfold recruit; split
 next g0 =>
    have hf:b ∉ misdemean p.threshold U:= fun z=> Nat.lt_irrefl (Sequest m) (lt_of_lt_of_le (g0.2 b z) (by simp))
    have hh:b∉misdemean T₀ U:= fun z=> hf (mem_filter.mpr ⟨mem_univ _,ht.trans_lt (mem_filter.mp z).2⟩)
    have hl (b':Cell n)(z:separation b.1 b'.1 ≤ Sequest m) : G.chord (faceValue U b') ≤ t:=by
       by_contra! ht'; exact not_le.mpr (g0.2 b' (mem_filter.mpr ⟨mem_univ _,ht'⟩)) z
    have hd:d ≤ p.threshold:= hl b (by simp)
    have hgk:PathData.kept q t b.1 U:= by
       intro f; by_cases h:separation b.1 f.1 ≤ Sequest m; · exact (hl f h).trans (le_mul_of_one_le_right h0.le (Real.one_le_exp (div_nonneg (by positivity) q.radius_pos.le)))
       exact (G.chord_le_two _).trans ((show 2≤ p.threshold * Real.exp ((Sequest m:ℕ)/ (q.relaxation:ℝ)) from l).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr ((le_of_not_ge h))) q.radius_pos.le)) h0.le))
    rw [if_neg hf,if_neg hh,add_zero,add_zero,PathData.baseTerm,PathData.clipped,if_pos hd,if_pos (show PathData.kept q p.threshold b.1 U from hgk),research]
    have hF:= arpa (angleFaceSmall h p' t' b (g0.1.shift (y:=b.1) (by simp [Sequest]))).2 (all_probe g b)
    have hw:= arpa (payLine B g h p' t' g0.1) (lean_M B g (by positivity))
    let D:=G.curvature (faceValue U b); have hg:‖D‖^2 ≤ d^2:= pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) _
    unfold Δ₁; have hm:=sq_nonneg (C*(4*(2*v)*trail η m)); unfold D d at hg; linarith only [mul_le_mul_of_nonneg_left hF hL.le,mul_le_mul_of_nonneg_left hg hL.le,hw,hm]
 next hx =>
    rw [add_assoc, add_comm, research]; obtain ⟨u,e⟩:= lost_M B f w hx (by positivity)
    apply add_le_add (baseReserve T₀ ht)
    rw [u,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,zero_add,Δ₁]; apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) e (2:ℕ)) (by norm_num)) (le_add_of_nonneg_left ?_)
    positivity

abbrev billA (R:Rules G)(q:Clip)(n:Side)(p:BudgetPoint)(β v η C S:ℝ)(m:ℕ)(L L':Flaws n)(f g:ℝ):= taxΔ R q n p β v η C S m - f*(L.card:ℝ) - g*(L'.card:ℝ)
def richBoth (Z:PathData G)(q:Clip)(p:BudgetPoint)(β κ k T:ℝ)(U:Config G n):= richG Z q p β κ U * Real.exp (k*(misdemean T U).card)
lemma collection_R (T:ℝ)(ht:p.threshold ≤ T)(s:0 ≤ v)(t:v≤ R.c)(l:EnoughMark q p m)(d':0≤β)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(u:abandons_A X r A (misdemean p.threshold U) m)(p':0 ≤ C)(b' k f' g':ℝ) -- b' actually κ
  (o1:b'+f' ≤ β*(q.linear*p.threshold^2/2)) (o2:k+g' ≤ β*(q.linear*p.threshold*T/2)) :
  richBoth Z q p β b' k T U ≤ Real.exp ((-β*∑ b:Cell n,recruit Z q r A (misdemean p.threshold U) m b X Y) + billA R q n p β v η C S m (misdemean p.threshold U) (misdemean T U) f' g'):=by
 let V:= CF.Graph.taxY n β p.threshold C S; let F(b:Cell n):=recruit Z q r A (misdemean p.threshold U) m b X Y; let Y'(b:Cell n):= Z.baseTerm q p U b; let t':=q.linear*p.threshold^2/2; let q':=q.linear*p.threshold*T/2; let n₁:ℝ:=(misdemean p.threshold U).card; let n₂:ℝ:=(misdemean T U).card
 unfold richBoth richG; rw [← Real.exp_add]; apply Real.exp_monotone
 have hr : (∑ b:Cell n,F b)+t'*n₁+q'*n₂ ≤ (∑ b:Cell n,Y' b)+(Fintype.card (Cell n):ℝ)*Δ₁ R q v m η C:=by
    have he:= sum_le_sum (s:=univ) fun i _=> tax_A (b:=i) B T ht f g h u l s t p'
    rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,counts_tax,counts_tax] at he; exact he
 obtain ⟨a,b⟩:=CF.Graph.oath B p U
 have hΔ: V ≥ β*(∑ x:Site n, -(PathData.atomSeries Z.cubic p U x + PathData.atomSeries Z.quartic p U x)) + ∑ x:Site n,-PathData.atomSeries Z.loop p U x:=by
    rw [sum_neg_distrib,sum_neg_distrib]; exact add_le_add (mul_le_mul_of_nonneg_left ((neg_le_neg (neg_le_of_abs_le a)).trans_eq (neg_neg _)) d') ((neg_le_neg (neg_le_of_abs_le b)).trans_eq (neg_neg _))
 unfold PathData.principal billA taxΔ; change -(β*((∑ b:Cell n,Y' b)+_)+_)+ b'*n₁ + k*n₂ ≤ (-β * ∑ b:Cell n,F b) + (V+_ -f'*n₁-g'*n₂)
 rw [sum_neg_distrib,sum_neg_distrib] at hΔ; unfold t' q' at hr
 linarith only [mul_le_mul_of_nonneg_left hr d', mul_le_mul_of_nonneg_right o1 (show 0≤n₁ from Nat.cast_nonneg _), mul_le_mul_of_nonneg_right o2 (show 0≤n₂ from Nat.cast_nonneg _),hΔ]
end YM.Gleam
end
