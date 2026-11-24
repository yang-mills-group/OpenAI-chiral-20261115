import YM.SU5.Gleam.Lacuna

/-! # Modified budget in competing precision frames. Need mark omission not to depend on geometry reaching WHOLE-block in penalty of authentic scale.
From Lacuna, warp threshold unchanged even while running two shelves. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius ENNReal
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}
variable (B:Z.Bounds q η C S)
-- operating metric in gauge site-units throughout the pricing (`Ratio` doesn't change heights).
def untouched (S:Support n)(k:ℕ)(x:Site n) := x ∉ halo k S
instance {S:Support n} {k:ℕ}{x:Site n} : Decidable (untouched S k x):=by unfold untouched; infer_instance -- tune
lemma untouched.recede (s:Support n) {k l:ℕ}(h:untouched s k x)(t:separation x z + l ≤ k): untouched s l z:=by
 intro g; obtain ⟨y,f,g⟩:= halo_spec.mp g; refine h (halo_spec.mpr ⟨y,f,?_⟩);
 exact (separation_triangle y z x).trans (by rw [add_comm, separation_comm z x]; omega)

def withinCore (r:Ratio c n)(A:Support c)(S:Support n)(m:ℕ)(x:Site n):= Safe r A m x∧ untouched S m x
instance {k:ℕ}(S:Support n) : Decidable (withinCore r A S k x):=by unfold withinCore; infer_instance
lemma withinCore.shift {S:Support n}{k l:ℕ}(p:withinCore r A S k x)(d:separation x z + l ≤ k): withinCore r A S l z:=⟨p.1.shift d,p.2.recede S d⟩
def withinMark (r:Ratio c n)(A:Support c)(s:Support n)(k:ℕ)(b:Cell n):= withinCore r A s (Sequest k) b.1
instance {k:ℕ}(S:Support n) : Decidable (withinMark r A S k b):=by unfold withinMark; infer_instance
variable {L:Support n} {Λ':Finset (Cell n)}
abbrev face_anchors (B:Finset (Cell n)):= B.image Prod.fst
def blank (v:fieldDir G n 1)(r:Ratio c n)(X:Support c)(L:Support n)(k:ℕ): Prop:=∀ b: Edge (Site n), collect G v b ≠ 0 → withinCore r X L (Sequest k+Sequest k) b.1
private lemma hush_c (h:blank X r A L m)(p:¬ withinMark r A L m b)(f:Cell n)(t:separation b.1 f.1 ≤ m) : faceCurl f X=0:=by
 have he:= grantFace (X:=X) (k:=f) (m:=4) (o:=f.1) (v:=0) (fun u v=> ?_) (by simp); · exact norm_le_zero_iff.mp (he.trans_eq (mul_zero _))
 rw [show collect G X u=0 from ?_, norm_zero]; by_contra he; apply p; apply (h u he).shift; unfold Sequest; rw [separation_comm]; apply Nat.add_le_add_right (k:=m+4) ?_; exact (separation_triangle ..).trans ((Nat.add_le_add t v))
include B
private lemma priceBase (D:ℕ→G.Color)(h:∀ i:ℕ, let k:= (Z.row b.2 i).2.length; ‖D i‖≤ v * Real.exp (η*k))(p:0 ≤ v) : let F:ℕ→G.Color:= fun i=> (Z.row b.2 i).1 • D i; Summable F ∧ ‖∑' i,F i‖ ≤ C*v:=by
 intro F; let Ψ:= (fun i=> |(Z.row b.2 i).1| *Real.exp (η*(Z.row b.2 i).2.length)); have ht:= B.rows b.2
 have he (i:ℕ): ‖F i‖ ≤ Ψ i*v:=by unfold F Ψ; rw [norm_smul,Real.norm_eq_abs,mul_right_comm]; exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))|>.trans_eq (by ring)
 have hf : Summable fun i=> Ψ i * v:= ht.2.1.mul_right _; have hx:Summable (fun i=> ‖F i‖):=hf.of_nonneg_of_le (fun _=>norm_nonneg _) he; exact ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he hf).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 p))⟩
private lemma loose_bound (h:ProbeBox X v)(w:0≤v) : ‖ellLine Z b X‖ ≤ C*(4*v):=by
 apply (priceBase B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) _ (by positivity:0 ≤ 4*v)).2; intro i k; have hr:=B.width; exact (all_probe h _).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
omit B in
private lemma tail {q:ℕ}(hm:m<q)(he:0 ≤ η): 1 ≤ trail η m * Real.exp (η*(q:ℝ)):=by unfold trail; rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hm.le) he]
lemma fallout (g:ProbeBox X v)(h:blank X r A L m)(t:¬ withinMark r A L m b)(w:0 ≤ v): faceCurl b X=0 ∧ ‖ellLine Z b X‖ ≤ C*(4*v*trail η m):=by
 refine ⟨hush_c h t _ (by simp),?_⟩; have hp:0 ≤ 4*v*trail η m:=by unfold trail; positivity
 refine (priceBase B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) (fun i=>?_) hp).2
 intro k; let F:=(Z.row b.2 i).2; by_cases l:k≤m
 · have he:separation b.1 (slotFace F b.1).1 ≤ m:= (Work.E04.slot_separation F b.1).trans l; change ‖faceCurl (slotFace F b.1) X‖≤ _; rw [hush_c h t _ he,norm_zero]; exact mul_nonneg hp (Real.exp_pos _).le
 refine (all_probe g _).trans (le_trans (le_mul_of_one_le_right (by positivity:0 ≤4*v) (tail (lt_of_not_ge l) B.width.le)) (le_of_eq ?_)); ring

def arrear (Z:PathData G) (q:Clip) (r:Ratio c n)(A:Support c)(L: Support n)(m:ℕ)(b:Cell n)(X Y:fieldDir G n 1): ℝ:= if withinMark r A L m b then research Z q b (X+Y) else research Z q b X
abbrev unitDueS(q:Clip)(p:BudgetPoint):= q.linear*p.threshold^2/2
abbrev unitDueL(q:Clip)(p:BudgetPoint)(v:ℝ):= q.linear*p.threshold*v/2
omit B in
lemma mane {ε:ℝ}(t:p.threshold≤ε): let D:= misdemean p.threshold U; let E:= misdemean ε U; (if b∈ D then unitDueS q p else 0) + (if b∈ E then unitDueL q p ε else 0) ≤ Z.baseTerm q p U b:=by
 intro D E; have hp:= p.threshold_pos; have hq:= q.tail_pos
 by_cases H:b∈ E; swap
 · rw [if_neg H, add_zero]; apply le_trans _ (base_malaise (p:=p) (q:=q)); change (if b∈ D then _ else 0)≤ if b∈ D then _ else 0; split_ifs; · unfold unitDueS; nlinarith only [mul_nonneg hq.le (sq_nonneg p.threshold)]
   exact le_rfl
 let d:= G.chord (faceValue U b); have hl:ε< d:=(mem_filter.mp H).2
 have hv:p.threshold< d:= t.trans_lt hl
 unfold PathData.baseTerm; refine (le_add_of_nonneg_right ?_).trans' ?_
 · split; positivity; exact le_rfl
 rw [PathData.clipped,if_neg hv.not_ge, if_pos H, if_pos (show b∈ D from mem_filter.mpr ⟨mem_univ _,hv⟩)]; unfold unitDueS unitDueL; change _ ≤ q.linear* p.threshold * d
 nlinarith only [mul_le_mul_of_nonneg_left hv.le (mul_nonneg hq.le hp.le),mul_le_mul_of_nonneg_left hl.le (mul_nonneg hq.le hp.le)]
omit B in
private lemma d_fines {x y : G.Color}{D d:ℝ}(p:‖x-y‖≤D)(h:‖y‖≤d) : ‖y‖^2 ≤ ‖x‖^2 + (2*D*d):=by
 rcases le_total ‖y‖ ‖x‖ with h1|h1
 · refine le_trans (pow_le_pow_left₀ (norm_nonneg y) h1 _) (le_add_of_nonneg_right ?_); have he:0 ≤ D:= le_trans (norm_nonneg _) p; have hp :0≤d:= (norm_nonneg _).trans h; positivity
 have he: 0≤D:=(norm_nonneg _).trans p; have hw: ‖y‖-‖x‖ ≤ D:= (norm_sub_norm_le y x).trans ((norm_sub_rev ..).trans_le p)
 have hz:=mul_le_mul_of_nonneg_left hw (show 0 ≤ ‖y‖+‖x‖ from by positivity)
 nlinarith only [hz,mul_le_mul_of_nonneg_right h1 he,mul_le_mul_of_nonneg_right h he]
lemma scar_line {ε:ℝ}(hε:p.threshold≤ε)(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r (broken r ε U) v) (w:blank X r (broken r ε U) (face_anchors (misdemean p.threshold U)) m) (l:EnoughMark q p m)(p':0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C) : arrear Z q r (broken r ε U) (face_anchors (misdemean p.threshold U)) m b X Y + ((if b∈misdemean p.threshold U then unitDueS q p else 0)+(if b∈misdemean ε U then unitDueL q p ε else 0)) ≤ Z.baseTerm q p U b + Δ₁ R q v m η C:=by
 let t:=p.threshold; let k:=Safe r (broken r t U) (Sequest m) b.1; let d:= G.chord (faceValue U b); have d0:0 ≤ d:= G.chord_nonneg _; have h0:=p.threshold_pos; have hL:=q.quadratic_pos
 have hδ : 0 ≤ faceCutError R v:=by unfold faceCutError; have h:=G.colorScale_pos; have xv:=R.positive; positivity
 let F:= acry R v m η C; have he:0 ≤ acry R v m η C:= acry_zero hv p'
 have v0:0≤ C*(4*(2*v)):=by positivity
 unfold arrear; split
 next g0 =>
    have hl (b':Cell n)(z:separation b.1 b'.1 ≤ Sequest m) : G.chord (faceValue U b') ≤ t:=by
       by_contra! ht; exact g0.2 (halo_spec.mpr ⟨b'.1,mem_image.mpr ⟨b',mem_filter.mpr ⟨mem_univ _,ht⟩,rfl⟩, (separation_comm ..).trans_le z⟩)
    have hd:d ≤ p.threshold:= hl b (by simp)
    have ht:PathData.kept q t b.1 U:= by
       intro f; by_cases h:separation b.1 f.1 ≤ Sequest m; · exact (hl f h).trans (le_mul_of_one_le_right h0.le (Real.one_le_exp (div_nonneg (by positivity) q.radius_pos.le)))
       exact (G.chord_le_two _).trans ((show 2≤ p.threshold * Real.exp ((Sequest m:ℕ)/ (q.relaxation:ℝ)) from l).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr ((le_of_not_ge h))) q.radius_pos.le)) h0.le))
    rw [if_neg (show b∉ misdemean p.threshold U from fun h=> hd.not_gt (mem_filter.mp h).2),if_neg (show b∉ misdemean ε U from fun h=> (hd.trans hε).not_gt ((mem_filter.mp h).2)), zero_add,add_zero,PathData.baseTerm,PathData.clipped,if_pos hd,if_pos (show PathData.kept q p.threshold b.1 U from ht),research]
    have hF:= d_fines (angleFaceSmall h p' t' b (g0.1.shift (y:=b.1) (by simp [Sequest]))).2 (all_probe g b)
    have hw:= d_fines (payLine B g h p' t' g0.1) (loose_bound B g (by positivity))
    let D:=G.curvature (faceValue U b); have hg:‖D‖^2 ≤ d^2:= pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) _
    unfold Δ₁; have hm:=sq_nonneg (C*(4*(2*v)*trail η m)); unfold D d at hg; linarith only [mul_le_mul_of_nonneg_left hF hL.le,mul_le_mul_of_nonneg_left hg hL.le,hw,hm]
 next hx =>
    rw [add_comm, research]; obtain ⟨u,e⟩:= fallout B f w hx (by positivity)
    apply add_le_add (mane hε)
    rw [u,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,zero_add,Δ₁]; apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) e (2:ℕ)) (by norm_num)) (le_add_of_nonneg_left ?_)
    positivity
end YM.Gleam
#print axioms YM.Gleam.scar_line
