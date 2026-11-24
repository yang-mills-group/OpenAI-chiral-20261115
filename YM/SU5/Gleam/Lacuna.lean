/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Gleam.Afeu
import YM.Work.F03.Metric
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Multiplier
/-! #Full row including long-range variables from DEEP interior, exact gaussian. Filling ALL rows
-- then boundary leakage via an absolute log-box bound. Does NOT have to compare smallest
eigenvalues under truncation on these volumes. -/
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
def ProbeBox (X:fieldDir G n 1) (v:ℝ):=∀ j:Bond n, ‖collect G X j‖ ≤ v
variable (B:Z.Bounds q η C S)
def Sequest (m:ℕ):ℕ:= m+4
abbrev insideB (r:Ratio c n)(A:Support c)(k:ℕ)(b:Cell n):= Safe r A (Sequest k) b.1
def abandon (v:fieldDir G n 1)(r:Ratio c n)(X:Support c)(k:ℕ): Prop:=∀ b: Edge (Site n), collect G v b ≠ 0 → Safe r X (Sequest k+Sequest k) b.1
-- not keep base iff NEGLIGIBLE deep
private lemma hush (h:abandon X r A m)(p:¬ insideB r A m b)(f:Cell n)(t:separation b.1 f.1 ≤ m) : faceCurl f X=0:=by
 have he:= grantFace (X:=X) (k:=f) (m:=4) (o:=f.1) (v:=0) (fun u v=> ?_) (by simp); · exact norm_le_zero_iff.mp (he.trans_eq (mul_zero _))
 rw [show collect G X u=0 from ?_, norm_zero]; by_contra he; apply p; apply (h u he).shift; unfold Sequest; rw [separation_comm]; apply Nat.add_le_add_right (k:=m+4) ?_; exact (separation_triangle ..).trans ((Nat.add_le_add t v))
lemma all_probe (g:ProbeBox X v)(b:Cell n): ‖faceCurl b X‖ ≤ 4*v := grantFace (o:=b.1) (m:=4) (fun i _=>g i) (by simp)
include B
private lemma priceBase (D:ℕ→G.Color)(h:∀ i:ℕ, let k:= (Z.row b.2 i).2.length; ‖D i‖≤ v * Real.exp (η*k))(p:0 ≤ v) : let F:ℕ→G.Color:= fun i=> (Z.row b.2 i).1 • D i; Summable F ∧ ‖∑' i,F i‖ ≤ C*v:=by
 intro F; let Ψ:= (fun i=> |(Z.row b.2 i).1| *Real.exp (η*(Z.row b.2 i).2.length)); have ht:= B.rows b.2
 have he (i:ℕ): ‖F i‖ ≤ Ψ i*v:=by unfold F Ψ; rw [norm_smul,Real.norm_eq_abs,mul_right_comm]; exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))|>.trans_eq (by ring)
 have hf : Summable fun i=> Ψ i * v:= ht.2.1.mul_right _; have hx:Summable (fun i=> ‖F i‖):=hf.of_nonneg_of_le (fun _=>norm_nonneg _) he; exact ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he hf).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 p))⟩
private lemma loose_bound (h:ProbeBox X v)(w:0≤v) : ‖ellLine Z b X‖ ≤ C*(4*v):=by
 apply (priceBase B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) _ (by positivity:0 ≤ 4*v)).2; intro i k; have hr:=B.width; exact (all_probe h _).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
def trail (s:ℝ)(v:ℕ):= Real.exp (-s*v)
omit B in
private lemma tail {q:ℕ}(hm:m<q)(he:0 ≤ η): 1 ≤ trail η m * Real.exp (η*(q:ℝ)):=by unfold trail; rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hm.le) he]
lemma lost (g:ProbeBox X v)(h:abandon X r A m)(t:¬ insideB r A m b)(w:0 ≤ v): faceCurl b X=0 ∧ ‖ellLine Z b X‖ ≤ C*(4*v*trail η m):=by
 refine ⟨hush h t _ (by simp),?_⟩; have hp:0 ≤ 4*v*trail η m:=by unfold trail; positivity
 refine (priceBase B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) (fun i=>?_) hp).2
 intro k; let F:=(Z.row b.2 i).2; by_cases l:k≤m
 · have he:separation b.1 (slotFace F b.1).1 ≤ m:= (Work.E04.slot_separation F b.1).trans l; change ‖faceCurl (slotFace F b.1) X‖≤ _; rw [hush h t _ he,norm_zero]; exact mul_nonneg hp (Real.exp_pos _).le
 refine (all_probe g _).trans (le_trans (le_mul_of_one_le_right (by positivity:0 ≤4*v) (tail (lt_of_not_ge l) B.width.le)) (le_of_eq ?_)); ring
abbrev acry (R:Rules G) (v:ℝ) (k:ℕ) (η C:ℝ):= C*(slotError R k v +(2+4*(2*v))*trail η k)
omit B in
lemma acry_zero (p:0 ≤ C)(v':0≤v): 0 ≤ acry R v m η C:= by unfold acry slotError trail faceCutError; have h:=R.positive; have hx:= G.colorScale_pos; positivity
lemma payLine (g:ProbeBox X (2*v))(h:TrustLogs X U r A v) (p:0≤v)(t':v≤R.c)(f:insideB r A m b) : ‖Z.ell U b-ellLine Z b X‖≤ acry R v m η C:=by
 let X':=2+4*(2*v); let V:=slotError R m v+X'* trail η m
 have hp:0≤slotError R m v:=by unfold slotError faceCutError; have h:= G.colorScale_pos; have he:=R.positive; positivity
 have hv:0≤V:=by unfold V X' trail; positivity
 let a(i:ℕ):=(Z.row b.2 i).2
 let D(i:ℕ):G.Color:= (a i).atSite U b.1-faceCurl (slotFace (a i) b.1) X
 have hx:= (priceBase B (b:=b) D (fun i => ?_) hv).2
 · unfold PathData.ell ellLine; let F(i:ℕ):=(Z.row b.2 i).1; rw [← Summable.tsum_sub (show Summable (fun i=> Z.ellTerms b i U) from ?_) (ellLine_summable Z B b X)]
   · exact le_trans (le_of_eq (congrArg norm (tsum_congr (fun z=>Eq.symm (smul_sub (F z) ((a z).atSite U b.1) (faceCurl (slotFace (a z) b.1) X)))))) hx
   apply (priceBase B (b:=b) (fun i=> (a i).atSite U b.1) _ (zero_le_two : (0:ℝ) ≤ 2)).1; intro i k; exact ((a i).eval_norm _).trans (le_mul_of_one_le_right zero_le_two (Real.one_le_exp (by have ht:=B.width; positivity)))
 intro k; let j:=a i; by_cases l:k≤m
 · exact ((grantSlot h p t' j f l).trans (show slotError R m v ≤ V from (by apply le_add_of_nonneg_right; unfold X' trail; positivity))).trans (le_mul_of_one_le_right hv (Real.one_le_exp (by have ht:=B.width; positivity)))
 have hz : ‖D i‖≤ X':=(norm_sub_le ..).trans (add_le_add (Slot.eval_norm ..) (all_probe g _)); let x:=Real.exp (η*k)
 exact hz.trans ((le_mul_of_one_le_right (by unfold X'; positivity : 0 ≤ X') (tail (lt_of_not_ge l) B.width.le)).trans (by rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hp) (Real.exp_pos _).le))

-- masked energy but use linear reference in ALL colors; prevent row cutoff on deep coordinates
def research (Z:PathData G)(q:Clip)(b:Cell n)(X:fieldDir G n 1) := q.direct * ‖faceCurl b X‖^2/2 + ‖ellLine Z b X‖^2/2
def rent (Z:PathData G) (q:Clip) (r:Ratio c n)(A:Support c)(m:ℕ)(b:Cell n)(X Y:fieldDir G n 1): ℝ:= if insideB r A m b then research Z q b (X+Y) else research Z q b X
omit B in
private lemma d_fines {x y : G.Color}{D d:ℝ}(p:‖x-y‖≤D)(h:‖y‖≤d) : ‖y‖^2 ≤ ‖x‖^2 + (2*D*d):=by
 rcases le_total ‖y‖ ‖x‖ with h1|h1
 · refine le_trans (pow_le_pow_left₀ (norm_nonneg y) h1 _) (le_add_of_nonneg_right ?_); have he:0 ≤ D:= le_trans (norm_nonneg _) p; have hp :0≤d:= (norm_nonneg _).trans h; positivity
 have he: 0≤D:=(norm_nonneg _).trans p; have hw: ‖y‖-‖x‖ ≤ D:= (norm_sub_norm_le y x).trans ((norm_sub_rev ..).trans_le p)
 have hz:=mul_le_mul_of_nonneg_left hw (show 0 ≤ ‖y‖+‖x‖ from by positivity)
 nlinarith only [hz,mul_le_mul_of_nonneg_right h1 he,mul_le_mul_of_nonneg_right h he]
-- error does NOT include curvature cost when target lost (direct row exactly 0)
abbrev Δ₁ (R:Rules G)(p:Clip)(v:ℝ)(m:ℕ)(η C:ℝ):= p.direct*(faceCutError R v * (4*(2*v))) + acry R v m η C*(C*(4*(2*v))) + (C*(4*(2*v)*trail η m))^2 /2
-- t arbitrary. V fee of entire working area. true clipped. ℎ masks not lost.
def EnoughMark (q:Clip)(p:BudgetPoint) (m:ℕ):= 2≤ p.threshold * Real.exp ((Sequest m:ℕ)/ (q.relaxation:ℝ))
omit B in
lemma base_malaise : let θ:=p.threshold; let E:=if b∈misdemean θ U then q.linear*θ^2 else 0; E ≤ Z.baseTerm q p U b:=by
 intro θ D; let d:=G.chord (faceValue U b); have hp:= p.threshold_pos; have he:= q.tail_pos; have ht:= q.quadratic_pos; have hd:=G.chord_nonneg (faceValue U b); let t:=q.linear; unfold D PathData.baseTerm
 refine le_trans (b:=PathData.clipped q p.threshold d) ?_ (le_add_of_nonneg_right ?_); swap; · split; positivity; exact le_rfl
 by_cases h:b∈ misdemean θ U; · have h':θ < d:= (mem_filter.mp h).2; rw [if_pos h,PathData.clipped,if_neg h'.not_ge,sq,←mul_assoc]; exact mul_le_mul_of_nonneg_left h'.le (mul_nonneg he.le hp.le)
 rw [if_neg h,PathData.clipped]; split; positivity; exact mul_nonneg (mul_nonneg he.le hp.le) hd
lemma Δ_line (f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r (broken r p.threshold U) v) (w:abandon X r (broken r p.threshold U) m) (l:EnoughMark q p m)(p':0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C) : rent Z q r (broken r p.threshold U) m b X Y + (if b∈misdemean p.threshold U then q.linear*p.threshold^2 else 0) ≤ Z.baseTerm q p U b + Δ₁ R q v m η C:=by
 let t:=p.threshold; let k:=insideB r (broken r t U) m b; let d:= G.chord (faceValue U b); have d0:0 ≤ d:= G.chord_nonneg _; have h0:=p.threshold_pos; have hL:=q.quadratic_pos
 have hδ : 0 ≤ faceCutError R v:=by unfold faceCutError; have h:=G.colorScale_pos; have xv:=R.positive; positivity
 let F:= acry R v m η C; have he:0 ≤ acry R v m η C:= acry_zero hv p'
 have v0:0≤ C*(4*(2*v)):=by positivity
 unfold rent; split
 next g0 =>
    have hf:b ∉ misdemean p.threshold U:= face_pure g0.1
    have hl (b':Cell n)(z:separation b.1 b'.1 ≤ Sequest m) : G.chord (faceValue U b') ≤ t:=by
       by_contra! ht; have s:r.parent b'.1∉ broken r t U:= g0.2 b'.1 z ▸ g0.1; exact face_pure s (mem_filter.mpr ⟨mem_univ _,ht⟩)
    have hd:d ≤ p.threshold:= hl b (by simp)
    have ht:PathData.kept q t b.1 U:= by
       intro f; by_cases h:separation b.1 f.1 ≤ Sequest m; · exact (hl f h).trans (le_mul_of_one_le_right h0.le (Real.one_le_exp (div_nonneg (by positivity) q.radius_pos.le)))
       exact (G.chord_le_two _).trans ((show 2≤ p.threshold * Real.exp ((Sequest m:ℕ)/ (q.relaxation:ℝ)) from l).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr ((le_of_not_ge h))) q.radius_pos.le)) h0.le))
    rw [if_neg hf,add_zero,PathData.baseTerm,PathData.clipped,if_pos hd,if_pos (show PathData.kept q p.threshold b.1 U from ht),research]
    have hF:= d_fines (angleFaceSmall h p' t' b (g0.shift (y:=b.1) (by simp [Sequest]))).2 (all_probe g b)
    have hw:= d_fines (payLine B g h p' t' g0) (loose_bound B g (by positivity))
    let D:=G.curvature (faceValue U b); have hg:‖D‖^2 ≤ d^2:= pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) _
    unfold Δ₁; have hm:=sq_nonneg (C*(4*(2*v)*trail η m)); unfold D d at hg; linarith only [mul_le_mul_of_nonneg_left hF hL.le,mul_le_mul_of_nonneg_left hg hL.le,hw,hm]
 next hx =>
    rw [add_comm, research]; obtain ⟨u,e⟩:= lost B f w hx (by positivity)
    apply add_le_add (base_malaise)
    rw [u,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,zero_add,Δ₁]; apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) e (2:ℕ)) (by norm_num)) (le_add_of_nonneg_left ?_)
    positivity
end YM.Gleam
#print axioms YM.Gleam.Δ_line
