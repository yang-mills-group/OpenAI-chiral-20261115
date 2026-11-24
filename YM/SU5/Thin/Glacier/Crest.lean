import YM.SU5.Gleam.Lacuna
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius ENNReal
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}
variable {W:Finset (Cell n)} (B:Z.Bounds q η C S) {e:ℕ}
-- Deep relative to coarse cells, lower defects, trims independently
abbrev afar (W:Finset (Cell n))(k:ℕ)(x:Site n):Prop:= ∀ b∈W,k<separation x b.1
def Deep (r:Ratio c n) (A:Support c)(W:Finset (Cell n))(k:ℕ)(x:Site n):Prop:= Safe r A k x ∧ afar W k x
lemma Deep.turn(h:Deep r A W m o)(p:separation o x+e≤m): Deep r A W e x:=by refine ⟨h.1.shift p,fun i t=> ?_⟩; have ht:= h.2 i t; have hp:=separation_triangle o x i.1; omega
def rimB (r:Ratio c n) (A:Support c) (m:ℕ)(W:Finset (Cell n))(b: Cell n): Prop:= Deep r A W (Sequest m) b.1
def noiseless (v:fieldDir G n 1)(r:Ratio c n)(X:Support c)(W:Finset (Cell n))(k:ℕ): Prop:=∀ b: Edge (Site n), collect G v b ≠ 0 → Deep r X W (Sequest k+Sequest k) b.1
private lemma vChill (h:noiseless X r A W m)(p:¬ rimB r A m W b)(f:Cell n)(t:separation b.1 f.1 ≤ m) : faceCurl f X=0:=by
 have he:= grantFace (X:=X) (k:=f) (m:=4) (o:=f.1) (v:=0) (fun u v=> ?_) (by simp); · exact norm_le_zero_iff.mp (he.trans_eq (mul_zero _))
 rw [show collect G X u=0 from ?_, norm_zero]; by_contra he; apply p; apply (h u he).turn; unfold Sequest; rw [separation_comm]; apply Nat.add_le_add_right (k:=m+4) ?_; exact (separation_triangle ..).trans ((Nat.add_le_add t v))
include B
private lemma priceChill (D:ℕ→G.Color)(h:∀ i:ℕ, let k:= (Z.row b.2 i).2.length; ‖D i‖≤ v * Real.exp (η*k))(p:0 ≤ v) : let F:ℕ→G.Color:= fun i=> (Z.row b.2 i).1 • D i; Summable F ∧ ‖∑' i,F i‖ ≤ C*v:=by
 intro F; let Ψ:= (fun i=> |(Z.row b.2 i).1| *Real.exp (η*(Z.row b.2 i).2.length)); have ht:= B.rows b.2
 have he (i:ℕ): ‖F i‖ ≤ Ψ i*v:=by unfold F Ψ; rw [norm_smul,Real.norm_eq_abs,mul_right_comm]; exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))|>.trans_eq (by ring)
 have hf : Summable fun i=> Ψ i * v:= ht.2.1.mul_right _; have hx:Summable (fun i=> ‖F i‖):=hf.of_nonneg_of_le (fun _=>norm_nonneg _) he; exact ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he hf).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 p))⟩
private lemma crisp_loose (h:ProbeBox X v)(w:0≤v) : ‖ellLine Z b X‖ ≤ C*(4*v):=by
 apply (priceChill B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) _ (by positivity:0 ≤ 4*v)).2; intro i k; have hr:=B.width; exact (all_probe h _).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
omit B in
private lemma tailAway {q:ℕ}(hm:m<q)(he:0 ≤ η): 1 ≤ trail η m * Real.exp (η*(q:ℝ)):=by unfold trail; rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hm.le) he]
lemma arctic_lost (g:ProbeBox X v)(h:noiseless X r A W m)(t:¬ rimB r A m W b)(w:0 ≤ v): faceCurl b X=0 ∧ ‖ellLine Z b X‖ ≤ C*(4*v*trail η m):=by
 refine ⟨vChill h t _ (by simp),?_⟩; have hp:0 ≤ 4*v*trail η m:=by unfold trail; positivity
 refine (priceChill B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) (fun i=>?_) hp).2
 intro k; let F:=(Z.row b.2 i).2; by_cases l:k≤m
 · have he:separation b.1 (slotFace F b.1).1 ≤ m:= (Work.E04.slot_separation F b.1).trans l; change ‖faceCurl (slotFace F b.1) X‖≤ _; rw [vChill h t _ he,norm_zero]; exact mul_nonneg hp (Real.exp_pos _).le
 refine (all_probe g _).trans (le_trans (le_mul_of_one_le_right (by positivity:0 ≤4*v) (tailAway (lt_of_not_ge l) B.width.le)) (le_of_eq ?_)); ring
omit B
def calf (Z:PathData G)(q:Clip)(r:Ratio c n)(A:Support c)(m:ℕ)(W:Finset (Cell n))(b:Cell n)(X Y:fieldDir G n 1): ℝ:= if rimB r A m W b then research Z q b (X+Y) else research Z q b X
private lemma tight_ice {x y : G.Color}{D d:ℝ}(p:‖x-y‖≤D)(h:‖y‖≤d) : ‖y‖^2 ≤ ‖x‖^2 + (2*D*d):=by
 rcases le_total ‖y‖ ‖x‖ with h1|h1
 · refine le_trans (pow_le_pow_left₀ (norm_nonneg y) h1 _) (le_add_of_nonneg_right ?_); have he:0 ≤ D:= le_trans (norm_nonneg _) p; have hp :0≤d:= (norm_nonneg _).trans h; positivity
 have he: 0≤D:=(norm_nonneg _).trans p; have hw: ‖y‖-‖x‖ ≤ D:= (norm_sub_norm_le y x).trans ((norm_sub_rev ..).trans_le p)
 have hz:=mul_le_mul_of_nonneg_left hw (show 0 ≤ ‖y‖+‖x‖ from by positivity)
 nlinarith only [hz,mul_le_mul_of_nonneg_right h1 he,mul_le_mul_of_nonneg_right h he]

abbrev meek (p:BudgetPoint)(U:Config G n):= misdemean (p.threshold/2) U
def leaff (q:Clip):= min (q.direct/8) (q.linear/2)
lemma leaf_p (q:Clip):0<leaff q:=lt_min (div_pos q.quadratic_pos (by norm_num)) (half_pos q.tail_pos)
lemma d_tier (z:p.threshold≤t)(x:b∈misdemean t U): b∈meek p U:= mem_filter.mpr ⟨mem_univ _,(half_lt_self p.threshold_pos).trans (lt_of_le_of_lt z (mem_filter.mp x).2)⟩
def hire (q:Clip)(p:BudgetPoint)(t:ℝ)(U:Config G n)(b:Cell n):= (if b∈meek p U then leaff q*p.threshold^2 else 0)+(if b∈misdemean t U then q.linear/2*p.threshold*t else 0)
lemma brusque (u:p.threshold≤t): hire q p t U b ≤ Z.baseTerm q p U b:=by
 let V:= G.chord (faceValue U b); let Y:=p.threshold; have hx:0<Y:=p.threshold_pos; have hv:0 ≤ V:=G.chord_nonneg _; have hq:=q.tail_pos; have hl:=q.quadratic_pos; have ha:leaff q≤q.direct/8:=min_le_left ..; have ht:leaff q≤q.linear/2:=min_le_right ..
 refine le_trans (b:=PathData.clipped q Y V) ?_ (le_add_of_nonneg_right ?_); swap; · split; positivity; exact le_rfl
 unfold hire PathData.clipped
 by_cases z:b∈meek p U
 · rw [if_pos z]; have he:Y/2<V:=(mem_filter.mp z).2
   by_cases g:b∈misdemean t U
   · have ht':t<V:=(mem_filter.mp g).2; rw [if_pos g,if_neg (show ¬ V≤Y from (lt_of_le_of_lt u ht').not_ge)]
     change _*Y^2 + _/2*Y*t ≤ _*Y*V; have hm:Y≤V:= u.trans ht'.le
     nlinarith only [mul_le_mul_of_nonneg_left hm (mul_nonneg hq.le hx.le),mul_le_mul_of_nonneg_left ht'.le (mul_nonneg hq.le hx.le),mul_le_mul_of_nonneg_right ht (sq_nonneg Y)]
   rw [if_neg g,add_zero]; by_cases s:V≤Y
   · rw [if_pos s]; change _*Y^2 ≤ _; nlinarith only [mul_le_mul_of_nonneg_right ha (sq_nonneg Y),mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (half_pos hx).le he.le 2) hl.le]
   rw [if_neg s]; change leaff q*Y^2 ≤ _; nlinarith only [mul_le_mul_of_nonneg_right ht (sq_nonneg Y),mul_le_mul_of_nonneg_left (le_of_not_ge s) (mul_nonneg hq.le hx.le),mul_nonneg hq.le (sq_nonneg Y)]
 rw [if_neg z,if_neg (fun i=>z (d_tier u i)),zero_add]; split <;> positivity
include B
lemma Δ_lane (f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(eP:ℝ)(ht:p.threshold≤eP)(h:TrustLogs (X+Y) U r A v)(w:noiseless X r A (meek p U) m) (l:EnoughMark q p m)(p':0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C) : calf Z q r A m (meek p U) b X Y + hire q p eP U b ≤ Z.baseTerm q p U b + Δ₁ R q v m η C:=by
 let t:=p.threshold; let k:=insideB r A m b; let d:= G.chord (faceValue U b); have d0:0 ≤ d:= G.chord_nonneg _; have h0:=p.threshold_pos; have hL:=q.quadratic_pos
 have hδ : 0 ≤ faceCutError R v:=by unfold faceCutError; have h:=G.colorScale_pos; have xv:=R.positive; positivity
 let F:= acry R v m η C; have he:0 ≤ acry R v m η C:= acry_zero hv p'
 have v0:0≤ C*(4*(2*v)):=by positivity
 unfold calf; split
 next g0 =>
    have hf:b ∉ meek p U:= fun i=> by have he:= g0.2 b i; simp at he
    have hl (b':Cell n)(z:separation b.1 b'.1 ≤ Sequest m) : G.chord (faceValue U b') ≤ t:=by
       by_contra! ht; have hs:b'∈meek p U:=mem_filter.mpr ⟨mem_univ _,(half_lt_self h0).trans ht⟩; exact Nat.not_lt.mpr z (g0.2 _ hs)
    have hd:d ≤ p.threshold:= hl b (by simp)
    have ht2:PathData.kept q t b.1 U:= by
       intro f; by_cases h:separation b.1 f.1 ≤ Sequest m; · exact (hl f h).trans (le_mul_of_one_le_right h0.le (Real.one_le_exp (div_nonneg (by positivity) q.radius_pos.le)))
       exact (G.chord_le_two _).trans ((show 2≤ p.threshold * Real.exp ((Sequest m:ℕ)/ (q.relaxation:ℝ)) from l).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr ((le_of_not_ge h))) q.radius_pos.le)) h0.le))
    rw [hire,if_neg hf,if_neg (fun i=> hf (d_tier ht i)),add_zero,add_zero,PathData.baseTerm,PathData.clipped,if_pos hd,if_pos (show PathData.kept q p.threshold b.1 U from ht2),research]
    have hF:= tight_ice (angleFaceSmall h p' t' b (g0.1.shift (y:=b.1) (by simp [Sequest]))).2 (all_probe g b)
    have hw:= tight_ice (payLine B g h p' t' g0.1) (crisp_loose B g (by positivity))
    let D:=G.curvature (faceValue U b); have hg:‖D‖^2 ≤ d^2:= pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) _
    unfold Δ₁; have hm:=sq_nonneg (C*(4*(2*v)*trail η m)); unfold D d at hg; linarith only [mul_le_mul_of_nonneg_left hF hL.le,mul_le_mul_of_nonneg_left hg hL.le,hw,hm]
 next hx =>
    rw [add_comm, research]; obtain ⟨u,e⟩:= arctic_lost B f w hx (by positivity)
    apply add_le_add (brusque ht)
    rw [u,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,zero_add,Δ₁]; apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) e (2:ℕ)) (by norm_num)) (le_add_of_nonneg_left ?_)
    positivity

end YM.Gleam