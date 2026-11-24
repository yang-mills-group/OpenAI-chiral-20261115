import YM.SU5.Selected.Hill.Via
import YM.SU5.Selected.Chene.Row
/-! Cut-tail & quadratic cost. Taylor lower row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Box
open Function Finset Lattice Tree Wilson RG Exterior Pressure Work.F03 Work.E01 Precision MeasureTheory Next.Rank.Spindle Push Work.F02
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{r:Side}{B R:ℕ}{e t:ℝ}{U:Config G n}{s:Signed}
variable (V:(columbia r n).Slice G)(w:U=(columbia r n).drape V)(L:Rules G)
lemma allo_nn (k:ℕ)(e:ℝ): 0≤allowance L e k:=by have h:=L.positive; have u:=G.colorScale_pos; unfold allowance; positivity
lemma allo_mono(e:ℝ) : Monotone (allowance L e):= by intro i j p; unfold allowance; have h:=L.positive; have u:=G.colorScale_pos; gcongr
include V w
lemma crop (b: Plane n) (p:Light r (menu U t) B (affine s 0 b.1))(ht:0≤t)(z:4*r.val*t≤e)(he:e ≤ L.c)(h₀:7≤B):
 ‖G.curvature (faceValue (pull s 0 U) b)-faceCurl b (Bid.pulled (scrim U) s)‖ ≤ allowance L e 4:=by
 rw [faceCurl,←fundamental]; exact (rocaille V w L (square b.2.val.1 b.2.val.2) _ (p.small h₀) ht z he).2 -- unlike abbrev?
lemma cruise (a: Slot)(x:Site n) (p:Light r (menu U t) B (affine s 0 x))(ht:0≤t)(z:4*r.val*t≤e)(he:e ≤ L.c)(hv:a.length ≤ R)(h₀:2*R+3≤B):
 ‖a.atSite (pull s 0 U) x - faceCurl (slotFace a x) (Bid.pulled (scrim U) s)‖ ≤ allowance L e (2*R):=by
 have hp:(slotWalk a).length ≤ 2*R:=(slot_t a).trans (Nat.mul_le_mul_left 2 hv); rw [←slot_v,atSite_curvature]; exact ((rocaille V w L _ x (p.small ((Nat.add_le_add_right hp _).trans h₀)) ht z he).2).trans (allo_mono L e hp)
omit V w
open Chene.Tail
variable {W:PathData G}{C:Clip}{σ X D θ:ℝ}
def trimmed (W:PathData G)(R:ℕ)(b:Plane n)(v: fieldDir G n 1)(j:ℕ):= if R < (W.row b.2 j).2.length then 0 else (W.row b.2 j).1 • faceCurl (slotFace (W.row b.2 j).2 b.1) v
def curtailed (W:PathData G)(R:ℕ)(b:Plane n)(v: fieldDir G n 1):=∑' j, trimmed W R b v j
variable (h: W.Bounds C σ X D)
include h
lemma trim_sum (b:Plane n)(v:fieldDir G n 1)(R:ℕ) : Summable (trimmed W R b v):=by
 apply Summable.of_norm_bounded (ellLine_summable W h b v).norm; intro i; unfold trimmed; split; simp; rfl
lemma curtailed_bill (b:Plane n)(v:fieldDir G n 1)(R:ℕ) : ellLine W b v= curtailed W R b v + tail_r W R (faceCurl · v) b:=by
 let T:=trimmed W R b v; have he (j:ℕ): visit W j R b (faceCurl · v)= (W.row b.2 j).1 • faceCurl (slotFace (W.row b.2 j).2 b.1) v- T j:=by unfold visit T trimmed; split <;> simp
 unfold tail_r; simp_rw [he]; unfold T ellLine curtailed; rw [(ellLine_summable W h b v).tsum_sub (trim_sum h b v R) ,add_sub_cancel] -- tune
abbrev summit (R:ℕ)(L:Rules G)(e σ:ℝ):=allowance L e (2*R)+2*Real.exp (-(σ*R))
include V w
lemma travelC (b: Plane n) (p:Light r (menu U t) B (affine s 0 b.1))(ht:0≤t)(z:4*r.val*t≤e)(he:e ≤ L.c)(h₀:2*R+3≤B):
 ‖W.ell (pull s 0 U) b-curtailed W R b (Bid.pulled (scrim U) s)‖ ≤ X*summit R L e σ:=by
 let v:=Bid.pulled (scrim U) s; let T:=pull s 0 U; let A(i:ℕ):=(W.row b.2 i).2; let c(i:ℕ):=(W.row b.2 i).1; let E(i:ℕ):=Real.exp (σ*(A i).length); let P:=allowance L e (2*R); let g:=Real.exp (-(σ*R)); let q(i:ℕ):=|c i| *E i; let f(i:ℕ):=W.ellTerms b i T-trimmed W R b v i; have hs:=h.rows b.2
 have hx:= (hs.2.1.mul_right (summit R L e σ)); have hS:= (W.ell_dominated h b).summable T; have hp:= (hS.sub (trim_sum h b v R)); have hP:0≤P:=allo_nn ..; have hg:0<g:= Real.exp_pos _
 have hz(i:ℕ) : ‖f i‖ ≤ q i * (P+2*g):=by
    unfold f trimmed PathData.ellTerms; split
    next u=>
       rw [sub_zero,norm_smul, Real.norm_eq_abs]; apply (mul_le_mul_of_nonneg_left ((A i).eval_norm _) (abs_nonneg _)).trans; unfold q; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); have hh:1≤E i*g:=by rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith only [show (R:ℝ) ≤ (A i).length by exact_mod_cast u.le, h.width]
       nlinarith only [hh,mul_nonneg (Real.exp_pos (σ*(A i).length)).le hP] -- uses E reducible
    next u=> rw [← smul_sub, norm_smul,Real.norm_eq_abs]; apply (mul_le_mul_of_nonneg_left (cruise V w L _ _ p ht z he (not_lt.mp u) h₀) (abs_nonneg _)).trans; unfold q; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (le_trans (show P≤P+2*g by linarith) (le_mul_of_one_le_left (by linarith) _)) (abs_nonneg _); exact Real.one_le_exp (mul_nonneg h.width.le (by positivity))
 unfold PathData.ell curtailed; rw [← hS.tsum_sub]; apply (norm_tsum_le_tsum_norm hp.norm).trans; apply (hp.norm.tsum_le_tsum hz hx).trans; rw [tsum_mul_right]; apply mul_le_mul_of_nonneg_right hs.2.2; change 0 ≤ P+2*g; linarith
 exact trim_sum h b v R
omit V w h in
lemma sleigh {x y a:ℝ}(u:0≤x)(v:0≤a)(p:y≤a+x)(s:0 < θ)(t:0≤y) : (1-θ)*y^2 ≤ a^2+x^2/θ:=by
 rcases le_or_gt 1 θ with h|h; · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)).trans (by positivity)
 have hP:=pow_le_pow_left₀ t p 2; have h0:0 ≤(1-θ):=by linarith
 refine (mul_le_mul_of_nonneg_left hP h0).trans ?_
 have hs : θ*(a^2+x^2/θ)= θ*a^2+x^2:=by field_simp <;> ring -- tune
 apply le_of_mul_le_mul_left _ s; rw [hs]; nlinarith only [sq_nonneg (θ*(a+x)-x),mul_nonneg s.le (sq_nonneg x)]
-- simplify signature
abbrev vault_fee (C:Clip)(L:Rules G)(X θ e σ:ℝ)(R:ℕ):=C.direct*(allowance L e 4)^2/θ+(X*summit R L e σ)^2/θ
def pansy (W:PathData G)(R:ℕ)(C:Clip)(b:Plane n)(v:fieldDir G n 1):=C.direct* ‖faceCurl b v‖^2 + ‖curtailed W R b v‖^2
lemma rubric {P:BudgetPoint}{m:ℕ} (b: Plane n)(p:Light r (menu U P.threshold) B (affine s 0 b.1))(z:4*r.val*P.threshold≤e)(he:e ≤ L.c)(h₁: m+2≤ B)(k: 2≤ P.threshold * Real.exp ((m:ℝ)/C.relaxation))(h₂:7 ≤ B)(h₀:2*R+3≤B)(hz:0<θ) :
 ((1-θ)*pansy W R C b (Bid.pulled (scrim U) s)-vault_fee C L X θ e σ R)/2 ≤ W.baseTerm C P (pull s 0 U) b:=by
 have hf := P.threshold_pos; have ht:= (p.small h₁).keep hf.le k; have hx:= (p.small h₁).pulls (i:=b) (by simp)
 let u:=(pull s 0 U); let a:=Bid.pulled (scrim U) s; let c:=G.chord (faceValue u b); let E₁:= allowance L e 4; let E₂:= X*summit R L e σ
 have hE₂:0 ≤ E₂:= by apply mul_nonneg (capital W h) (add_nonneg (allo_nn ..) _); positivity
 have hh: ‖faceCurl b a‖ ≤ c+E₁:=by let g:= faceCurl b a; let v:=G.curvature (faceValue u b); calc
    _ ≤ ‖v - g‖ + ‖v‖ := by rw [norm_sub_rev]; exact norm_le_norm_sub_add ..
    _ ≤ c+E₁ := by rw [add_comm c]; exact add_le_add (crop V w L b p hf.le z he h₂) (G.curvature_norm _)
 have hp: ‖curtailed W R b a‖ ≤ ‖W.ell u b‖+E₂:=by
    rw [add_comm]; apply (norm_le_norm_sub_add _ _).trans; rw [norm_sub_rev]; apply add_le_add (travelC V w L h b p hf.le z he h₀) le_rfl
 unfold PathData.baseTerm PathData.clipped pansy vault_fee
 rw [if_pos hx,if_pos ht]; have hH := mul_le_mul_of_nonneg_left (sleigh (θ:=θ) (allo_nn L 4 e) (G.chord_nonneg (faceValue u b)) hh hz (norm_nonneg _)) C.quadratic_pos.le
 have hP:= sleigh hE₂ (norm_nonneg (W.ell u b)) hp hz (norm_nonneg (curtailed W R b a))
 change ((1-θ)*(C.direct* ‖faceCurl b a‖^2+ ‖curtailed W R b a‖^2) -(C.direct* _/θ + E₂^2/θ))/2 ≤ C.direct*c^2/2+‖W.ell u b‖^2/2
 dsimp [c]; simp only [div_eq_mul_inv _ θ] at hH hP ⊢; linarith only [hH,hP]
end YM.Hill.Box
#print axioms YM.Hill.Box.rubric
