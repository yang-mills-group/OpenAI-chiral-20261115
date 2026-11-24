import Compass.Quads
import Compass.Match
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Compass
open Function Spire Scroll Pec Lattice AnalyticBridge.VerifiedReset Moto
-- paint orientation score. Int to use decide.
abbrev decor(i:PlaqAxes):ℤ:=if i=p02∨i=p13 then 1 else if i=p03∨i=p12 then -1 else 0
def times (i:Bool):ℤ:=if i then -1 else 1
lemma sail_decide (s:Signed)(h:Anchored s)(i:PlaqAxes): decor (PlaqAxes.rotate s i)=times (tariffX s) * decor i:=by
 obtain ⟨a,b,c,u⟩:=lists s h; let T:= X (ticket c facing)*X (ticket a side01)* X (ticket b side23)
 have hx:tariffX s=tariffX T:=congrArg (detX ∘ X) u
 have ht : PlaqAxes.rotate s i=PlaqAxes.rotate T i:=by unfold PlaqAxes.rotate; simp_rw [show s.perm=T.perm from u]
 have hi(b:Bool)(f:Equiv.Perm Axis)(i:PlaqAxes):PlaqAxes.rotate (X (ticket b f)) i=if b then PlaqAxes.rotate (X f) i else i:=by cases b; exact rotplain _ rfl i; rfl
 rw [ht,hx]; unfold T; rw [taxes,taxes]
 have hp:tariffX (X facing)=false:=facing_det; have h0:tariffX (X (1:Equiv.Perm Axis))=false:= det_i
 cases c<;> cases a<;> cases b
 all_goals simp only [ticket,↓reduceIte,Bool.false_eq_true,h0,hp,show tariffX (X side01)=true from tax_s _ _ (by decide),show tariffX (X side23)=true from tax_s _ _ (by decide),Bool.true_xor,Bool.false_xor,Bool.not_true,Bool.not_false]
 all_goals clear ht; revert i; decide
lemma prime_C (r:ℝ): HasCrystal (paintS (r:ℂ)):=by
 intro s q h i j
 let w:=SkateGlyph s q
 unfold paintS; by_cases p:i=j; swap
 · have he:PlaqAxes.rotate s i≠PlaqAxes.rotate s j := (PlaqAxes.transform s).injective.ne p; rw [if_pos he,if_pos p,show cSignX _ _=(0:ℂ) from by cases wZ:SkateGlyph s q <;>simp [cSignX],smul_zero,smul_zero]
 subst j; let u:= PlaqAxes.rotate s i; rw [dirS_sq,one_smul,if_neg (not_not_intro rfl),if_neg (not_not_intro rfl)]
 have hr:=sail_decide s h i; unfold decor times at hr
 split_ifs at hr ⊢
 all_goals norm_num at hr
 all_goals cases zv:SkateGlyph s q <;> simp [cSignX, Complex.star_def]
-- norm useful use unit=±1
lemma normP : ‖paintS (1:ℂ)‖ ≤1:=by
 refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j=> ?_; unfold paintS; split_ifs<;>simp
end YM.CF.Compass
