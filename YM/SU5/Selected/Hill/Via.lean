/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.Hill.Epice
import YM.Next.RANK.Ray
import YM.Work.F02.Path
/-! Upper gauge account: on light plateau, honest linear test; no phase/log outside assumed. Both connection and arbitrary path layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Box
open Function Finset Lattice Tree Wilson RG Exterior Pressure Work.F03 Work.E01 Precision MeasureTheory Next.Rank.Spindle Push Work.F02
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{r:Side}{B R:ℕ}{x y:Site n}{e t:ℝ}{U:Config G n}{s:Signed}
variable (V:(columbia r n).Slice G)(w:U=(columbia r n).drape V)(L:Rules G)
include V w
lemma stamp_curv {y':Axis}(p:Light r (menu U t) 1 (scene s (x,y'):Edge (Site n)).1)(z:4*r.val*t≤ e)(ht:0≤t)(he:e ≤ L.c):
 G.chord ((pull s 0 U) (x,y')) ≤ e ∧ ‖G.curvature (pull s 0 U (x,y'))- Exterior.collect G (Bid.pulled (scrim U) s) (x,y')‖ ≤ L.C*e^2:=by
 let i:=scene s (x,y'); have hh:G.chord (U i) ≤ e:= (p.link V w i.2 ht).trans z; have hp := L.positive; have hv : ‖G.curvature (U i)-Exterior.collect G (scrim U) i‖ ≤ L.C*e^2:=by rw [norm_sub_rev,log_it]; exact (L.bars _ (hh.trans he)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G.chord_nonneg _) hh _) hp.le)
 rw [fold_t]; change G.chord (if (snip s y').neg then (U i)⁻¹ else U i) ≤_ ∧ ‖G.curvature (if (snip s y').neg then (U i)⁻¹ else U i)-(if (snip s y').neg then - Exterior.collect G (scrim U) i else Exterior.collect G (scrim U) i)‖≤ L.C*e^2 -- explicit first hole
 split_ifs
 · simp only [Gauge.chord_inv,Gauge.curvature_inv, ← neg_sub',norm_neg]; exact ⟨hh,hv⟩
 exact ⟨hh,hv⟩
abbrev allowance (L:Rules G)(e:ℝ)(m:ℕ) := (L.C+G.colorScale)*(m:ℝ)^2*e^2
lemma rocaille (m:Walk) (x:Site n)(p: Light r (menu U t) (m.length+3) (affine s 0 x))(ht:0≤t)(z:4*r.val*t≤e)(he:e ≤ L.c) :
 G.chord (travel (pull s 0 U) x m)≤ (m.length:ℝ)*e ∧ ‖G.curvature (travel (pull s 0 U) x m)-linkSum (Exterior.collect G (Bid.pulled (scrim U) s)) x m‖ ≤ allowance L e m.length:=by
 induction m generalizing x with
 | nil=> simp [travel, linkSum,allowance,Gauge.chord_one]
 | cons a m ih=>
    let f:=affine s (0:Site n); let u':=pull s 0 U; let i:= a.used x; let V':=Exterior.collect G (Bid.pulled (scrim U) s); let m':=a.read u' x; let v:= travel u' (x+a.vec) m; let v':= linkSum V' (x+a.vec) m
    let q:= if a.neg then -(V' i) else V' i; have hcost : G.chord m'≤e ∧ ‖G.curvature m'-q‖ ≤ L.C*e^2 := by
       have hh : separation (f x) (scene s i).1 ≤2:= (separation_triangle _ (f i.1) _).trans (Nat.add_le_add (show separation (f x) (f i.1) ≤1 from by simpa [affine,f] using go_by a x) (scene_by s i))
       obtain ⟨hv,hP⟩:= stamp_curv V w L (x:=i.1) (y':=i.2) ((p.small (R:=2+1) (by rw [List.length_cons]; omega)).sees hh) z ht he
       unfold m' q Step.read; split 
       next h=> rw [G.chord_inv,G.curvature_inv,← neg_sub',norm_neg]; exact ⟨hv,hP⟩
       next h=> exact ⟨hv,hP⟩
    specialize ih (x+a.vec) ((p.small (R:=1+(m.length+3)) (by rw [List.length_cons]; omega)).sees (by simpa only [affine, separation_translate,separation_signed] using move_by a x))
    obtain ⟨hc₁,hc₂⟩:= ih
    rw [List.length_cons]; unfold allowance -- need cast add, alias
    change G.chord (m'*v)≤ ((_+1:ℕ):ℝ)*e ∧ ‖G.curvature (m'*v)-(q+v')‖ ≤ _
    push_cast
    have hu :0≤ e:= le_trans (by positivity) z; have hp :=L.positive; have he:= G.colorScale_pos
    constructor
    · rw [add_mul,one_mul]; exact (G.chord_triangle ..).trans ((add_le_add hcost.1 hc₁).trans_eq (add_comm ..))
    let k:=(m.length:ℝ); apply (norm_sub_le_norm_sub_add_norm_sub _ (G.curvature m'+G.curvature v) _).trans
    refine (add_le_add ((Next.Rank.Spindle.weave ..).trans (mul_le_mul (mul_le_mul_of_nonneg_left hcost.1 he.le) hc₁ (G.chord_nonneg _) (mul_nonneg he.le hu))) (le_trans ?_ (add_le_add hcost.2 hc₂))).trans ?_
    · rw [add_sub_add_comm]; exact norm_add_le _ _
    have h0 : 0≤ k:= Nat.cast_nonneg _
    change G.colorScale*e*(k*e)+(L.C*e^2+(L.C+G.colorScale)*k^2*e^2)≤ (L.C+G.colorScale)*(k+1)^2*e^2
    nlinarith only [mul_nonneg h0 (mul_nonneg he.le (sq_nonneg e)),mul_nonneg h0 (mul_nonneg hp.le (sq_nonneg e)),mul_nonneg he.le (sq_nonneg e)]
omit V w
lemma slot_t (s:Slot): (slotWalk s).length ≤ 2*s.length :=by
 simp only [slotWalk, List.length_append, Lattice.reverse,List.length_map,List.length_reverse]; change s.walk.length+4+s.walk.length ≤ 2*(s.walk.length+4); omega
lemma slot_v (L:Slot) (x:Site n)(v:fieldDir G n 1): Exterior.linkSum (Exterior.collect G v) x (slotWalk L)= faceCurl (slotFace L x) v:=by
 have h:= slot_deriv L x v; simp_rw [Work.F02.atSite_curvature] at h; exact (curvature_of_hasDerivAt (Push.travell (slotWalk L) x v)).unique h
end YM.Hill.Box
#print axioms YM.Hill.Box.stamp_curv
#print axioms YM.Hill.Box.rocaille
