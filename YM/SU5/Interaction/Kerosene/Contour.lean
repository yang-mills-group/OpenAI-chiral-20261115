import YM.CF.Cadre.Bezel

/- Single-step variant of `Cadre` incidence charging (vsp.Dev). Buy *sequential* Mark coats
 using NON-uniform support valuation. Inflation purchased per future Rinse, released precisely
 on the old-support neighbors. Keeps also the normal total tariff, no dependence on count of
 roots after simultaneous purchase at this one mesh.

  Rational from (74), with overlap-cost distribution instead of metric. Since every new term
 has exactly the new root in support, this will even pay unflagged increments at Q*cool when
 the kernel is only cool *with no factor Q*, provided the free term itself has that burn.
 -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)

abbrev contour (C:Palot.leaf A→ℝ)(X:Palot.leaf A):ℝ:=∑ Y∈blaze X,C Y
abbrev style (W C:Palot.leaf A→ℝ)(X:Palot.leaf A):ℝ:= W X* Real.exp (contour C X)

private lemma style_add_one (W C:Palot.leaf A→ℝ)(X:Palot.leaf A)(p:0≤W) : W X+W X*contour C X ≤ style W C X:=by
 have hv:=Real.add_one_le_exp (contour C X); unfold style; rw [mul_comm (W X),mul_comm (W X),show W X+_= (contour C X+1)*W X from by ring]; exact mul_le_mul_of_nonneg_right hv (p X)

variable (Z:Palot.leaf A→ℝ)(hZ:0 ≤ Z)
include hZ
lemma contour_beam (X:Palot.leaf A)(G:hook A)(p:G∈drum X Y ∅) : contour Z X ≤ contour Z Y + ∑ i∈G, contour Z i := by
 have hx: X.val= Y.val∪robe G:= (drum_p ..|>.mp p).2.2
 let V i (X:Palot.leaf A):= if i∈blaze X then Z i else 0
 have hv(i X):0≤ V i X:= ite_nonneg (hZ _) le_rfl
 have ht(X:Palot.leaf A):contour Z X=∑ i,V i X:=by unfold contour V; rw [sum_filter]; simp [blaze]
 simp_rw [ht]; rw [sum_comm (s:=G),←sum_add_distrib]; refine sum_le_sum fun i _=>?_
 by_cases t:i∈blaze X; swap; · rw [show V i X=0 from if_neg t]; exact add_nonneg (hv ..) (sum_nonneg fun i _=> hv ..)
 obtain ⟨j,a,l⟩:= not_disjoint_iff.mp ((mem_filter.mp t).2)
 rw [show V i X=Z i from if_pos t]; rcases mem_union.mp (show j∈ Y.val∪robe G from hx ▸ a) with a|a
 · rw [show V i Y=Z i from if_pos (show i ∈ blaze Y from mem_filter.mpr ⟨mem_univ _, not_disjoint_iff.mpr ⟨j,a,l⟩⟩)]; exact le_add_of_nonneg_right (sum_nonneg (fun _ _=>hv ..))
 obtain ⟨b,p,q⟩:=mem_biUnion.mp a
 have hh:V i b=Z i:= if_pos (show i ∈ blaze b from mem_filter.mpr ⟨mem_univ _,not_disjoint_iff.mpr ⟨j,q,l⟩⟩)
 exact (hh.symm.trans_le (single_le_sum (fun j _=>hv i j) p)).trans (le_add_of_nonneg_left (hv ..))
omit hZ
abbrev WarmStyle (W:Palot.leaf A→ℝ): Prop:=∀ (X Y:Palot.leaf A)(G:hook A),G∈drum X Y ∅→ W X ≤ W Y*tilt W G
variable (W P Q: Palot.leaf A→ℝ)
variable (pW:WarmStyle W)(hw:0 ≤ W)(hp:0 ≤ P)(hq:0 ≤ Q)(γ:ℝ)(hγ:0 ≤ γ)
include hZ pW hw
lemma Style_beam : WarmStyle (style W Z) := by
 intro X Y G p
 have he:= Real.exp_monotone (contour_beam Y Z hZ X G p); rw [Real.exp_add, Real.exp_sum (s:=G)] at he
 have hv:0≤ W Y*tilt W G:=mul_nonneg (hw Y) (prod_nonneg fun i _=>hw i)
 exact (mul_le_mul (pW X Y G p) he (Real.exp_pos _).le hv).trans_eq (by unfold style tilt; rw [prod_mul_distrib]; ring)
variable (hP:∀ i:A,nook (P*W) i ≤ γ)(H:fog W Q γ ≤ Z)
omit hZ
include hP H hp hq hγ
private lemma wake_nearer (o:A): vaultℜ P Q W o ≤ shelfR Z o*γ+nook (P*W*contour Z) o:=by
 let C:=P*W; have hc:0 ≤ C:=fun i=>mul_nonneg (hp i) (hw i)
 let f(Y:Palot.leaf A):=if o∈ Y.val then Z Y*((Y.val.card:ℝ)*γ) else 0
 let g(Y:Palot.leaf A):= Z Y*∑ X∈spark o∩blaze Y,C X
 have ht: vaultℜ P Q W o≤ ∑ Y:Palot.leaf A,(f Y+g Y):=by
    unfold vaultℜ; simp_rw [sum_mul]; rw [sum_comm]
    apply sum_le_sum; intro Y _; refine (aura Y o Q P W hq hp hw pW hP).trans ?_; let u:= contour Z
    apply add_le_add; swap; · exact mul_le_mul_of_nonneg_right (H Y) (sum_nonneg fun i _=>hc _)
    unfold f; split_ifs
    · exact mul_le_mul_of_nonneg_right (H Y) (by positivity)
    exact le_rfl
 rw [sum_add_distrib,show ∑ x:Palot.leaf A,f x=shelfR Z o*γ from by unfold f shelfR; rw [←sum_filter,sum_mul]; simp_rw [mul_assoc],show ∑ y:Palot.leaf A,g y=nook (C*contour Z) o from canal Z C o] at ht
 exact ht
lemma wake_contour (o:A):nook (P*W) o+ vaultℜ P Q W o ≤ nook (P*style W Z) o + shelfR Z o*γ := by
 have he: nook (P*W) o+nook (P*W*contour Z) o ≤ nook (P*style W Z) o:=by
    unfold nook; rw [←sum_add_distrib]; refine sum_le_sum fun i _=> ?_
    simp only [Pi.mul_apply,mul_assoc,←mul_add]; exact mul_le_mul_of_nonneg_left (style_add_one _ _ _ hw) (hp i)
 linarith only [he,wake_nearer Z W P Q pW hw hp hq γ hγ hP H o]

omit pW hw hp hq hγ hP H
variable {I:Type*}[DecidableEq I]
-- dynamic weighting associated with a batch. No geometry hypothesis on spacing here.
variable (C E: I→Palot.leaf A→ℝ)(G:Finset I)
variable (hC:∀ i∈G,0 ≤ C i)
/-- Finset Z. Need order still when evolving! have powerset. -/
abbrev maestro (c:I→Palot.leaf A→ℝ)(G:Finset I)(W:Palot.leaf A→ℝ): Palot.leaf A→ℝ := style W (∑ i∈G,c i)
variable (b:Palot.leaf A→ℝ)(s:ℝ)(u:Tour b s)
variable (t:ℝ)
local notation "Xh" t:max=> loom_v t 0 b 0
include hC
lemma paidContour (X:Palot.leaf A):0 ≤ contour (∑ i∈G,C i) X:= sum_nonneg fun i _=>by rw [Finset.sum_apply]; exact sum_nonneg fun j z=> hC j z i
lemma maestro_warm (hw:0≤W)(pW:WarmStyle W): WarmStyle (maestro C G W):= Style_beam (∑ i∈G,C i) (fun X=>by rw [Finset.sum_apply]; exact sum_nonneg (fun i p=> hC i p X)) W pW hw
lemma maestro_lo (hw:0 ≤ W): W≤ maestro C G W:= fun i=> le_mul_of_one_le_right (hw i) (Real.one_le_exp (paidContour C G hC i))
include u
lemma maestro_salary (c:ℝ)(p:0 ≤ c)(v:∀ i:A,nook (∑ k∈G,C k) i ≤ c) : maestro C G (Xh t) ≤ Xh (t+s*c) := by
 let f:=∑ i∈G,C i; have hp:0≤ f := Finset.sum_nonneg hC
 intro i
 unfold maestro style loom_v; rw [←Real.exp_add]; apply Real.exp_monotone; have he:= beam i f hp c (fun i _=>v i)
 have hx:= he.trans (mul_le_mul_of_nonneg_right (u.rate i) p)
 change contour (∑ i∈G,C i) i≤ _ at hx
 nlinarith only [hx]
lemma maestro_beam (hv:0 ≤ t): WarmStyle (maestro C G (Xh t)):= maestro_warm _ C G hC (fun i=> (Real.exp_pos _).le) (fun X Y G p=> tier t 0 b u 0 (by linarith) le_rfl X Y G ⟨le_rfl,le_rfl⟩ p)
omit hC u
lemma maestro_insert (i:I)(v:i∉G):maestro C (insert i G) W=style (maestro C G W) (C i):=by
 unfold maestro; funext X; unfold style contour; rw [sum_insert v]; simp_rw [Pi.add_apply,sum_add_distrib,Real.exp_add]; ring
lemma maestro_plus {S T:Finset I}(q:S ⊆ T)(hW:0 ≤ W)(h:∀ i∈ T,0 ≤ C i): maestro C S W ≤ maestro C T W :=by
 intro X; apply mul_le_mul_of_nonneg_left _ (hW X); apply Real.exp_monotone; exact sum_le_sum fun i _=> by simp_rw [Finset.sum_apply]; exact sum_le_sum_of_subset_of_nonneg q fun i l _=> h i l _
end YM.CF.Cadre
#print axioms YM.CF.Cadre.wake_contour
