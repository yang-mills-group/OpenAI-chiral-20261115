import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
/-!
# An analytic locality bill: two-sided uniqueness with just one further extension

Part I. A Banach-valued gluing argument. Use ordinary boundary values
(not a.e. or distributional statements). The applications will *not* postulate
analytic spacetime covariant fields, or infer new holomorphy from an angular symmetry.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SatinMacro.Glue
open Complex Function Set Filter Metric MeasureTheory Bornology
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {s : Set ℂ}

private lemma oneSide {z w : ℂ} (h : 0 ≤ min z.im w.im ∨ max z.im w.im ≤ 0)
    (p : Rectangle z w ⊆ s) (c : ContinuousOn f s)
    (d : ∀ u ∈ s, u.im ≠ 0 → DifferentiableAt ℂ f u) :
    wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn _ _ _ (c.mono p)
  intro u t
  have e : u ∈ s := p ⟨Ioo_subset_Icc_self t.1,Ioo_subset_Icc_self t.2⟩
  apply (d u e ?_).differentiableWithinAt
  rcases h with h|h
  · exact (h.trans_lt t.2.1).ne'
  exact (lt_of_lt_of_le t.2.2 h).ne

private lemma twoSides {z w : ℂ} (hz : z.im ≤ 0) (hw : 0 ≤ w.im)
    (p : Rectangle z w ⊆ s) (c : ContinuousOn f s)
    (d : ∀ u ∈ s, u.im ≠ 0 → DifferentiableAt ℂ f u) :
    wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
  let Z : ℂ := z.re
  let W : ℂ := w.re
  have hz' : [[z.im, 0]] ⊆ [[z.im, w.im]] := by
    rw [uIcc_of_le hz, uIcc_of_le (hz.trans hw)]
    exact Icc_subset_Icc le_rfl hw
  have hw' : [[0, w.im]] ⊆ [[z.im, w.im]] := by
    rw [uIcc_of_le hw, uIcc_of_le (hz.trans hw)]
    exact Icc_subset_Icc hz le_rfl
  have ed := oneSide (z:=z) (w:=W)
    (Or.inr (max_le hz (by simp [W]))) (Subset.trans (b:=Rectangle z w)
      (fun x ⟨a,b⟩ => ⟨(show x.re∈[[z.re,w.re]] from a), hz' b⟩) p) c d
  have eu := oneSide (z:=Z) (w:=w)
    (Or.inl (le_min (by simp [Z]) hw)) (Subset.trans (b:=Rectangle z w)
      (fun x ⟨a,b⟩ => ⟨(show x.re∈[[z.re,w.re]] from a), hw' b⟩) p) c d
  rw [wedgeIntegral_add_wedgeIntegral_eq] at *
  simp only [Z,W,ofReal_re,ofReal_im] at eu ed
  let F (x : ℝ) (y : ℝ) := f ((x:ℂ)+(y:ℂ)*Complex.I)
  have cont (x : ℝ) (hx : x ∈ [[z.re,w.re]]) : ContinuousOn (F x) [[z.im,w.im]] := by
    apply c.comp (s:=[[z.im,w.im]]) (f:= fun y : ℝ => (x:ℂ)+(y:ℂ)*I) (by fun_prop)
    intro i hi
    exact p ⟨(show ((x:ℂ)+(i:ℂ)*I).re∈[[z.re,w.re]] by simpa),
       (show ((x:ℂ)+(i:ℂ)*I).im∈[[z.im,w.im]] by simpa)⟩
  have he (x : ℝ) (hx : x ∈ [[z.re,w.re]]) := intervalIntegral.integral_add_adjacent_intervals
    ((cont x hx |>.mono hz').intervalIntegrable (μ:=volume))
    ((cont x hx |>.mono hw').intervalIntegrable (μ:=volume))
  have hez := he z.re left_mem_uIcc
  have hew := he w.re right_mem_uIcc
  unfold F at hez hew
  rw [← hez, ← hew, smul_add, smul_add]
  exact (by grind)

variable [CompleteSpace E]

/-- If `f` is continuous on an open set and holomorphic there off the real edge,
  then it is holomorphic there. -/
theorem analyticOnNhd_of_off (o : IsOpen s) (c : ContinuousOn f s)
    (d : ∀ u ∈ s, u.im ≠ 0 → DifferentiableAt ℂ f u) : AnalyticOnNhd ℂ f s := by
  suffices DifferentiableOn ℂ f s from this.analyticOnNhd o
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn o).mp ⟨fun z w p => ?_,c⟩
  rw [← add_eq_zero_iff_eq_neg]
  rcases le_total z.im 0 with x|x <;> rcases le_total 0 w.im with y|y
  · exact twoSides x y p c d
  · exact oneSide (Or.inr (max_le x y)) p c d
  · exact oneSide (Or.inl (le_min x y)) p c d
  rw [add_comm]
  exact twoSides y x (by rwa [Rectangle,uIcc_comm w.re,uIcc_comm w.im]) c d

local notation3 "Up(" t ")" => { z : ℂ | (t:ℝ) < z.im }
local notation3 "Dn(" t ")" => { z : ℂ | z.im < (t:ℝ) }
local notation3 "ToEdge" => { z : ℂ | z.im ≤ 0 }

private lemma open_up (a : ℝ) : IsOpen (Up(a)) := isOpen_lt continuous_const continuous_im
private lemma open_down (a : ℝ) : IsOpen (Dn(a)) := isOpen_lt continuous_im continuous_const
private lemma open_door (a b r : ℝ) : IsOpen ({z : ℂ| z.re ∈ Ioo a b} ∩ Up(r)) :=
  (isOpen_Ioo.preimage continuous_re).inter (open_up r)

variable {g : ℂ → E} {a b r : ℝ}

/-- Coincidence on a nonempty segment of the edge already enforces equality
throughout an open overlap strip, if one function extends analytically there.
Not assuming analytic edge values of the other. -/
theorem overlap_of_edge (h : a < b) (p : r < 0)
    (F : AnalyticOnNhd ℂ f (Up(r)))
    (G : AnalyticOnNhd ℂ g (Dn(0))) (c : ContinuousOn g ToEdge)
    (w : ∀ x : ℝ, x ∈ Ioo a b → f (x:ℂ) = g (x:ℂ)) :
    EqOn f g (Up(r) ∩ Dn(0)) := by
  let U := Up(r)
  let T := {z : ℂ | z.re∈ Ioo a b}
  let D := T ∩ U
  let k (z : ℂ) := if z.im < 0 then g z else f z
  have eq (z : ℂ) (e : z ∈ D) (t : z.im = 0) : g z = f z := by
    have he := w z.re e.1
    rw [show (↑z.re:ℂ) = z from Complex.ext rfl (by simp [t])] at he
    exact he.symm
  have hD : IsOpen D := open_door a b r
  have hk : ContinuousOn k D := by
    apply ContinuousOn.if
    · intro z hz; exact eq z hz.1 (show z ∈ { z : ℂ | z.im = 0 } from (frontier_setOf_im_lt 0) ▸ hz.2)
    · rw [closure_setOf_im_lt]; exact c.mono inter_subset_right
    exact F.continuousOn.mono (inter_subset_left.trans inter_subset_right)
  have hf (z : ℂ) (t : 0 < z.im) : f =ᶠ[𝓝 z] k := (show ∀ᶠ x : ℂ in 𝓝 z, 0 < x.im from (open_up 0).mem_nhds t).mono
    (fun _ (q : 0 < _)=> (if_neg q.asymm).symm)
  have hg (z : ℂ) (t : z.im < 0) : g =ᶠ[𝓝 z] k := (show ∀ᶠ x : ℂ in 𝓝 z, x.im < 0 from (open_down 0).mem_nhds t).mono
    (fun _ (q : _ < 0)=> (if_pos q).symm)
  have hd : AnalyticOnNhd ℂ k D := by
    apply analyticOnNhd_of_off hD hk
    intro z e t
    rcases lt_or_gt_of_ne t with t|t
    · exact ((G z t).congr (hg z t)).differentiableAt
    exact ((F z e.2).congr (hf z t)).differentiableAt
  have ht : Convex ℝ T := (convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)
  obtain ⟨x,hx,j⟩ := exists_between h
  obtain ⟨y,hy,i⟩ := exists_between p
  have u : (Complex.mk x 1) ∈ D := ⟨⟨hx,j⟩,(lt_trans p zero_lt_one)⟩
  have v : EqOn f k D := (F.mono inter_subset_right).eqOn_of_preconnected_of_eventuallyEq hd
    (ht.inter (convex_halfSpace_im_gt r)).isPreconnected u (hf _ zero_lt_one)
  have he : Complex.mk x y ∈ D := ⟨⟨hx,j⟩,hy⟩
  exact (F.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq (G.mono inter_subset_right)
    ((convex_halfSpace_im_gt r).inter (convex_halfSpace_im_lt 0)).isPreconnected
    (show Complex.mk x y ∈ _ from ⟨hy,i⟩) ((v.eventuallyEq_of_mem (hD.mem_nhds he)).trans (hg _ i).symm)

/-- Liouville now forbids local commutativity at any displacement
with an extending, still-varying heat correlation. Purely analytic bill. -/
theorem rigid_of_edge (h : a < b) (p : r < 0)
    (F : AnalyticOnNhd ℂ f (Up(r)))
    (G : AnalyticOnNhd ℂ g (Dn(0))) (c : ContinuousOn g ToEdge)
    (A : IsBounded (f '' Up(r))) (B : IsBounded (g '' Dn(0)))
    (w : ∀ x : ℝ, x ∈ Ioo a b → f (x:ℂ) = g (x:ℂ)) :
    ∃ v : E, EqOn f (fun _ => v) (Up(r)) ∧ EqOn g (fun _ => v) ToEdge := by
  obtain ⟨y,v,q⟩ := exists_between p
  let k := fun z : ℂ => if z.im < y then g z else f z
  have e := overlap_of_edge h p F G c w
  have fx : EqOn k f (Up(r)) := by
    intro z t; unfold k; split_ifs with x; exact (e ⟨t,x.trans q⟩).symm; rfl
  have gx : EqOn k g (Dn(0)) := by
    intro z t; unfold k; split_ifs with x; rfl; exact e ⟨lt_of_lt_of_le v (not_lt.mp x),t⟩
  have full (z : ℂ) : z ∈ Up(r) ∨ z ∈ Dn(0) := (le_or_gt z.im r).recOn
    (fun s=> Or.inr (lt_of_le_of_lt s p)) (fun s=> Or.inl s)
  have hd : Differentiable ℂ k := by
    intro z; rcases full z with d|d
    · exact ((F _ d).congr (fx.eventuallyEq_of_mem ((open_up r).mem_nhds d)).symm).differentiableAt
    exact ((G _ d).congr (gx.eventuallyEq_of_mem ((open_down 0).mem_nhds d)).symm).differentiableAt
  have sub : Set.range k ⊆ f '' Up(r) ∪ g '' Dn(0) := by
    rintro _ ⟨x,rfl⟩; exact (full x).elim (fun h=> Or.inl ⟨x,h,(fx h).symm⟩) (fun h=> Or.inr ⟨x,h,(gx h).symm⟩)
  obtain ⟨v,t⟩ := hd.exists_const_forall_eq_of_bounded ((A.union B).subset sub)
  · refine ⟨v,fun x h => (fx h).symm.trans (t x),?_⟩
    rw [← closure_setOf_im_lt] at c ⊢
    exact EqOn.of_subset_closure (fun x e=> (gx e).symm.trans (t x)) c continuousOn_const subset_closure Set.Subset.rfl
end YM.SatinMacro.Glue

#print axioms YM.SatinMacro.Glue.rigid_of_edge
