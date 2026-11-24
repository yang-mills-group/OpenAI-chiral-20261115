import ExactRunning.Dyne.Berth
/-!
# Balancing the longitudinal parts of the aliases

A form of horizontal projection, modified in the central mode to keep
the mean constraint. Only needed near zero. The trick here is to adjust
away *every* large high leg, including its contribution in solving the
central constraint, without ever estimating the soft inverse ghost.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Asymptotics
namespace BlockTie
variable (X)

abbrev roll (p) (l : Site X.L) := rollMean X.patch (aliasAt p l)
abbrev cap (p) (l : Site X.L) := capBond (G:=G) (aliasAt p l) X.patch

def adjust (p : Momentum) (i : G.ColorIndex) (l : Site X.L) : Phase (Loc G 0) :=
  if l=0 then -((X.roll p 0)⁻¹ •
    ∑ j ∈ univ.erase 0, X.roll p j • horizontalQ X.Phi p j (stripe i))
  else horizontalQ X.Phi p l (stripe i)

def hatch (p : Momentum) (i) (l : Site X.L) :=
  nose X.Phi p l (stripe i) + pageD G 0 (aliasAt p l) *ᵥ X.adjust p i l

lemma center_adjust {p} (hp : X.roll p 0≠0) (i) :
    ∑ l, X.roll p l • X.adjust p i l = 0 := by
  rw [← add_sum_erase _ _ (mem_univ 0)]
  have e :
    ∑ j ∈ univ.erase (0:Site X.L), X.roll p j • X.adjust p i j =
    ∑ j ∈ univ.erase (0:Site X.L), X.roll p j • horizontalQ X.Phi p j (stripe i) := by
      refine sum_congr rfl fun j hj => ?_
      rw [adjust, if_neg (mem_erase.mp hj).1]
  rw [e,adjust, if_pos rfl]
  rw [smul_neg,smul_smul,mul_inv_cancel₀ hp,one_smul, neg_add_cancel]

lemma hatch_mean {p} (hp : star p=p) (hw : X.roll p 0≠0) (i j) :
    ∑ l, X.cap p l j * X.hatch p i l j =
      (X.result p *ᵥ Pi.single (stripe i) 1) j := by
  let R := meanRay G X.patch p
  let e : Phase (Loc G 1) := Pi.single (stripe i) 1
  have h : ∑ l, R *ᵥ tiled p l (X.hatch p i l) = X.result p *ᵥ e := by
    rw [← X.success hp,←mulVec_mulVec,←alias_pack p (X.Phi p *ᵥ e),mulVec_sum]
    have add {l : Site X.L} (x y : Phase (Loc G 1)) :
        tiled p l (x+y)=tiled p l x+tiled p l y :=
          funext fun _=> mul_add ..
    simp_rw [hatch, add, ← furnish_gear (pageD G 0),mulVec_add,sum_add_distrib]
    have hg (l : Site X.L) (v : Phase (Loc G 0)) :
        R *ᵥ (furnish X.L (pageD G 0) p *ᵥ tiled p l v) =
            pageD G 0 p *ᵥ (X.roll p l • v) := by
      unfold R
      rw [mulVec_mulVec,mean_stern p, ←mulVec_mulVec,jar_aim]
    simp_rw [hg]
    rw [← mulVec_sum (pageD G 0 p),X.center_adjust hw,mulVec_zero,add_zero];rfl
  have := congr_fun h j
  simp_rw [Finset.sum_apply,R,mean_aim] at this
  exact this

lemma roll_zero : X.roll 0 0=1 := by
  simp only [roll,rollMean, show aliasAt 0 (0:Site X.L)=0 from by simp [aliasAt]]
  simp [←Complex.ofReal_sum]; exact X.patch.weight_sum

lemma cap_zero (i) : X.cap 0 0 i=X.L.val := by
  unfold cap capBond
  change X.roll 0 0 * _ = _
  rw [X.roll_zero];simp [aliasAt]

lemma roll_lit (l) : ContDiff ℝ 2 (fun p=> X.roll p l) := by
  simp only [roll,rollMean,aliasAt,mode]
  fun_prop
lemma cap_lit (l i) : ContDiff ℝ 2 (fun p=> X.cap p l i) := by
  simp only [cap,capBond]
  refine (X.roll_lit l).mul ?_
  simp only [aliasAt,mode]; fun_prop

abbrev coin (i : G.ColorIndex) (p) := (X.cap p 0 (stripe i))⁻¹

lemma coin_zero (i) : X.coin i 0=inch X.L := by
  simp [coin,X.cap_zero,inch]

lemma coin_lit (i) : ContDiffAt ℝ 2 (X.coin i) 0 :=
  (X.cap_lit 0 (stripe i)).contDiffAt.inv
    (X.cap_zero _ ▸ by exact_mod_cast (X.L.property.ne'))

def aim (i : G.ColorIndex) (l : Site X.L) (p : Momentum) : Phase (Entry G) :=
  if l=0 then X.coin i p • Pi.single (stripe i) 1 else 0

lemma hatch_high (l : Site X.L) (hl : l≠0) (i) (y : Track) (j) :
    Cost (fun t=> X.hatch (axes (t • y)) i l j) := by
  simp only [hatch,adjust, if_neg hl]
  exact high_halo hl (stripe i) j E.strip E.house E.floor E.strict I.strip I.house
    (fun v => (X.actor (axes_real v)).1) y

lemma cap_gap (y : Track) (i : G.ColorIndex) (j : Entry G) :
    Cost (fun t=>
      let p := axes (t•y)
      X.cap p 0 j * X.hatch p i 0 j - (Pi.single (stripe i) 1:Phase (Entry G)) j) := by
  let f (t : ℝ) := axes (t • y)
  have ht : Tendsto f cutRay (𝓝 0) := by
    rw [← axes_origin]
    exact axes_maps.continuous.continuousAt.tendsto.comp (along y)
  let h (t : ℝ) (l) := X.cap (f t) l j * X.hatch (f t) i l j
  have hx : Cost (fun t=> ∑ l ∈ univ.erase 0, h t l) := by
    refine IsBigO.sum ?_
    intro l hl
    refine ((((X.cap_lit l j).continuous.tendsto 0).comp ht).isBigO_one ℝ
      |>.mul (X.hatch_high l (mem_erase.mp hl).1 i y j)).congr_right (fun _=>one_mul _)

  refine ((X.result_change i y j).sub hx).congr' ?_ EventuallyEq.rfl
  have hu : ∀ᶠ t in cutRay, X.roll (f t) 0 ≠0 :=
    ((X.roll_lit 0).continuous.tendsto 0 |>.comp ht).eventually
      (compl_singleton_mem_nhds (X.roll_zero ▸ one_ne_zero))
  filter_upwards [hu] with t ht
  have hm : ∑ l, h t l=(X.result (f t) *ᵥ Pi.single (stripe i) 1) j :=
    X.hatch_mean (axes_real _) ht i j
  rw [← add_sum_erase _ _ (mem_univ 0)] at hm
  dsimp only [Pi.sub_apply]
  rw [← hm,add_sub_right_comm,add_sub_cancel_right]

lemma hatch_cost (y : Track) (i : G.ColorIndex) (l : Site X.L) (j) :
    Cost (fun t=>
      let p := axes (t•y)
      (X.hatch p i l-X.aim i l p) j) := by
  by_cases hl : l=0
  swap
  · simpa [aim,hl] using X.hatch_high l hl i y j
  subst l
  let f (t : ℝ) := axes (t • y)
  have hz : X.cap 0 0 j≠0 := X.cap_zero _ ▸ by exact_mod_cast (X.L.property.ne')
  have ht : Tendsto (fun t=>X.cap (f t) 0 j) cutRay (𝓝 (X.cap 0 0 j)) :=
    ((X.cap_lit 0 j).continuous.tendsto 0).comp (by
      rw [← axes_origin]
      exact axes_maps.continuous.continuousAt.tendsto.comp (along y))
  refine (((ht.inv₀ hz).isBigO_one ℝ).mul (X.cap_gap y i j)).congr_right (fun _=>one_mul _)
    |>.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually (compl_singleton_mem_nhds hz)] with t ht
  have he : X.cap (f t) 0 j≠0 := ht
  dsimp only [aim,if_true,Pi.sub_apply,Pi.smul_apply]
  rw [mul_sub,show (X.cap (f t) 0 j)⁻¹*_=_ from inv_mul_cancel_left₀ he _]
  by_cases h : j=stripe i
  · subst j; rw [if_pos rfl];rfl
  simp [h]

lemma aim_lit (i l) : ContDiffAt ℝ 2 (X.aim i l) 0 := by
  unfold aim
  split_ifs
  · exact (X.coin_lit i).smul contDiffAt_const
  exact contDiffAt_const

end BlockTie
end ExactRunning
