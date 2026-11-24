import YM.CF.Kea.Mant
import Zephyr.Chern.Bud
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Lat YM.CF.Cube YM.CF.Kea


open scoped Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

def dye : TF := ⟨![1,-1,0,0,0],by norm_num [Fin.sum_univ_succ]⟩

/-- diagonal skew generator weights on matter. -/
def wgt (i:SU.Slot) : ℂ := Complex.I * freqD dye i

def moor (u:ℂ) : Twig :=
  (Matrix.diagonal fun i=> Complex.exp (wgt i * u),
    Matrix.diagonal fun i=> Complex.exp (Complex.I * dye.val i * u))

def diluted (t:ℝ) : TF := ⟨fun i=>t*dye.val i,by rw [←Finset.mul_sum,dye.property,mul_zero]⟩

def arc (t:ℝ) : SU.E := waveG (diluted t)

lemma freq_diluted (t:ℝ)(i:SU.Slot) : freqD (diluted t) i=t * freqD dye i := by
  obtain ⟨_,x|y⟩ := i
  · exact (mul_add _ _ _).symm
  exact (mul_neg ..).symm

lemma arc_zero : arc 0=1 := by
  apply Subtype.ext; apply Subtype.ext
  change Matrix.diagonal _=1
  simp [Function.comp_def,diluted,phase_z]
  exact rfl

lemma arc_add (a b:ℝ): arc (a+b)=arc a*arc b:=by
  rw [arc,arc,arc,tax_mul]
  congr 1
  exact Subtype.ext (funext fun i=>add_mul _ _ _)

lemma arc_neg(t:ℝ): arc (-t)=(arc t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [←arc_add,neg_add_cancel,arc_zero])

lemma brand_arc (t:ℝ) : brand (arc t) = moor t := by
  unfold brand arc moor
  rw [matD]
  change (_,Matrix.diagonal _)=_
  congr 1
  · congr 1
    funext i
    simp only [Function.comp_apply,pw,BZ.phase,wgt,freq_diluted,Complex.ofReal_mul]
    congr 1; ring
  congr 1
  funext i
  simp only [Function.comp_apply,diluted,pw,BZ.phase,Complex.ofReal_mul]
  congr 1; ring

lemma moor_zero : moor 0=1:=by
  rw [←Complex.ofReal_zero,←brand_arc,arc_zero,brand_one]

lemma moor_diff : Differentiable ℂ moor := by
  have h {ι : Type} [Fintype ι] [DecidableEq ι] (w:ι→ℂ) :
      Differentiable ℂ (fun t=>Matrix.diagonal fun i=>Complex.exp (w i*t)) :=
    (Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap.differentiable.comp
      (show Differentiable ℂ (fun t i=>Complex.exp (w i*t)) by fun_prop)
  exact (h _).prodMk (h _)

lemma cont_arc : Continuous arc:=by
  have h : Continuous fun x:ℝ=>brand (arc x):=by
    simp_rw [brand_arc]
    exact moor_diff.continuous.comp Complex.continuous_ofReal
  exact Continuous.subtype_mk (h.snd.subtype_mk _) _

abbrev Angles (N:Side) := Edge (Site N) → ℝ
variable {N:Side}
def petals (A:Angles N)(t:ℝ) : Bkg N := fun i=>arc (A i * t)
lemma petal_idle (A:Angles N): petals A 0=1 := by
  funext i
  simp [petals,arc_zero]
lemma cont_petal (A:Angles N) : Continuous (petals A) :=
  continuous_pi fun _=> cont_arc.comp (continuous_const.mul continuous_id)

def faux (A:Angles N) (t:ℂ) : Stem N:=fun i b=> moor ((if b then A i else -A i : ℝ) * t)

lemma faux_real (A:Angles N)(t:ℝ) : faux A t = profile (petals A t) := by
  funext i b
  cases b <;>
    simp [profile,faux,petals,-Complex.ofReal_neg,←Complex.ofReal_mul,
      ←brand_arc,neg_mul,arc_neg,brand_inv]

lemma faux_zero (A:Angles N):faux A 0=1:=by
  funext i b
  simp [faux,moor_zero]

lemma faux_diff (A:Angles N): Differentiable ℂ (faux A) := by
  rw [differentiable_pi]
  intro i;rw [differentiable_pi];intro b
  exact moor_diff.comp ((differentiable_const _).mul differentiable_id)

lemma petals_safe (A:Angles N){e:ℝ}(he:0<e): ∀ᶠ t in 𝓝 0,Guard (petals A t) e := by
  have hx(x:Site N)(w:Walk) : Continuous fun t=> travel (petals A t) x w:=by
    induction w generalizing x with
    | nil=> exact continuous_const
    | cons y w ih=>
      apply Continuous.mul _ (ih _)
      have hi : ∀ i, Continuous fun t=> petals A t i:=fun i=>
        (continuous_apply i).comp (cont_petal A)
      rcases y with ⟨a,_|_⟩
      · exact hi _
      exact (hi _).inv

  have h {I:Type} [Fintype I] [DecidableEq I](P:SU.E →* UNI I)
      (p:Continuous fun x=>(P x).val) : ∀ᶠ t in 𝓝 0,PlaqBound P (petals A t) e:=by
    have hk:∀ᶠ t in 𝓝 0, ∀ x i j, ‖(P (travel (petals A t) x (square i j))).val-1‖ < e := by
      rw [eventually_all];intro x;rw [eventually_all];intro i; rw [eventually_all];intro j
      have h0: ‖(P (travel (petals A 0) x (square i j))).val-1‖ < e := by
        simpa [petal_idle,square,travel]
      exact ((p.comp (hx x _)).sub continuous_const).norm.continuousAt.eventually
        (gt_mem_nhds h0)
    filter_upwards [hk] with t ht
    intro x i j hne
    exact (ht x i j).le
  exact (h firstF SU.fund_cont).and (h SU.matter SU.matter_cont)
