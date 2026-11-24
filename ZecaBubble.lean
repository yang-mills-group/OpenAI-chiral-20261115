import ZecaVee
import YM.SU5.FiniteGaugeData.Cirrus.Maison
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin

open Boundary

variable (Ω:Bench S) (D:Moment H)
local notation "O"=>Ω.val
variable (h:saucer S Ω.val=Ω.val) (e:∀p,M S p Ω.val=Ω.val)

abbrev tip (z:ℂ): H.Op := (S.E z.re.toNNReal) * (S.edge (-z.im))
lemma tip_eq (z:ℂ)(p:z∈inside): tip S z=S.F z:=by
 have q:0<z.re:=p
 rw [tip,←S.roots_heat (Real.toNNReal_pos.mpr q)]
 refine (S.either (dur.mpr (Real.toNNReal_pos.mpr q)) _).trans ?_
 apply congrArg S.F; apply Complex.ext <;>simp [duration,sideways, q.le]
lemma tip_side (t:ℝ):tip S (sideways t)=S.edge t:=by
 unfold tip; rw [side]; rw [show (-((sideways t).im))=t by simp [sideways],Real.toNNReal_zero,S.eZero]; rfl
lemma bubble_split (u:ℝ≥0)(t:ℝ)(p:0<u)(x y:H):
 inner ℂ x (tip S (duration (u+u)+sideways t) y)=
   inner ℂ (S.E u x) (S.edge t (S.E u y)):=by
 rw [←S.sym u,ContinuousLinearMap.adjoint_inner_left,S.sym,tip_eq _ _ (length.mpr (add_pos p p))]
 have e: S.E u * (S.edge t * S.E u)= S.F (duration (u+u)+sideways t):=by
    rw [←S.roots_heat p]
    rw [show S.edge t * S.F (duration u)=_ from S.along (dur.mpr p) t,show S.F (duration u)*_=_ from (S.pairs (dur.mpr p) ((length (q:=t)).mpr p)).symm]
    simp [duration,add_assoc]
 rw [←e]; rfl

lemma stmt_c (x y:H):Continuous (fun z=>inner ℂ x (tip S z y)):=by
 have l:Continuous (fun z:ℂ=> (z.re.toNNReal,S.edge (-z.im) y)):= (continuous_real_toNNReal.comp continuous_re).prodMk ((S.cont y).comp continuous_im.neg)
 exact continuous_const.inner ((duet S).comp (continuous_swap.comp l))
lemma stmt_a (x y:H):AnalyticOnNhd ℂ (fun z=>inner ℂ x (tip S z y)) inside:=by
 let L:= (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space y)
 intro z p
 refine ((L.analyticAt _).comp (S.localHeat _ p)).congr ?_
 exact ((show ∀ᶠ w in 𝓝 z,w∈inside from open_inside.mem_nhds p).mono fun w p=>congrArg L (tip_eq S w p).symm)

section detect
variable {I:Type}[DecidableEq I][Fintype I] (X Y:I→H)

def bubble (z:ℂ) : Matrix I I ℂ:=Matrix.of (fun i j=>inner ℂ (X i) (tip S z (Y j)))
def Fires (A:Matrix I I ℂ):Prop:= A.det≠0 ∧ ∀i,A i i≠0
def blast(z:ℂ):=(bubble S X Y z).det*∏ i:I,bubble S X Y z i i
lemma blasted(z:ℂ):blast S X Y z≠0↔Fires (bubble S X Y z):=by
 unfold blast Fires; rw [mul_ne_zero_iff,Finset.prod_ne_zero_iff];simp

lemma blast_c:Continuous (blast S X Y):=by
 have c:Continuous (bubble S X Y):=continuous_matrix fun i j=>stmt_c ..
 exact c.matrix_det.mul
       (continuous_finsetProd _ fun i _=> c.matrix_elem i i)

lemma blast_a:AnalyticOnNhd ℂ (blast S X Y) inside:=by
 intro z p
 have hb(i j:I):AnalyticAt ℂ (fun w=> bubble S X Y w i j) z:=stmt_a S (X i) (Y j) z p
 unfold blast
 apply AnalyticAt.mul
 · simp_rw [Matrix.det_apply, Units.smul_def]
   exact Finset.analyticAt_fun_sum _ (fun σ _=>
        (Finset.analyticAt_fun_prod _ (fun i _=> hb (σ i) i)).const_smul)
 exact Finset.analyticAt_fun_prod _ (fun i _=>hb i i)

lemma bubble_found {z:ℂ} (p:z∈inside) (h:Fires (bubble S X Y z)):
 ∃ᶠ r:ℝ in 𝓝 (0:ℝ), Fires (bubble S X Y (sideways (-r))):=by
 contrapose! h
 rw [←blasted,not_not]
 have k:∀ᶠ r in 𝓝 (0:ℝ),blast S X Y ⟨0,r⟩=0:=by
   filter_upwards [h] with r v
   rwa [←blasted,not_not,show sideways (-r)= ⟨0,r⟩ by apply Complex.ext <;> simp [sideways]] at v
 exact Maison.crease _ _ (blast_c S X Y) (blast_a S X Y).differentiableOn k (show 0≤ z.re from (show 0<z.re from p).le)
end detect
