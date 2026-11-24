
import Velour.Marocain.Verge
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe

variable {n:ℕ}


local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight
local notation "𝓧" => Fin n → H.Op
local notation "𝒦" => Fin n → ℕ
local notation "𝓕" => Fin n → Test4
local notation "𝓑" => Module.End ℂ D
local notation "𝓗" => H.space

local notation "G!" => S.heatL
local notation "E!" => S.E
local notation "𝓛" => Fin n → ℝ≥0
local notation "𝓣" => Fin n → S.Detector
local notation "𝓠" => Fin n → ℝ≥0 → H.Op


private def held₂ : Points 1 ≃ₗᵢ[ℝ] E4 where
 toFun:=fun x=>x 0
 invFun:=fun y=>points fun _=>y
 left_inv:=by intro; ext1 i; rw [Subsingleton.elim i 0]; rfl
 right_inv _:=rfl
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
 norm_map' x:=by
   rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),PiLp.norm_sq_eq_of_L2 _ x]
   simp

def twin : Points 2 ≃L[ℝ] E4 × E4:= Joint.breakAt.trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ..) held₂.toContinuousLinearEquiv)

lemma twin_measure: MeasurePreserving twin volume (volume.prod volume):=
   (((MeasurePreserving.id (volume:Measure E4)).prod held₂.measurePreserving).comp
     ((WithLp.volume_preserving_ofLp E4 (Points 1)).comp (Points.peel (n:=1)).measurePreserving))
private def distancePair : (E4 × E4) ≃L[ℝ] E4 × E4 where 
 toFun:= fun z=>(z.1,z.2-z.1)
 invFun:=fun z=>(z.1,z.2+z.1)
 left_inv:=by intro; simp
 right_inv:=by intro;simp
 map_add':=by intro _ _;ext1; · rfl; 
              change _ +_ - (_+_)= (_ - _)+(_ - _);abel
 map_smul':=by intros;ext1;· rfl;
               exact (smul_sub ..).symm




def leaflet (χ f:Test4) : Joint 2:= Probe.along (twin.trans distancePair) (Probe.combine χ f)

variable (v:H.space)(c:∀p,S.unit.translation p v=v)
include c
lemma inner_translation_left (v':H.space)(p:E4):
 inner ℂ v (U p v')=inner ℂ v v':=by
 rw [← ContinuousLinearMap.adjoint_inner_left]
 change inner ℂ (star (U p) v) v'=_;rw [S.unit_star,c]

lemma parade₂ (X:Fin 2→H.Op)(b:Points 2):
 inner ℂ v (S.parade X b v)=
    inner ℂ (star (X 0) v) (U (b 1-b 0) (X 1 v)):=by
 let e:=X 0
 have p:S.parade X b=S.dangle (b 0) (X 0)*S.dangle (b 1) (X 1):=by
    rw [S.parade_next,S.parade_next,S.parade_zero,mul_one];rfl
 rw [p]
 unfold dangle
 simp_rw [mul_apply_eq_comp, c]
 rw [S.inner_translation_left v c,←mul_apply_eq_comp (U (-(b 0))),S.unit_step,
    add_comm (-(b 0)),←sub_eq_add_neg]
 exact (ContinuousLinearMap.adjoint_inner_left ..).symm



lemma reads_leaflet (χ f:Test4)(X:Fin 2→H.Op):
 inner ℂ v (S.procession X (leaflet χ f) v)=
 (∫ b,χ b) * ∫y,f y* inner ℂ (star (X 0) v) (U y (X 1 v)):=by
 let F(z:E4×E4):= χ z.1 * (f (z.2-z.1)*inner ℂ (star (X 0) v) (U (z.2-z.1) (X 1 v)))
 have e:(fun b=>inner ℂ v (leaflet χ f b • S.parade X b v))=F ∘ ⇑twin:=by
     funext b;rw [inner_smul_right, S.parade₂ v c]
     change (χ (b 0)*f (b 1-b 0))*_=_ * (_*_); rw [mul_assoc];rfl
 rw [procession_apply,← integral_inner (S.p_available ..),e,
     show integral volume (F ∘ ⇑twin)= _ from twin_measure.integral_comp twin.toHomeomorph.measurableEmbedding _,
     integral_prod F]


 · rw [←integral_mul_const]
   refine integral_congr_ae (ae_of_all _ fun b=>?_ )
   dsimp only
   rw [←integral_add_right_eq_self (fun y=>F (b,y)) b]
   dsimp only [F]
   simp_rw [add_sub_cancel_right, integral_const_mul]
 · apply (twin_measure.integrable_comp_emb twin.toHomeomorph.measurableEmbedding).mp
   rw [←e]
   exact (S.p_available ..).const_inner _
#print axioms reads_leaflet

