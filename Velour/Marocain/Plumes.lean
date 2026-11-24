
import Velour.Marocain.Cortege
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



lemma procession_combine (X:Fin (n+1)→H.Op)(g:Test4)(w:Joint n):
 S.procession X (Joint.combine g w)= S.rasp (X 0) g * S.procession (Fin.tail X) w:=by
 ext1 v
 rw [S.procession_apply,mul_apply_eq_comp,S.rasp_apply]
 let F(p:E4 × Points n):= (g p.1 * w p.2) •
      S.dangle p.1 (X 0) (S.parade (Fin.tail X) p.2 v)
 let e:=@Joint.breakAt n
 have h:MeasurePreserving e volume (volume.prod volume):=
    (WithLp.volume_preserving_ofLp E4 (Points n)).comp Points.peel.measurePreserving
 have H₁ : (fun b => Joint.combine g w b • S.parade X b v)=F ∘ e:=by funext b; rw [Joint.combine_at,S.parade_next]; rfl
 have p:=(h.integrable_comp_emb e.toHomeomorph.measurableEmbedding (g:=F)).mp 
      (H₁ ▸ S.p_available X (Joint.combine g w) v)
 rw [H₁,show integral volume (F ∘ e) = integral _ F from h.integral_comp e.toHomeomorph.measurableEmbedding F,integral_prod F p]
 refine integral_congr_ae (ae_of_all _ fun b=>?_ )
 dsimp only
 rw [procession_apply,← (S.dangle b (X 0)).integral_comp_comm (S.p_available ..),←integral_smul]
 dsimp only [F]
 simp_rw [map_smul,mul_smul]

lemma procession_pure
(X:𝓧)(f:𝓕) :
 S.procession X (Joint.materialize n f)=filepast fun i=> S.rasp (X i) (f i):=by
 induction n with
 | zero=>
    ext1 v
    rw [S.procession_apply, Points.volume_nil, integral_dirac]
    simp [S.parade_zero, filepast]
 | succ n ih=>
    ext1 v
    rw [filepast_cons,mul_apply_eq_comp]
    change S.procession X (Joint.combine (f 0) (Joint.materialize n (Fin.tail f))) v =
      S.rasp (X 0) (f 0)
         (filepast (fun i=>S.rasp (Fin.tail X i) (Fin.tail f i)) v)
    rw [← ih, S.procession_combine, mul_apply_eq_comp]
    

#print axioms procession_pure


def tickPoint (a:Axis)(i:Fin n):Points n:=points (update (fun _=>0) i (basis a))

def beatTick (a:Axis)(i:Fin n): Joint n →L[ℂ] Joint n:=
   LineDeriv.lineDerivOpCLM ℂ (Joint n) (tickPoint a i)

lemma material_slot (i:Fin n)(f:𝓕)(x:Points n):
 Joint.materialize n f x = f i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j):=by
 rw [Joint.material_at]
 exact (Finset.mul_prod_erase _ (fun j=> f j (x j)) (Finset.mem_univ i)).symm

lemma material_update (i:Fin n)(f:𝓕)(g:Test4)(x:Points n):
 Joint.materialize n (update f i g) x = g (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j):= by
 rw [material_slot i,update_self]
 congr 1
 exact Finset.prod_congr rfl fun j hj=>by rw [update_of_ne (Finset.mem_erase.mp hj).1]

lemma tick_joint (i:Fin n)(f:𝓕)(a:Axis):
  beatTick a i (Joint.materialize n f)= Joint.materialize n (update f i (tick a (f i))):= by
 ext1 x
 rw [material_update]
 have h:=Joint.materialize n f|>.differentiableAt (x:=x)|>.hasFDerivAt.hasLineDerivAt (tickPoint a i)
 have t:=tick_obeys (a:=a) (f i) (x i)
 unfold HasLineDerivAt at h t
 


 refine h.unique ((t.mul_const _).congr_of_eventuallyEq (Eventually.of_forall fun r=>?_ ))
 dsimp only; rw [material_slot i]
 congr 1
 · simp [tickPoint]
 exact Finset.prod_congr rfl fun j hj=>by simp [tickPoint,(Finset.mem_erase.mp hj).1]

def beat (a:Axis)(i:Fin n): Joint n →L[ℂ] Joint n:= I • beatTick a i
lemma beat_pure (i:Fin n)(f:𝓕)(a:Axis):
  beat a i (Joint.materialize n f)= Joint.materialize n (update f i (shuttle a (f i))):=by
 rw [beat,_root_.smul_apply,tick_joint]
 ext1 x
 rw [_root_.smul_apply,material_update,material_update,shuttle,_root_.smul_apply,_root_.smul_apply]
 exact (mul_assoc ..).symm
#print axioms beat_pure

