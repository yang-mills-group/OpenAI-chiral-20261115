
import Velour.Marocain.Plumes
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


private lemma fileadd {α:Type*} [Semiring α] (w x y:Fin n→α)(i:Fin n)
 (hwx:∀j≠i,w j=x j)(hwy:∀j≠i,w j=y j)(h:w i=x i+y i):
 filepast w = filepast x + filepast y:=by
 induction n with
 | zero=>exact Fin.elim0 i
 | succ n ih=>
   rw [filepast_cons,filepast_cons x,filepast_cons y]
   induction i using Fin.cases with
   | zero=>
      have X:Fin.tail x=Fin.tail w:=funext fun j=>(hwx _ (Fin.succ_ne_zero _)).symm
      have Y:Fin.tail y=Fin.tail w:=funext fun j=>(hwy _ (Fin.succ_ne_zero _)).symm
      rw [X,Y,h,add_mul]
   | succ r=>
      rw [←hwx 0 (Ne.symm (Fin.succ_ne_zero _)),←hwy 0 (Ne.symm (Fin.succ_ne_zero _)), ←mul_add]
      rw [ih (Fin.tail w) (Fin.tail x) (Fin.tail y) r (fun j hj=>hwx _ (by simpa)) (fun j hj=>hwy _ (by simpa)) h]

lemma rise_gauze (X:H.Op)(d:ℕ)(f:Test4):
 S.rise (X*R) d f=S.rise X d f *R:=by
 induction d generalizing f with
 | zero=>exact S.rasp_more_right _ _ (fun b=>S.unit_weight b) f
 | succ d ih=>rw [rise_step,S.rise_step X,ih,ih,add_mul]




def lash (a:Axis): List (Fin n)→ Joint n→ℝ
| []=>P₁
| i::l=> fun f=> lash a l f + lash a l (beat a i f)
lemma lash_price (l:List (Fin n))(f:Joint n):0≤lash a l f:=by
 induction l generalizing f with
 | nil=> exact P₁_nonneg _
 | cons i t ih=> exact add_nonneg (ih f) (ih _)
lemma lash_cont (l:List (Fin n)): Continuous (lash a l):=by
 induction l with
 | nil=>exact P₁_cont
 | cons i t ih=>exact ih.add (ih.comp (beat a _).continuous)
lemma lash_zero (l:List (Fin n)): lash a l 0=0:=by
 induction l with
 | nil=>exact zero_P₁
 | cons i t ih=>simp [lash,ih]

/-- One energy shuttle for each slot in the list, with repetition. -/
def feathers : List (Fin n) → 𝓧 → Joint n →L[ℂ] H.Op
| [],X=> S.procession X
| i::l,X=>feathers l X + (feathers l (update X i (X i*R))).comp (beat a i)
termination_by structural l=>l

lemma feathers_bound (X:𝓧)(l:List (Fin n))(f:Joint n):
 ‖S.feathers l X f‖ ≤ lash a l f * ∏i,‖X i‖ := by
 induction l generalizing X f with
 | nil=>exact S.procession_bill ..
 | cons i t ih=>
    have u: ∀j,‖update X i (X i*R) j‖≤‖X j‖:=by
      intro j
      by_cases h:j=i
      · subst j; rw [update_self]; exact (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) S.gauze_norm)
      rw [update_of_ne h]


    rw [feathers,_root_.add_apply,ContinuousLinearMap.comp_apply,lash,add_mul]
    exact (norm_add_le ..).trans (add_le_add (ih ..)
      ((ih ..).trans (mul_le_mul_of_nonneg_left
       (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>u _)) (lash_price ..))))

lemma feathers_height (X:𝓧)(l:List (Fin n))(f:𝓕):
 S.feathers l X (Joint.materialize n f) = filepast fun i=> S.rise (X i) (l.count i) (f i):=by
 induction l generalizing X f with
 | nil=>
    simpa only [feathers, List.count_nil, rise_zero] using S.procession_pure X f
 | cons i t ih=>
    rw [feathers,_root_.add_apply,ContinuousLinearMap.comp_apply,beat_pure,ih,ih]
    symm
    refine fileadd _ _ _ i ?_ ?_ ?_
    · intro j hj; simp [hj.symm]
    · intro j hj; simp [hj,hj.symm]
    simp [rise_step,S.rise_gauze]



def festers: ∀ n:ℕ,(Fin n→ℕ)→ List (Fin n)
| 0,_=>[]
| n+1,k=> List.replicate (k 0) 0 ++ (festers n (Fin.tail k)).map Fin.succ

#check List.count_map_of_injective
#check Fin.succ_injective
lemma festers_height (k:𝒦)(i:Fin n): (festers n k).count i=k i:=by
 induction n with
 | zero=>exact Fin.elim0 i
 | succ n ih=>
   rw [festers,List.count_append]
   induction i using Fin.cases with
   | zero=>
      have t: (0:Fin (n+1)) ∉ ((festers n (Fin.tail k)).map Fin.succ):=by simp
      rw [List.count_eq_zero_of_not_mem t]; simp
   | succ r=>
      rw [List.count_map_of_injective _ _ (Fin.succ_injective n), ih, List.count_eq_zero_of_not_mem, zero_add]
      · rfl
      simp


abbrev sail (X:𝓧)(k:𝒦):= S.feathers (festers n k) X
lemma sail_pure (X:𝓧)(k:𝒦)(f:𝓕):
 S.sail X k (Joint.materialize n f)=filepast fun i=> S.rise (X i) (k i) (f i) := by
  simp_rw [sail,feathers_height,festers_height]
#print axioms sail_pure

