
import Velour.Marocain.Trimmings
import YM.Work.C25
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

open Work.C25

#print YM.Bid.C25
#print axioms YM.Work.C25.answer

def easter : ∀ n:ℕ,(Fin n→ℕ)→ ℕ→ Fin n→ℕ
 | 0,_,_=>fun i=> i.elim0
 | n+1,k,m=> Fin.cons (k 0+m)
      (easter n (Fin.tail k) ((k 0+k 0)+m))

abbrev sheaf (k:𝒦):ℕ:= ∑ i,(k i+k i)

/-- Transfer identity on pure words. -/
lemma easter_price (k:𝒦)(m:ℕ)(X:𝓧)(f:𝓕):
 S.Refines (filepast fun i=> S.hatch (X i) (k i) (f i)) (sheaf k) m
  (S.sail X (easter n k m) (Joint.materialize n f)):=by
 induction n generalizing m with
 | zero=>
    rw [sail_pure]; simp [filepast,sheaf,Refines]
 | succ n ih=>
    have e: sheaf k= sheaf (Fin.tail k)+(k 0+k 0):=by
      rw [Nat.add_comm _ (k 0+k 0),sheaf,Fin.sum_univ_succ]; rfl
    rw [sail_pure,filepast_cons,filepast_cons (fun i =>S.rise (X i) (easter (n+1) k m i) (f i)),e]
    


    have h:=ih (Fin.tail k) ((k 0+k 0)+m) (Fin.tail X) (Fin.tail f)
    rw [sail_pure] at h
    exact (S.hatch_refines _ _ m _).mul h

lemma ext_spring {A:Type*}[AddCommMonoid A][TopologicalSpace A][T2Space A][Module ℂ A]
   (v w:Joint n →L[ℂ] A)
   (h:∀ f:𝓕,v (Joint.materialize n f)=w (Joint.materialize n f)) :
   v=w:= by
  have p:Dense (span n:Set (Joint n)):=fun x=>show x∈(span n).topologicalClosure from
     (show _ from by rw [show (span n).topologicalClosure=⊤ from answer n]; exact Submodule.mem_top)
  exact ContinuousLinearMap.ext_on p (forall_mem_range.mpr h)



def carriage (k:𝒦)(X:𝓧)(m:ℕ)(v:D):
 Joint n →L[ℂ] H.space:=
 (ContinuousLinearMap.apply ℂ H.space (B (sheaf k+m) v).val).comp (S.sail X (easter n k m))

private lemma arrives (k:𝒦)(X:𝓧)(m:ℕ)(v:D):
  (R^m).comp (S.carriage k X m v)=S.carriage k X 0 v:=by
  refine ext_spring _ _ fun f=>?_
  simp only [carriage,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply]
  rw [←S.easter_price k m X f v, S.weight_cancel, ← S.easter_price k 0 X f v,S.weight0]

private lemma plush (k:𝒦)(X:𝓧)(F:Joint n)(v:D):
  S.carriage k X 0 v F ∈ D:=
    (S.muslin_exhibits ..).mpr fun m=> ⟨S.carriage k X m v F,
         DFunLike.congr_fun (S.arrives k X m v) F⟩

private def seats (k:𝒦)(X:𝓧)(F:Joint n): 𝓑 where
  toFun v:= ⟨S.carriage k X 0 v F, S.plush k X F v⟩
  map_add' v w:=by
    refine Subtype.ext ?_
    change S.sail X _ F (B _ (v+w)).val= S.sail X _ F (B _ v).val+S.sail X _ F (B _ w).val
    simp
  map_smul' c v:=by
    refine Subtype.ext ?_
    change S.sail X _ F (B _ (c•v)).val=c • S.sail X _ F (B _ v).val
    simp



/-- Real Minkowski word extension to Joint **on the graph domain**. -/
def coaches (k:𝒦)(X:𝓧): Joint n →ₗ[ℂ] 𝓑 where
  toFun:= S.seats k X
  map_add' _ _:= LinearMap.ext fun _=> Subtype.ext (map_add (S.carriage k X ..) _ _)
  map_smul' _ _:= LinearMap.ext fun _=> Subtype.ext (map_smul (S.carriage k X ..) _ _)

lemma coach_refines (k:𝒦)(X:𝓧)(F:Joint n)(m:ℕ):
 S.Refines (S.coaches k X F) (sheaf k) m (S.sail X (easter n k m) F):=by
 intro v
 refine S.gauze_power_inj m ?_
 rw [weight_cancel]
 exact (DFunLike.congr_fun (S.arrives k X m v) F).symm

lemma coach_pure (k:𝒦)(X:𝓧)(f:𝓕):
 S.coaches k X (Joint.materialize n f)=filepast fun i=> S.hatch (X i) (k i) (f i):=by
 ext1 v
 apply Subtype.ext
 exact ((S.easter_price k 0 X f v).symm.trans (congrArg Subtype.val (S.weight0 _)))

lemma coach_cost (k:𝒦)(X:𝓧)(F:Joint n)(m:ℕ)(v:D):
 ‖B m (S.coaches k X F v)‖ ≤ lash a (festers n (easter n k m)) F * (∏ i,‖X i‖) *
    ‖B (sheaf k+m) v‖:=
 ((S.coach_refines k X F m).bill v).trans
   (mul_le_mul_of_nonneg_right (S.feathers_bound ..) (norm_nonneg _))

#print axioms coach_cost
#print axioms coach_pure

