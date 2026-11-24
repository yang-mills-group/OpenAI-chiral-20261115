import GaugeFieldConstruction.Neon
import Mathlib.LinearAlgebra.Projection

/-!
# Whitehead for compact rotation. Via representation Casimir. Preliminary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Function Module Cauchy Stage Set
open scoped BigOperators
variable {X : Type*} [AddCommGroup X] [Module ℝ X]

abbrev Bile (X : Type*) [AddCommGroup X] [Module ℝ X]:= G→ₗ[ℝ]G→ₗ[ℝ]X
lemma action_sum (s: S3) (f : S3→X): ∑ i:S3,f i=f s+f (cw s)+f (ccw s) := by
  rw [show ∑ i:S3,f i=f 0+f 1+f 2 from by simp [Fin.sum_univ_succ,add_assoc]]
  fin_cases s
  · rfl
  · change _= f 1+f 2+f 0; abel
  change _=f 2+f 0+f 1; abel
lemma sync (p:Bool) (f:Bool→X) : ∑ i:Bool,f i=f p+f (!p):= by cases p <;> simp [add_comm]

lemma series (f:Bile X) (u:G): (∑ i:Tape, f (bracket (wall i) u) (wall i)+ ∑ i:Tape,f (wall i) (bracket (wall i) u))=0:= by
  have h (p i): (∑ j : Tape, f (bracket (wall j) (mot p i)) (wall j)+∑ j:Tape,f (wall j) (bracket (wall j) (mot p i)))=0:=by
    let k:=cw i; let s:=ccw i
    have he : bracket (mot p k) (mot p i) = -mot p s := (flips ..).trans (congr_arg _ (sym_sr p i))
    have ht : bracket (mot p s) (mot p i)=mot p k:= by simpa only [k,s,cwc, show ccw (ccw i)=cw i by fin_cases i <;> decide] using sym_sr p (ccw i)
    have hg j : bracket (mot (!p) j) (mot p i)=0 := by rw [flips,away_pair,neg_zero]
    rw [← Finset.sum_add_distrib,Fintype.sum_prod_type,sync p]; simp_rw [wall]; simp only [hg,map_zero, LinearMap.zero_apply,add_zero,Finset.sum_const_zero]
    rw [action_sum i]; simp only [self,map_zero,LinearMap.zero_apply]; change (0+0)+(f (bracket (mot p k) _) _ + f _ (bracket (mot p k) _)) + (f (bracket (mot p s) _) _+f _ (bracket (mot p s) _))= _; rw [he,ht]; simp only [map_neg,LinearMap.neg_apply]; abel
  let g (i:Tape) := f.flip (wall i) ∘ₗ bracket (wall i)+(f (wall i) ∘ₗ bracket (wall i))
  let P:=∑ i:Tape,g i
  have he (u:G):P u=(∑ i:Tape,f (bracket (wall i) u) (wall i))+∑ i:Tape,f (wall i) (bracket (wall i) u) := by rw [← Finset.sum_add_distrib,show P u=_ from LinearMap.sum_apply ..]; rfl
  rw [← he, ← Apit.repr u,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [map_smul, he, show (∑ j:Tape,f (bracket (wall j) (wall i)) (wall j)) + (∑ j:Tape,f (wall j) (bracket (wall j) (wall i)))=0 from h i.1 i.2, smul_zero]

abbrev Tour (X : Type*) [AddCommGroup X] [Module ℝ X] := G→ₗ[ℝ]Endr X
structure Stood (S:Tour X):Prop where
  acts i j : S (bracket i j)= S i * S j-S j*S i
structure Dome (S:Tour X) where
  form : X→ₗ[ℝ] X→ₗ[ℝ] ℝ
  sym i j:form i j=form j i
  pos i:i≠0→ 0<form i i
  neg a i j:form (S a i) j= - form i (S a j)

variable {S : Tour X}
def mtx (S : Tour X):Endr X:=∑ i:Tape,(S (wall i) * S (wall i))
lemma jmt (x:X): mtx S x=∑ i:Tape,S (wall i) (S (wall i) x):= by unfold mtx; rw [LinearMap.sum_apply]; rfl
lemma companion (U:Stood S) (s:G): Commute (mtx S) (S s):= by
  let Q: Bile (Endr X):= ((LinearMap.llcomp ℝ X X X).compl₁₂ S S)
  have ht := series Q s
  have e i : S (wall i) * S (wall i) * S s - S s * (S (wall i)*S (wall i)) = Q (bracket (wall i) s) (wall i)+Q (wall i) (bracket (wall i) s) :=by
    change _ = S _* S (wall i)+ S (wall i)* S _; rw [U.acts]; noncomm_ring
  apply sub_eq_zero.mp; unfold mtx; rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]; simp_rw [e]; rw [Finset.sum_add_distrib,ht]

variable (F:Dome S)
lemma negMetric (x y:X) : F.form (mtx S x) y= -(∑ i:Tape, F.form (S (wall i) x) (S (wall i) y)) := by rw [jmt,map_sum,LinearMap.sum_apply,← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _=> F.neg ..
lemma transport (x y:X) : F.form (mtx S x) y=F.form x (mtx S y):=by
  rw [F.sym x,negMetric, negMetric]; congr 1; exact Finset.sum_congr rfl fun _ _=>F.sym .. -- F unsure
include F
lemma ker_price (x:X) (p:mtx S x=0) (a:G): S a x=0:=by
  have u:=negMetric F x x; rw [p,map_zero,LinearMap.zero_apply] at u
  have q : (∑ i:Tape,F.form (S (wall i) x) (S (wall i) x))=0 := neg_eq_zero.mp u.symm
  have he v:0≤F.form v v:=by by_cases h:v=(0:X); simp [h]; exact (F.pos v h).le
  have hw j:S (wall j) x=0:=by
    by_contra y
    have v:=Finset.single_le_sum (f:=fun i:Tape=> F.form (S (wall i) x) (S (wall i) x)) (fun i _=>he _) (Finset.mem_univ j)
    rw [q] at v; exact not_lt_of_ge v (F.pos _ y)
  rw [← Apit.repr a, map_sum, LinearMap.sum_apply]; simp_rw [map_smul, LinearMap.smul_apply,hw, smul_zero, Finset.sum_const_zero]
lemma non (u:X) (p:u∈ LinearMap.ker (mtx S)) (h:u ∈ LinearMap.range (mtx S)): u=0:= by
  obtain ⟨x,rfl⟩:=h
  by_contra v; have w:= F.pos _ v; rw [transport,show mtx S (mtx S x)=0 from p,map_zero] at w; exact lt_irrefl _ w
variable [FiniteDimensional ℝ X]
lemma poles : IsCompl (LinearMap.ker (mtx S)) (LinearMap.range (mtx S)) := by
  let R:=LinearMap.ker (mtx S); let v:=LinearMap.range (mtx S)
  have p :Disjoint R v := by rw [Submodule.disjoint_def]; exact fun a i z=> non F a i z
  apply IsCompl.mk p; apply codisjoint_iff.mpr
  apply Submodule.eq_top_of_finrank_eq
  have h:= LinearMap.finrank_range_add_finrank_ker (mtx S); have he:=Submodule.finrank_sup_add_finrank_inf_eq R v; rw [p.eq_bot,finrank_bot,add_zero] at he; rw [he]; exact (add_comm _ _).trans h -- name

def oct := (LinearMap.ker (mtx S)).projection _ (poles F)
lemma oct_mem (x:X): oct F x∈LinearMap.ker (mtx S):= Submodule.projection_apply_mem (poles F) x
lemma oct_id (x:X) (p:mtx S x=0): oct F x=x:=Submodule.projection_apply_of_mem_left (poles F) p
lemma no_oct (u:Stood S) (i x): oct F (S i x)=0:= by
  have R (s:X) (p:s∈LinearMap.range (mtx S)): S i s∈LinearMap.range (mtx S):=by
    obtain ⟨x,rfl⟩:=p; exact ⟨S i x,LinearMap.congr_fun (companion u i) x⟩
  let v:=oct F x
  have ht:x-v∈LinearMap.range (mtx S):= Submodule.sub_projection_mem (poles F) x
  apply Submodule.projection_apply_of_mem_right (poles F)
  have he:= R _ ht; rw [map_sub,ker_price F v (oct_mem F x) i,sub_zero] at he; exact he

def vista := mtx S +oct F
lemma high : Injective (vista F) := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
  intro x h; change mtx S x+oct F x=0 at h; have he:= eq_neg_of_add_eq_zero_left h
  have p:mtx S x=0:= non F _ (by rw [he]; exact Submodule.neg_mem _ (oct_mem F x)) ⟨_,rfl⟩; rw [oct_id F x p,p,zero_add] at h; exact h))
def mac := LinearEquiv.ofBijective _ ⟨high F, LinearMap.surjective_of_injective (high F)⟩
lemma mac_p (U:Stood S) (i x) : mac F (S i x)= S i (mac F x) := by
  change mtx S (S i x)+oct F (S i x)= S i (mtx S x+oct F x); rw [no_oct F U, map_add,ker_price F _ (oct_mem F x)]
  exact congr_arg (fun z:X=>z+0) (LinearMap.congr_fun (companion U i) x)
end YM.GaugeFieldConstruction.Apit
