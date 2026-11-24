import GaugeFieldConstruction.Neutron

/-!
# Whitehead capacity on so(4), compact-metric version
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Function Module Cauchy Stage Set
open scoped BigOperators
section
variable {X : Type*} [AddCommGroup X] [Module ℝ X]

abbrev C1 (X : Type*) [AddCommGroup X] [Module ℝ X]:= G→ₗ[ℝ]X
def opposite (X : Type*) [AddCommGroup X] [Module ℝ X] : Submodule ℝ (Bile X) where
  carrier:={v|∀ x y,v x y+v y x=0}
  add_mem' {x y} u v :=fun a b=>by simp only [LinearMap.add_apply]; rw [add_add_add_comm,u a b,v a b,add_zero]
  smul_mem' c x u:=fun a b=>by simp only [LinearMap.smul_apply]; rw [← smul_add,u a b,smul_zero]
  zero_mem':= fun a b=>by simp
abbrev C2 (X : Type*) [AddCommGroup X] [Module ℝ X]:= ↥(opposite X)
lemma swap (p : C2 X) (x y) : p.val x y= -p.val y x:= eq_neg_of_add_eq_zero_left (p.property x y)
lemma same₂ (p : C2 X) (x): p.val x x=0:= by
  have h : (2:ℝ) • p.val x x=0:= by rw [two_smul]; exact p.property _ _
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

variable {S : Tour X}
-- define using function construction, keep Wein costs

def dmark (S:Tour X) (p:C1 X) : Bile X :=
  let F : G→ₗ[ℝ] G→ₗ[ℝ] X := (LinearMap.llcomp ℝ G X X).flip p ∘ₗ S
  F-F.flip-bracket.compr₂ p
def lone (S:Tour X):C1 X →ₗ[ℝ] C2 X where
  toFun p:=⟨dmark S p,fun x y=>by
    change _ - _-p (bracket x y)+(_ -_-p (bracket y x))=0; rw [flips,map_neg]; change S x (p y)-S y (p x)- -p _+(S y (p x)- S x (p y)-p _)=_; abel⟩
  map_add' v w:= by
    apply Subtype.ext; ext1 x; ext1 y
    change S x (v y+w y) - S y (v x+w x)-(v _+w _) = (_-_-_)+ (_-_-_); simp only [map_add]; change _=(S x (v _)-S y (v _)-v _)+(S x (w _) - S y (w _) -w _); abel
  map_smul' r v:= by
    apply Subtype.ext; ext1 x; ext1 y
    change S x (r • v y) - S y (r • v x)-r • v _=r • (S x (v y)-S y (v x)-v _); rw [map_smul,map_smul,smul_sub,smul_sub]
lemma turn (v:C1 X) (x y:G): (lone S v).val x y=S x (v y)-S y (v x)-v (bracket x y):=rfl

def Cycle (S:Tour X) (v:C2 X): Prop := ∀ x y z, S x (v.val y z) + S y (v.val z x) + S z (v.val x y) = v.val (bracket x y) z + v.val (bracket y z) x + v.val (bracket z x) y

variable (P:Stood S)
include P
lemma s_roll (x y:G) (v:X): S x (S y v) = S y (S x v)+S (bracket x y) v:=by rw [P.acts]; change S x (S y v)= S y (S x v) + (S x (S y v)- S y (S x v)); simp
lemma cycle (p:C1 X): Cycle S (lone S p):= by
  intro x y z; simp only [turn,map_sub, LinearMap.add_apply];
  rw [s_roll P x y, s_roll P y z,s_roll P z x] -- rw first match
  have Q:= p.map_zero
  have h: p (bracket (bracket x y) z) + p (bracket (bracket y z) x) + p (bracket (bracket z x) y)=0:= by
    rw [← map_add,← map_add,flips (bracket x y), flips (bracket y z),flips (bracket z x), ← neg_add,← neg_add,jac z x y,neg_zero,map_zero]
  simp only [P.acts,LinearMap.sub_apply,Module.End.mul_apply]; rw [eq_neg_of_add_eq_zero_right h]; abel
omit P

def hooked (L:Endr X) (p:C2 X):C2 X:=⟨p.val.compr₂ L,fun x y=>by change L (p.val x y)+L _=0; rw [← map_add,show p.val x y+p.val y x=0 from p.property x y,map_zero]⟩
lemma Cycle.map {v:C2 X} (p:Cycle S v) {M: Endr X} (h : ∀ i k,M (S i k)=S i (M k)): Cycle S (hooked M v):= by
  intro i j k; change S _ (M (v.val j k))+S _ (M (v.val k i))+S _ (M (v.val i j))= M (v.val _ _)+M (v.val _ _)+M (v.val _ _)
  simp_rw [← h,← map_add]; exact congr_arg M (p i j k)
lemma bothD (v:C1 X) (M:Endr X) (h:∀ i k,M (S i k)=S i (M k)): lone S (M ∘ₗ v)=hooked M (lone S v):= by apply Subtype.ext; ext1 i; ext1 j; rw [turn]; change S i (M (v j))-S j (M (v i))-M _=M _; simp only [turn,h,map_sub]

-- order zero: elementary
include P in
lemma ideal (x:X): lone S (S.flip x)=0:=by apply Subtype.ext; ext1 i; ext1 j; rw [turn]; change S i (S j x)-S j (S i x)-S _ x=0; rw [P.acts]; exact sub_self _
lemma quiet1 (p:C1 X) (v:lone S p=0) (h:∀ i k,S i (p k)=0):p=0:= by
  have he i j : p (bracket i j)=0 := by
    have hv:= congr_arg (fun (r:C2 X)=>r.val i j) v; change (lone S p).val i j=(0:X) at hv; rw [turn,h,h,sub_zero,zero_sub] at hv; exact neg_eq_zero.mp hv
  apply LinearMap.ext; intro x
  rw [← Apit.repr x,map_sum]; simp only [LinearMap.zero_apply]; apply Finset.sum_eq_zero; intro i _; have ht: bracket (mot i.1 (cw i.2)) (mot i.1 (ccw i.2))=wall i:= by
    have v:= sym_sr i.1 (cw i.2); rw [cw_c,ccw_c] at v; exact v
  rw [← ht,map_smul,he,smul_zero]
lemma ideals (p:C2 X) (h:Cycle S p) (v:∀ i j k,S i (p.val j k)=0): p ∈ LinearMap.range (lone S):=by
  classical
  let B (i:Tape):X:= - p.val (mot i.1 (cw i.2)) (mot i.1 (ccw i.2))
  let P : C1 X:= ∑ i:Tape, LinearMap.smulRight (point i) (B i)
  have he i:P (wall i)=B i:= by unfold P; rw [LinearMap.sum_apply]; simp [shines]
  let L:=lone S P
  have hp (d i j) : S j (P (mot d i))=0:= by rw [show mot d i=wall (d,i) from rfl,he]; unfold B; rw [map_neg,v,neg_zero]
  have hh (d i): L.val (mot d i) (mot d (cw i))=p.val (mot d i) (mot d (cw i)):= by
    unfold L; rw [turn,hp,hp,sym_sr, sub_zero, zero_sub]; rw [show P (mot d (ccw i))=B (d,ccw i) from he (d,ccw i)]
    unfold B; simp only [neg_neg,cwc, show ccw (ccw i)= cw i by fin_cases i <;> decide]
  have hC (d i j): p.val (mot d i) (mot (!d) j) =0:= by
    have ht:=h (mot d (cw i)) (mot d (ccw i)) (mot (!d) j); simp_rw [v] at ht; rw [add_zero,add_zero,away_pair,flips (mot (!d) j),away_pair,neg_zero, show bracket (mot d _) (mot d (ccw i))=mot d i by rw [← cw_c,sym_sr,ccw_c]] at ht -- check
    simpa only [map_zero,LinearMap.zero_apply,add_zero] using ht.symm
  have hO (d s : Bool) (i j:S3): L.val (mot d i) (mot s j)=p.val (mot d i) (mot s j):= by
    by_cases u:d=s
    · subst s
      by_cases v:i=j
      · rw [v,same₂,same₂]
      rcases is_p j i (Ne.symm v) with q|q
      · rw [q]; exact hh ..
      rw [swap L,swap p]; have e:= hh d j; rw [show cw j=i by rw [q,cwc]] at e; rw [e]
    have hs:s=(!d):=by cases d<;> cases s<;> first|rfl|exact (u rfl).elim
    rw [hs]; unfold L; rw [hC,turn,hp,hp,away_pair,map_zero,sub_zero,sub_zero]
  refine ⟨P,Subtype.ext ?_⟩; ext1 i; ext1 j
  rw [← Apit.repr i,← Apit.repr j]; change L.val _ _ = p.val _ _; simp_rw [map_sum,map_smul]; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]; simp_rw [wall,hO]

-- nontrivial
include P
lemma blemish (f:C1 X) (h:lone S f=0) : ∀ a, mtx S (f a)= S a (∑ i:Tape,S (wall i) (f (wall i))) := by
  intro a
  have e (v): S v (f a)= S a (f v)+f (bracket v a) := by
    have k : (lone S f).val v a=(0:X):= by rw [h]; rfl
    rw [turn] at k; rw [← sub_eq_iff_eq_add'] -- adjust via abel
    exact sub_eq_zero.mp k
  let q:= S.compl₂ f -- oll
  have ht:= series q a
  rw [jmt,map_sum]; simp_rw [e,map_add,Finset.sum_add_distrib,s_roll P _ a (f _)]; -- risk rewrite loops
  rw [Finset.sum_add_distrib,add_assoc]; rw [show (∑ i:Tape,S (bracket (wall i) a) (f (wall i))) + ∑ i:Tape,S (wall i) (f (bracket (wall i) a))=0 from ht,add_zero]

-- Cartan contraction
lemma cartan (f:C2 X) (h:Cycle S f): let w:C1 X:=∑ i:Tape,S (wall i) ∘ₗ f.val (wall i)
                                     hooked (mtx S) f = lone S w:= by
  intro w; apply Subtype.ext; ext1 a; ext1 b; rw [turn]; change mtx S (f.val a b)=S a (w b)-S b (w a)-w _
  have he x: S x (f.val a b)=S a (f.val x b)-S b (f.val x a)+f.val (bracket x a) b-f.val x (bracket a b)-f.val (bracket x b) a:= by
    have k:= h x a b; rw [swap f b, map_neg, swap f (bracket a b), flips b, map_neg,LinearMap.neg_apply] at k
    rw [add_assoc] at k; rw [eq_sub_of_add_eq k]; abel
  have hz (i:Tape) : S (wall i) (S (wall i) (f.val a b))= (S a (S (wall i) (f.val (wall i) b))+S (bracket (wall i) a) (f.val (wall i) b)) - (S b (S (wall i) (f.val (wall i) a))+ S (bracket (wall i) b) (f.val (wall i) a))+ S (wall i) (f.val (bracket (wall i) a) b) - S (wall i) (f.val (wall i) (bracket a b)) - S (wall i) (f.val (bracket (wall i) b) a) := by rw [he]; simp only [map_add,map_sub]; rw [s_roll P _ a _,s_roll P (wall i) b _]
  unfold w; rw [jmt]; simp only [LinearMap.sum_apply,map_sum, hz, Finset.sum_add_distrib, Finset.sum_sub_distrib, LinearMap.comp_apply]
  let Gt (i:G): Bile X:=(S.compl₂ (f.val.flip i))
  have gx (a b : G): (∑ i:Tape,S (bracket (wall i) a) (f.val (wall i) b))+∑ i:Tape,S (wall i) (f.val (bracket (wall i) a) b)=0:=series (Gt b) a
  rw [eq_neg_of_add_eq_zero_left (gx a b),eq_neg_of_add_eq_zero_left (gx b a)]; abel
end
end YM.GaugeFieldConstruction.Apit
