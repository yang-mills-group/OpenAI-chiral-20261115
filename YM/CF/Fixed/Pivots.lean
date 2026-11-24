import YM.Wilson.Law
import Mathlib.MeasureTheory.Integral.Marginal

/-!
Vacuum & numerator architecture for the fixed-coupling `Fixed` approach.
Pay *same* shell factors by geometric pivot trees. Span has `#N^4−1` tree
links. Upper uses triangular independent plaquette costs, **#links − #N^4 +
1 − 4** (the four generator holonomies about the origin excluded). Similar
idea to gauge-fixing count in the construction notes. Distinct here: define marks
& dependencies directly on the cubic layout, use the unsliced Haar with
measure-preserving transformations both upper and lower. Will use this for
actual cap state, at fixed x stages. Exact priority calculation, no misleading
symmetry assumptions for the gauge slice.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Pivots
open Function Filter MeasureTheory Gauge Lattice Finset
open scoped Matrix.Norms.Frobenius BigOperators Topology ENNReal InnerProductSpace
variable {N:Side}
abbrev Link (N:Side):=Edge (Site N)
abbrev originSum(x:Site N):ℕ:=∑ i:Axis,(x i).val
lemma origin_pos (e:Site N)(h:e≠0):∃ i:Axis,e i≠0 := by by_contra p; push Not at p; exact h (funext p)
lemma origin_abs (e:Site N)(h:originSum e=0): e=0:=by
  funext i; apply ZMod.val_injective; change (e i).val=ZMod.val 0; rw [ZMod.val_zero]; exact Nat.eq_zero_of_le_zero ((single_le_sum (s:=univ) (fun i _=>Nat.zero_le ((e i).val)) (mem_univ i)).trans h.le)
private lemma vals (x:Per N) : (x+1).val= if x.val+1=N.val then 0 else x.val+1 := by
  rw [ZMod.val_add,ZMod.val_one_eq_one_mod,Nat.add_mod_mod]; split_ifs with h
  · rw [h,Nat.mod_self]
  exact Nat.mod_eq_of_lt (by have h := ZMod.val_lt x; omega)
private lemma nextS (x: Site N)(i: Axis) : ((x+step i : Site N) i).val= if (x i).val+1=N.val then 0 else (x i).val+1 := by simp [vals]
private lemma prev (x : Site N)(i:Axis)(h:x i ≠0): (((x-step i) : Site N) i).val+1=(x i).val := by
  let y:=x-step i; have he:y+step i=x:=sub_add_cancel ..; have hK := nextS y i; rw [he] at hK; have hp: (x i).val≠0 := mt (ZMod.val_eq_zero (x i)).mp h; split_ifs at hK with k; exact (hp hK).elim; exact hK.symm
lemma sum_shift (x y:Site N)(i:Axis)(h:∀ k:Axis,k≠i→ y k=x k) :
    originSum x + (y i).val = originSum y+(x i).val := by
  unfold originSum; nth_rw 1 [← Finset.sum_erase_add _ _ (mem_univ i)]; nth_rw 1 [← Finset.sum_erase_add _ (fun j=> (y j).val) (mem_univ i)]
  rw [sum_congr (s₁:=univ.erase i) (f:=fun j=> (y j).val) (g:=fun j=>(x j).val) rfl (fun j hj=> by rw [h j (mem_erase.mp hj).1])]; omega
lemma reduced (x: Site N)(i:Axis)(h:x i≠0): originSum ((x-step i) : Site N) + 1 = originSum x := by have he:= sum_shift ((x-step i) : Site N) x i (fun k g=> by simp [g]); have hp:= prev x i h; omega

def Tree (a: Link N) := (a.1 a.2).val+1 < N.val ∧ ∀ k< a.2, a.1 k=0
def Gen (a: Link N) := (a.1 a.2).val+1=N.val ∧ ∀ k:Axis,k≠a.2 → a.1 k=0
def Active (a: Link N) := ¬ Tree a ∧ ¬ Gen a
instance (a:Link N): Decidable (Tree a):= by unfold Tree; infer_instance
instance (a:Link N): Decidable (Gen a):=by unfold Gen; infer_instance
instance (a:Link N): Decidable (Active a):=by unfold Active; infer_instance

/-- Counts used at the very same gauge period on both numerator and denominator computations. -/
def treeLinks(N:Side):= univ.filter (fun a:Link N=> Tree a)
def generators(N:Side):= univ.filter (fun a:Link N=> Gen a)
def pivots(N:Side):= univ.filter (fun a:Link N=> Active a)
lemma gen_disjoint: Disjoint (treeLinks N) (generators N) :=by rw [Finset.disjoint_left]; intro a t u; exact (mem_filter.mp t).2.1.ne (mem_filter.mp u).2.1
lemma all_count : (treeLinks N).card + (generators N).card + (pivots N).card = 4*N.val^4 := by
  let A:= treeLinks N ∪ generators N
  have hp:pivots N=Aᶜ:= Finset.ext fun i=>by simp [pivots,A,generators,treeLinks,Active]
  rw [← card_union_of_disjoint gen_disjoint, hp]; have he:= card_compl_add_card A
  change A.card+Aᶜ.card=_; rw [add_comm,he]; unfold Link Edge; rw [Fintype.card_prod,site_card,show Fintype.card Axis=4 from rfl,Nat.mul_comm] -- check

abbrev reach(e: Link N):=e.1+step e.2
lemma reach_tree (x:Link N)(h:Tree x) : reach x≠0:=by
  intro g; have he:ZMod.val ((reach x) x.2)=0:= g ▸ ZMod.val_zero; unfold reach at he; rw [nextS,if_neg h.1.ne] at he; omega

def starting (x:Site N):Finset Axis:= univ.filter fun i=> x i ≠0
lemma starting_nonempty (x:Site N)(h:x≠0): (starting x).Nonempty:=by obtain ⟨i,e⟩:=origin_pos x h; exact ⟨i,mem_filter.mpr ⟨mem_univ _,e⟩⟩
abbrev gapAxis (x:Site N)(h:x≠0):= (starting x).min' (starting_nonempty x h)
lemma gapAxis_nonzero (x:Site N)(h:x≠0): x (gapAxis x h) ≠0:= (mem_filter.mp (min'_mem _ (starting_nonempty x h))).2
def parentLink (x:Site N)(h:x≠0): Link N := (x-step (gapAxis x h),gapAxis x h)
lemma tree_is (x:Site N)(p:x≠0) : Tree (parentLink x p) := by
  let i:=gapAxis x p; constructor
  · rw [parentLink]; change (((x-step i) : Site N) i).val+1<N.val; rw [prev x i (gapAxis_nonzero x p)]; exact ZMod.val_lt _
  intro k h; change k < i at h; change ((x-step i) : Site N) k=0; have he:x k=0:=by by_contra g; exact h.not_ge (min'_le _ k (mem_filter.mpr ⟨mem_univ _,g⟩))
  simp [h.ne,he]
lemma origin_child (x: Site N)(h:x≠0): reach (parentLink x h)=x:=sub_add_cancel ..
lemma reach_unique (x: Link N)(h:Tree x) : gapAxis (reach x) (reach_tree x h)=x.2:=by
  let v:=reach x; have hp:x.2∈starting v:=by apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; intro g; have he: ZMod.val (v x.2)=0:=g ▸ ZMod.val_zero; unfold v reach at he; rw [nextS,if_neg h.1.ne] at he; omega
  apply le_antisymm (min'_le _ _ hp); apply le_of_not_gt; intro k; let i:=gapAxis v (reach_tree x h); exact gapAxis_nonzero v (reach_tree x h) (show v i= 0 from by change x.1 i+_=0; rw [h.2 i k,step_apply,if_neg (show i≠x.2 from k.ne),add_zero])
lemma tree_reduces (x:Link N)(h:Tree x) : parentLink (reach x) (reach_tree x h)=x:=by rw [parentLink,reach_unique x h]; unfold reach; simp

theorem tree_card : (treeLinks N).card+1=N.val^4 := by
  classical
  let S:= treeLinks N; let F:= S.image reach
  have he: F=univ.erase (0:Site N):=by
    ext x; constructor
    · intro v; obtain ⟨y,hy,rfl⟩:= mem_image.mp v; exact mem_erase.mpr ⟨reach_tree y (mem_filter.mp hy).2, mem_univ _⟩
    intro v; let T:= (mem_erase.mp v).1; exact mem_image.mpr ⟨parentLink x T, mem_filter.mpr ⟨mem_univ _,tree_is x T⟩,origin_child x T⟩
  have hv:F.card=S.card:= card_image_of_injOn (fun x hx y hy e=>by
    have hp:Tree x:=(mem_filter.mp (show x∈S from hx)).2
    have hq:Tree y:=(mem_filter.mp (show y∈S from hy)).2
    have he : ∀ (u v:Site N)(h:u=v)(p:u≠0)(q:v≠0),parentLink u p=parentLink v q:=by intro u v e k l; subst e; rfl
    exact (tree_reduces x hp).symm.trans ((he _ _ e _ _).trans (tree_reduces y hq)))
  change S.card+1=_; rw [←hv,he,card_erase_add_one (mem_univ (0:Site N)),card_univ, site_card]
lemma pin_le : (generators N).card ≤ 4:=by
  -- at most generator holonomy count enough
  let S:= generators N; change S.card≤_; rw [← Finset.card_image_of_injOn (f:=Prod.snd) (s:=S) ?_]; swap
  · intro x hx y hy e; have h:Gen x:= (mem_filter.mp (show x∈S from hx)).2; have p:Gen y:= (mem_filter.mp (show y∈S from hy)).2; apply Prod.ext _ e; funext i; by_cases hi:i=x.2
    · have hv: ZMod.val (x.1 i)+1=N.val := hi.symm ▸ h.1; have hy:ZMod.val (y.1 i)+1=N.val:= (hi.trans e).symm ▸ p.1; exact ZMod.val_injective _ (by omega)
    rw [h.2 i hi,p.2 i (by rw [←e]; exact hi)]
  exact card_le_card (subset_univ _)
def aims (e:Link N): Finset Axis:= (starting e.1).erase e.2
lemma aims_nonempty (e:Link N)(h:Active e): (aims e).Nonempty:=by
  by_contra p
  have he(k:Axis)(g:k≠e.2):e.1 k=0:=by by_contra hh; exact p ⟨k,mem_erase.mpr ⟨g,mem_filter.mpr ⟨mem_univ _,hh⟩⟩⟩
  have hu:= h.1; by_cases g:(e.1 e.2).val+1=N.val; · exact h.2 ⟨g,he⟩
  exact h.1 ⟨by have hh:=ZMod.val_lt (e.1 e.2); omega,fun i p=> he i p.ne⟩
def tooth(e:Link N)(h:Active e):Axis:= (aims e).min' (aims_nonempty e h)
lemma tooth_spec (e:Link N)(h:Active e): tooth e h≠e.2 ∧ e.1 (tooth e h) ≠ 0∧∀ j:Axis,j≠e.2 → e.1 j≠0→ tooth e h ≤ j:=by
  obtain ⟨A,B⟩:= (mem_erase.mp (min'_mem _ (aims_nonempty e h))); exact ⟨A,(mem_filter.mp B).2,fun i p t=>min'_le _ i (mem_erase.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,t⟩⟩)⟩

def mark (e:Link N)(h:Active e) : Face (Per N):= (e.1-step (tooth e h),PlaqAxes.ordered e.2 (tooth e h) (tooth_spec e h).1.symm)
-- actual walk from Face p.1. Accounting orientation. Exempt by membership in pivot.
def window (x:Site N)(a b:Axis) : Finset (Link N):= {(x,a),(x+step a,b),(x+step b,a),(x,b)}
abbrev support (V:Face (Per N)):= window (N:=N) V.1 V.2.val.1 V.2.val.2
lemma mark_window (x: Site N)(i:Axis)(h: Active (x,i)): let k:=tooth (x,i) h
    support (mark (x,i) h)=window (x-step k) i k:=by
  intro k
  unfold support mark PlaqAxes.ordered; change window (x-step k) (min i k) (max i k)=_; rcases le_total i k with h|h
  · rw [min_eq_left h,max_eq_right h]
  rw [min_eq_right h,max_eq_left h]; ext x; simp only [window,mem_insert,mem_singleton]; tauto
lemma mark_roll (x: Link N)(h:Active x): x ∈ support (mark x h):=by
  rcases x with ⟨x,i⟩; rw [mark_window x i h]; simp [window]
lemma behind (e:Link N)(h:Active e)(p:Link N)(g: Active p)(x:p∈ support (mark e h))(he:p≠e) :
    originSum p.1 < originSum e.1 := by
  rcases e with ⟨x',i⟩; let k:=tooth (x',i) h; let y:= x'-step k; let z:=y+step i; have ht: y+step k=x':=sub_add_cancel ..
  rw [mark_window x' i h] at x; change p∈ window y i k at x; simp only [window,mem_insert,mem_singleton] at x; obtain ⟨a,H,L⟩:= tooth_spec _ h
  have hr :=reduced x' k H; have hp: originSum y< originSum x':= Nat.lt_of_succ_le hr.le
  rcases x with u|u|u|u
  · rw [u]; exact hp
  · rw [u]; change originSum z < originSum x'; rcases lt_or_gt_of_ne (show k≠i from a) with v|v
    · exfalso
      apply g.1; rw [u]; constructor
      · change (z k).val+1<N.val; have hu:z k=y k:=by simp [z,v.ne]
        rw [hu]; exact (prev x' k H).trans_lt (ZMod.val_lt _)
      intro l hl; change l<k at hl; change z l=0
      have ht:x' l=0:=by by_contra w; exact hl.not_ge (L l (hl.trans v).ne w)
      simp [z,y,hl.ne,(hl.trans v).ne,ht]
    have hy:(x' i).val+1=N.val:=by
      by_contra w
      exact h.1 ⟨by have he:= ZMod.val_lt (x' i); change (x' i).val+1 <N.val; omega,fun j hj=>by change j< i at hj; change x' j=0; by_contra q; exact (hj.trans v).not_ge (L j hj.ne q)⟩
    apply lt_of_le_of_lt _ hp
    have hu:(z i).val=0:=by change ((y+step i : Site N) i).val=0; rw [nextS y i,if_pos]; simpa [y,v.ne] using hy
    have he:= sum_shift z y i (fun l hl=> by simp [z,hl]); omega
  · rw [ht] at u; exact (he u).elim
  rw [u]; exact hp
lemma mark_inj (x y:Link N)(p:Active x)(q:Active y)(u:mark x p=mark y q):x=y:=by
  by_contra k; have ht:= behind x p y q (u.symm ▸ mark_roll y q) (Ne.symm k); exact ht.not_gt (behind y q x p (u ▸ mark_roll x p) k)

variable (G:Gauge)
open Wilson
lemma square_formula(x:Site N)(U:Config G N)(a b:Axis):
    travel U x (square a b)= U (x,a)*U (x+step a,b)*(U (x+step b,a))⁻¹*(U (x,b))⁻¹:=by
  simp only [travel,square,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one,mul_assoc]; rw [show x+step a+step b-step a=x+step b by abel,show x+step a+step b+ -step a-step b=x by abel]
lemma face_unique (U V:Config G N)(f:Face (Per N))(e:∀ i∈ support f,U i=V i): faceValue U f=faceValue V f := by
  rcases f with ⟨x,⟨⟨a,b⟩,u⟩⟩; unfold faceValue; dsimp only; rw [square_formula,square_formula, e (x,a) (by simp [support,window]), e (x+step a,b) (by simp [support,window]), e (x+step b,a) (by simp [support,window]),e (x,b) (by simp [support,window])]
end YM.CF.Fixed.Pivots
