import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.Push.ABSOLUTE_SUMS.Animals
import YM.Corona.Fit
import YM.Corona.Halo
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5800
set_option maxHeartbeats 220000
noncomputable section
namespace YM.Lattice.Corona.Hive
open Function Filter MeasureTheory NormedSpace Finset
open scoped Topology BigOperators Classical
variable {n:Side} (B:ℕ)(η a:ℝ)(L:List (Site n)) (o:Site n)(A:Support n) {X Y:Support n}
abbrev ζd:ℝ:=1/1024
lemma ζdp :0< ζd:=by norm_num [ζd]
def yard_M(B:ℕ):ℕ:=50000*(B+1)
abbrev yardZ(B:ℕ):ℝ:= (2*(16*((yard_M B:ℕ):ℝ)+9))^4
def windPulse (y:Site n) :ℝ:=Real.exp (-((separation o y:ℕ):ℝ)/(4*(yard_M B:ℝ)+2)) -- cast
local notation "θ"=> windPulse B
lemma pulse_pos (x:Site n):0< θ o x:=Real.exp_pos _
lemma pulse_world : ∑ a:Site n,θ a o ≤ yardZ B:= Extra.Multi.torus_kernel o

def cubeCt(B:ℕ):ℝ:=(B+B+1:ℕ)^ (4:ℕ) -- check cast maybe ℝ expected. simp
abbrev Cube_M(B:ℕ):ℝ:=cubeCt B/ζd
def heft :ℝ:=coverNumber B A
local notation "K"=> heft B
lemma heft_card : (A.card:ℝ)≤cubeCt B * K A:=by
 unfold cubeCt heft; rw[mul_comm]; exact_mod_cast pays A B
abbrev ridg :ℝ:=Real.exp (ζd*K A)
lemma ridg_pos:0 < ridg B A:=Real.exp_pos _
lemma ridg_one:1≤ ridg B A:=Real.one_le_exp (mul_nonneg ζdp.le (Nat.cast_nonneg _))
lemma cube_M_pos: 0<Cube_M B:=div_pos (by unfold cubeCt; positivity) ζdp
lemma hefty : (A.card:ℝ)≤ Cube_M B * ridg B A:=by
 have h:ζd*K A≤ ridg B A:=le_trans (le_add_of_nonneg_right (by norm_num:0≤(1:ℝ))) (Real.add_one_le_exp _)
 refine (heft_card B A).trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h (cube_M_pos B).le))
 unfold Cube_M; field_simp
lemma pulse_core {x:Site n}(p:o∈A)(u:x∈A):1≤ windPulse B o x * ridg B A:=by
 unfold windPulse ridg; rw[←Real.exp_add]
 have hc:0<coverNumber B A:=(Push.AbsoluteSums.Animals.price_pos ..).2 ⟨o,p⟩
 let y:= K A; have he:(1:ℝ)≤ y:=by unfold y heft; exact_mod_cast (show 1≤ _ from hc)
 have hv: (separation o x:ℝ) ≤ y*(4*(B:ℝ)+2)+2*B:=by unfold y heft; exact_mod_cast extent A B p u
 have h:((separation o x:ℕ):ℝ)/(4*(yard_M B:ℝ)+2) ≤ ζd*y:=by
    apply (div_le_iff₀ (by positivity)).2
    apply hv.trans; unfold yard_M ζd; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) B]
 apply Real.one_le_exp; rw [neg_div]; linarith

def cum:= ∑ y∈A,θ o y
def Bonus:= η*(L.map fun i=>cum B i A).sum
local notation "ibo"=> Bonus B η
lemma cum_pos:0 ≤ cum B o A:=sum_nonneg (fun _ _=>(pulse_pos ..).le)
lemma cum_union :cum B o (X∪Y) ≤ cum B o X+cum B o Y:=by
 have ht:cum B o (X∪Y)=cum B o X+ cum B o (Y\X):=by
    unfold cum; rw[←sum_union (s₂:=Y\X) (disjoint_left.mpr (fun {i} p h=> (mem_sdiff.mp h).2 p))]; congr 1; exact (union_sdiff_self_eq_union ..).symm -- tune
 refine ht.trans_le (add_le_add_right ?_ _); exact Finset.sum_le_sum_of_subset_of_nonneg sdiff_subset fun i _ _=>(pulse_pos ..).le
lemma Bonus_nil:ibo [] A=0:=by simp [Bonus]
lemma Bonus_more: ibo (o::L) A=η*cum B o A+ibo L A:=by unfold Bonus; rw[List.map_cons,List.sum_cons,mul_add]
lemma Bonus_gene (h:0≤η):0≤ ibo L A:=by
 induction L with
 | nil=> rw[Bonus_nil]
 | cons i L ih=>rw[Bonus_more]; exact add_nonneg (mul_nonneg h (cum_pos ..)) ih
lemma Bonus_adv (h:0≤η): ibo L X+ibo L Y ≥ ibo L (X∪Y):=by
 induction L with
 | nil=> simp [Bonus]
 | cons i L ih=>rw[Bonus_more,Bonus_more,Bonus_more]; exact ((add_le_add ((mul_le_mul_of_nonneg_left (cum_union B i) h).trans_eq (mul_add ..)) ih)).trans_eq (by ring)
def crewFlow(B:ℕ)(L:List (Site n))(u:ℝ):Prop:=∀ y:Site n,(L.map (fun i=> windPulse B i y)).sum≤ u
lemma asset (v:ℝ)(l:crewFlow B L v) (h:0≤η)(p:0≤v)(q:η*(v*cubeCt B) ≤ ζd): ibo L A≤ζd*K A:=by
 unfold Bonus
 have he (L : List (Site n)):(L.map (fun i=>cum B i A)).sum=∑ i∈A,(L.map (fun j=> θ j i)).sum:=by
    induction L with
    | nil=> simp
    | cons t L ih=> simp only [List.map_cons,List.sum_cons,sum_add_distrib]; rw[ih]; rfl
 rw [he]; refine le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (fun i (_:i∈A)=> l i)) h) ?_
 rw[sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (heft_card B A) p) h)
 nlinarith only[mul_le_mul_of_nonneg_right q (show 0 ≤ K A from Nat.cast_nonneg _)]
-- flow via sparse map
variable {I:Type} (σ:I→Site n)
lemma crew_at (L:List I)(p:L.Nodup){k:ℕ}(v: ∀ x,(L.toFinset.filter fun i=>σ i=x).card ≤ k): crewFlow B (L.map σ) ((k:ℝ)*yardZ B):=by
 intro i; rw[List.map_map]; calc
  _ = ∑ j∈L.toFinset,θ (σ j) i:=by
    clear v; induction L with
    | nil=> simp
    | cons a L ih=> obtain ⟨p,t⟩:=List.nodup_cons.mp p; simp only [List.map_cons,Function.comp_apply,List.toFinset_cons,List.sum_cons,sum_insert (mt List.mem_toFinset.mp p),ih t]
  _ = ∑ x:Site n,∑ j∈L.toFinset.filter (fun j=>σ j=x),θ x i:=by
    simp_rw[sum_filter]; rw[sum_comm]; refine Finset.sum_congr rfl fun j _=>?_ ; symm; rw[sum_eq_single (σ j)]; simp; intro x hx u; rw[if_neg u.symm]; simp
  _ ≤ ∑ x:Site n,(k:ℝ)* θ x i:=Finset.sum_le_sum (fun a _=>by rw[sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (v _)) (pulse_pos ..|>.le))
  _ ≤ _ :=by rw [←mul_sum]; gcongr; exact pulse_world B i
end YM.Lattice.Corona.Hive
end
