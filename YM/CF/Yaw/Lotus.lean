import YM.Push.ABSOLUTE_SUMS.Footprint
import YM.CF.Yaw.Trust
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP Push.AbsoluteSums Push.AbsoluteSums.Trees Push.AbsoluteSums.Footprint RG
open scoped Classical
variable {ι:Type}[Fintype ι][DecidableEq ι]{V:Side}
local notation "H_"=> Stilo.Harper (Site V)
local notation "bay"=>Stilo.bay
local notation "ζ_"=>Push.AbsoluteSums.Trees.currency
variable (X:ι→leaf (Site V))(R:ι→Track (Stilo.Harper (Site V)) ℝ)(C:ι→ℝ)(Z:ι→ Site V)
variable {A a d γ u Δ ε:ℝ}{B:ℕ}
-- only output leaves extending mandatory. zero unmatched
abbrev Se(ι:Type)(V:Side):= ι × leaf (Site V)
def tongue (q:Se ι V):Support V:=q.2.val ∪ (X q.1).val
def runH(q:Se ι V):= R q.1 (beamH q.2.val)
variable (p:∀ i,Strung (X i).val (R i) B A (C i))(h:∀ i,Z i∈ (X i).val)
local notation "ιT"=> Se ι V
include p
lemma spring_v:tea Prod.fst (tongue X) (runH R)=R:=by
 funext i j; unfold runH tea; rw [sum_filter, Fintype.sum_prod_type,sum_eq_single i]; swap; · intro y _ k; simp [k]
 have hp(h:H_):R i h≠0→ h=beamH (bay h):=fun v=> ((p i).spear _ v).2
 have ht (Y:leaf (Site V))(g:R i (beamH Y.val)≠0): tongue X (i,Y)=Y.val:= by unfold tongue; dsimp only; refine union_eq_left.mpr ?_; have hx:= ((p i).spear _ g).1; rwa [bay_beam] at hx
 · simp only [Finset.sum_apply,Pi.single_apply]; by_cases u:j=beamH (bay j) ∧ (bay j).Nonempty
   · let V':leaf (Site V):= ⟨bay j,u.2⟩; rw [Finset.sum_eq_single V']; swap
     · intro b h v; simp only [if_true, Pi.single_apply]; by_cases k:R i (beamH b.val)=0; · simp [k]
       rw [ht _ k]; by_contra w; apply v; split at w; next h => apply Subtype.ext; change b.val=bay j; rw [h,bay_beam]
       contradiction
     · simp only [if_true,Pi.single_apply]; by_cases h:R i j=0
       · rw [show beamH V'.val=j from u.1.symm,h]; split<;>rfl
       rw [ht V' (by rwa [show beamH V'.val=j from u.1.symm]),show beamH V'.val=j from u.1.symm,if_pos rfl]
     simp
   have h:R i j=0:=by by_contra g; exact u ⟨hp _ g,(X i).property.mono ((p i).spear _ g).1⟩
   rw [h]; apply sum_eq_zero; intro i' _; simp only [if_true]; by_cases h:R i (beamH i'.val)=0; · simp [h]
   rw [ht i' h,Pi.single_apply,if_neg]; intro k; rw [k,bay_beam] at u; exact u ⟨rfl,i'.property⟩
 simp
lemma pays_l(i): stampQ V B A (R i)= ∑ j:leaf (Site V),currency B A (tongue X (i,j)) * R i (beamH j.val):=by
 nth_rw 1 [←spring_v X R C p]; unfold tea; rw [sum_filter,Fintype.sum_prod_type,sum_eq_single i]; swap; · intro b _ v; simp [v]
 · simp only [ite_true,map_sum]; simp_rw [bloom_s, bay_beam]; rfl
 simp
include h
lemma pound(hp:∀ x, (∑ i:ι with Z i=x,C i) ≤ γ)(v:0≤ a)(g:reserve A a 1 ε) : Ac.Hit (tongue X) B (runH R) a (payment 1 (6*(B+1)) 0 ε 1 γ a 0):=by
 let f(i: Se ι V):=Z i.1; let b(i:Se ι V):=coverNumber B (tongue X i); have hx :∀ (i:Se ι V),0≤runH R i:= fun i=> (p i.1).hand _
 refine assigned id 1 ?_ f (runH R) hx b _ ?_ _ _ _ ?_ ?_ zero_le_one g _ hx ?_
 · intro Y; simp [id]
 · intro x; let V':= fun i:ιT=> if f i=x then runH R i *Real.exp (A*b i) else 0
   apply budget_of_sum; · intro i; split_ifs; exact mul_nonneg (hx _) (Real.exp_pos _).le; exact le_rfl
   intro s; change (∑ i∈ s,V' i)≤γ; apply le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intro i f g; unfold V'; split; exact mul_nonneg (hx _) (Real.exp_pos _).le; exact le_rfl))
   change (∑ i:ι×leaf (Site V),V' i) ≤ γ; rw [Fintype.sum_prod_type]; apply le_trans _ (hp x); rw [sum_filter]; apply sum_le_sum; intro i _; by_cases g:Z i=x; swap; · unfold V' f; simp only [if_neg g,sum_const_zero]; exact le_rfl
   rw [if_pos g]; apply le_trans _ (p i).pay; rw [pays_l X R C p]; exact sum_le_sum fun j _=>by unfold V' f; rw [if_pos g,mul_comm]; exact le_rfl
 · intro i x u; have hp:= Corona.extent (tongue X i) B u (show f i∈ tongue X i from mem_union_right _ (h i.1)); apply hp.trans; unfold b; nlinarith
 · intro i; unfold b; simp
 intro i; simp
variable {m:ℕ} {Q:Finset ι→ Track (Harper (Site V)) ℝ}{L:Finset ι→ List ι} (r:∀ i, (L i).toFinset=i)(hr:∀ i,(L i).Nodup)
include r hr
lemma power_v(hp:∀ x, (∑ i:ι with Z i=x,C i)≤ γ)(v:0≤a)(b:0<d)(g:reserve A (a+d) 1 ε) (hv:payment 1 (6*(B+1)) 0 ε 1 γ (a+d) 0 ≤ u)(he:0<u)(hy:degreePrice B u d≤Δ)(h':Δ < 1)(x:Site V)(hp':∀ i,Q i ≤ payH R (L i)):(∑ i:Finset ι with Palot.outC m i, invoiceB B a x (Q i))≤ u*Δ^m*(1-Δ)⁻¹:=by
 have ht:= pound X R C Z p h hp (a:=a+d) (add_nonneg v b.le) g; have hx:Ready (tongue X) B (runH R) a u d Δ:=⟨he,b,hy,h',fun i=>(p i.1).hand _,fun x=>budget_loosen (ht x) hv⟩; apply le_trans _ (awaken (@Prod.fst ι (leaf (Site V))) (tongue X) (runH R) (fun i=>i.2.property.mono subset_union_left) B a u d Δ v hx m x); apply sum_le_sum; intro i _; let G:=hp' i; nth_rw 1 [←spring_v X R C p] at G; rw [erupt _ _ _ _ (hr i),r] at G
 apply sum_le_sum; intro j p; split; exact mul_le_mul_of_nonneg_right (G _) (Real.exp_pos _).le; exact le_rfl
end YM.CF.Yaw
