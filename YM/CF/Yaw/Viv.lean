/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Yaw.Trust
import YM.Corona.Spend
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
open Scion PetalP RG Push.AbsoluteSums.Trees
open scoped Classical
open Corona
variable {n m:Side}{U:Support n}{D c a:ℝ} {s B k:ℕ}
abbrev χ (s:ℕ):ℕ:=((s+6)+(s+6)+1)^4
lemma fingers(q:Ratio m n)(h:Grove (terr _) U)(t:k ≤ s*B)(b:0<B): q.count.val*B*coverNumber B (halo k (U.image q.parent)) ≤ (2*U.card + q.count.val*B)*χ s:=by
 obtain ⟨N,l,Z,x,hN⟩:= ring_path 1 (D:=U) (rooted h); obtain ⟨X,h,hp,f⟩:= fuel q Z N x B b; let Y:= U.image q.parent; have hx: covers ((s+5)*B) (halo k Y) X:= by
    refine ⟨fun i v=>?_,ship_halo _ fun i p j u=>?_⟩
    · obtain ⟨j,x,q'⟩:=halo_spec.mp v; obtain ⟨w,l',rfl⟩:=mem_image.mp x; obtain ⟨r,v,t'⟩:=hN w l'; obtain ⟨j,p,v'⟩:=halo_spec.mp (f r v); rw [t'] at v'; apply halo_spec.mpr ⟨_,p,(separation_triangle ..).trans (show separation j (q.parent w)+separation _ i ≤_ from ?_)⟩; simp_rw [Nat.add_mul]; omega
    exact ReflTransGen.mono (fun x y (e : Touch X (2*B) x y)=> ⟨e.1,e.2.1,(e.2.2.trans (by simp only [Nat.add_mul]; omega)) ⟩) _ _ (h i p j u)
 refine (Nat.mul_le_mul_left _ (tiling b hx)).trans ?_; rw [←Nat.mul_assoc]; have hx := hx
 have hT : N ≤ 2*U.card:=by omega
 exact Nat.mul_le_mul_right _ (hp.trans (Nat.add_le_add_right hT _))
local notation "cost'"=>Push.AbsoluteSums.Trees.currency
lemma aidV(q:Ratio m n)(h:Grove (terr _) U)(t:k ≤ s*B)(b:0<B)(p:0≤a)(f:a*2*χ s≤ (B:ℝ)*D)(g:0≤D): cost' B a (halo k (U.image q.parent)) ≤ Real.exp (a*χ s)*Branch.rent D U:=by
 unfold Push.AbsoluteSums.Trees.currency Branch.rent; rw [← Real.exp_add]; apply Real.exp_monotone
 let V:=coverNumber B (halo k (U.image q.parent)); let L:ℕ:= q.count.val; have hp:1 ≤ L:=q.count.property; let M:ℕ:=L*B
 have hp':(1:ℝ)≤L:=by exact_mod_cast hp
 have hz :0<(M:ℝ):=by have hu:0<M:=Nat.mul_pos hp b; positivity
 have hs: (M:ℝ)*V≤ (2*U.card+M:ℝ)*χ s:=by exact_mod_cast fingers q h t b
 apply le_of_mul_le_mul_left (a:=(M:ℝ)) _ hz; change (M:ℝ)*(a*V) ≤ (M:ℝ)*(a* (χ s:ℝ)+D*(U.card:ℝ)); rw [mul_left_comm (M:ℝ)]
 refine (mul_le_mul_of_nonneg_left hs p).trans ?_; have hw : a*2*χ s≤ M*D:=f.trans (mul_le_mul_of_nonneg_right (show (B:ℝ)≤ M by unfold M; push_cast; exact le_mul_of_one_le_left (by positivity) hp') g); linarith only [mul_le_mul_of_nonneg_right hw (show 0 ≤ (U.card:ℝ) from by positivity)] -- nonlinear normalize
-- trivial currency of bottom; used many times high degree
lemma blank_z(n:Side)(B:ℕ)(a:ℝ): cost' B a (∅: Support n)=1:=by
 have hv: halo (n:=n) B ∅=∅:=by ext; simp [halo_spec]
 have ht:coverNumber B (∅:Support n) ≤0 := list_cost B (D:=∅) (X:=∅) (by unfold Lattice.covers; simp [hv]); simp [Push.AbsoluteSums.Trees.currency,show coverNumber B (∅:Support n)=0 from Nat.eq_zero_of_le_zero ht]
end YM.CF.Yaw
