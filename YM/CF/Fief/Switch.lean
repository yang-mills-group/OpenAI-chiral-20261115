import YM.CF.Fief.Ling
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{k n j d:ℕ}
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(n)
variable {C a b c g:ℝ}
variable {o:Site (Domain N B)}{w:LinkS S k}{b:ℕ}
local notation "m"=> Domain N B
local notation "b₀'"=>radiusB x
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare Order Relation
def pathPay (lX:ℕ):ℕ:= ((lX+66)+(lX+66)+1)^4
open Corona
lemma closedB (hp:0 < b₀')(h:w∈finW o S x k): coverNumber b₀' (Lich.Muster.badge A w).val ≤ (k+2)*pathPay A.post:=by
 let f(i: Fin (k+2)):=S.ratio.parent (w i).1; let N':=univ.image f; let R:=(A.post+65)*b₀'; have he:N'.card ≤ k+2:= card_image_le.trans (by simp)
 apply le_trans _ (Nat.mul_le_mul_right (pathPay A.post) he)
 apply tiling hp («m»:=A.post+65); refine ⟨?_,Corona.ship_halo ((A.post+65)*b₀') ?_⟩
 · intro i p; obtain ⟨jX,u,X⟩:= mem_biUnion.mp p; obtain ⟨t,v,z⟩:= halo_spec.mp X; rw [mem_singleton.mp v] at z; exact halo_spec.mpr ⟨_,mem_image_of_mem f u,z⟩
 have ht (i:Fin (k+2)): Relation.ReflTransGen (Touch N' (R+R+1)) (f 0) (f i):=by
    induction i using Fin.induction with
    | zero=> exact .refl
    | succ jX ih=> refine ih.tail ⟨mem_image_of_mem f (mem_univ _),mem_image_of_mem f (mem_univ _),?_⟩; exact ((mem_filter.mp h).2.2.2 jX _ (Set.mem_insert ..) _ (Set.mem_insert ..)).trans (by unfold R; simp only [Nat.add_mul]; omega) -- tune
 intro i p u v; obtain ⟨i,p,rfl⟩:=mem_image.mp p; obtain ⟨u,v,rfl⟩:=mem_image.mp v; exact (Corona.sym (ht i)).trans (ht u)
def diameterW (lX k B:ℕ):ℕ:= 3*k*B+(lX+70)*B
lemma steps_l (hp:0<b₀')(h:w∈finW o S x k) : (Lich.Muster.badge A w).val ⊆ halo (diameterW A.post k (radiusB x)) {o}:=by
 intro i p; obtain ⟨jX,u,t⟩:=mem_biUnion.mp p; obtain ⟨s,z,v⟩:=halo_spec.mp t; rw [mem_singleton.mp z] at v
 obtain ⟨t,h,w⟩:= (mem_filter.mp h).2; have hh:= latticeFieldEstimatesC ⟨h,w⟩ t jX; refine halo_spec.mpr ⟨_,mem_singleton_self _, (separation_triangle _ _ _).trans (Nat.add_le_add hh v |>.trans ?_)⟩; have ht: jX.val≤ k+1:=by omega
 have he:= Nat.mul_le_mul_right (3*radiusB x) ht; unfold diameterW; rw [Nat.add_mul,one_mul] at he; rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm 3 k, Nat.mul_assoc]; omega
section hit
open Rel
variable {i:Site (Domain N B)}
def tallyL (u:Site m)(L:Palot.leaf (Site m))(σ':ℝ)(B':ℕ):ℝ := if u∈L.val then Real.exp (σ'*coverNumber B' L.val) else 0
def tapeQ(lX n:ℕ)(σ:ℝ):= Real.exp (σ*pathPay lX)^(n+2)
def barkQ(lX k B:ℕ):ℕ:=(diameterW lX k B+diameterW lX k B+1)^4
variable {b':ℝ}
lemma driftX(u:ℝ)(z:Site (Domain N B)) : (∑ iX:Palot.leaf (Site m), tallyL z iX u b₀'*note_g n A C a b' c iX k)=∑ j':Site (Domain N B),∑ w'∈finW j' S x k,tallyL z (Lich.Muster.badge A w') u b₀'*fareI C a b' c x n k:=by
 unfold note_g; simp_rw [mul_sum,sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro o t; rw [sum_comm]; apply sum_congr rfl; intro p v; simp
lemma debt_p {u:ℝ}(p:0 ≤ u)(z:Site (Domain N B)) {w:LinkS S k}(hx:w∈finW o S x k)(hP:0<b₀') : tallyL z (Lich.Muster.badge A w) u b₀' ≤ tapeQ A.post k u:=by
 unfold tallyL tapeQ; split; swap; positivity
 rw [←Real.exp_nat_mul,mul_comm]; apply Real.exp_le_exp.mpr; apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (closedB A hP hx)) p); push_cast; exact le_of_eq (by ring)
def tribute (B':ℕ)(a b c d:ℝ)(n:ℕ)(lX:ℕ)(q:ℕ)(L:ℕ)(D:ℝ)(x:ℝ) := (barkQ lX q L:ℝ)* ((ratioB S 1*(ratioB S B')^(q+1):ℕ):ℝ)*tapeQ lX q D *fareI a b c d x n q
lemma rapid (p:0≤ C)(h:0≤b')(u:0≤c)(hK:0<b₀')(σ':ℝ)(g:0≤σ') (z:Site (Domain N B))(k:ℕ): (∑ iX:Palot.leaf (Site m), tallyL z iX σ' b₀'*note_g n A C a b' c iX k) ≤ tribute (S:=S) (3*b₀') C a b' c n A.post k b₀' σ' x:=by
 rw [driftX]; let L:=diameterW A.post k (radiusB x); let S':=halo L ({z}:Support m); let γ':=fareI C a b' c x n k
 let F(j':Site m)(w:LinkS S k):= tallyL z (Lich.Muster.badge A w) σ' b₀'*γ'; let P'(j':Site m):=∑ w'∈finW j' S x k,F j' w'; have he(j':Site m)(t:j'∉ S'):P' j'=0:=sum_eq_zero fun w v=>by
    unfold F tallyL; split
    next hx=> obtain ⟨kX,u,g⟩:=halo_spec.mp (steps_l A hK v hx); rw [mem_singleton.mp u] at g; exact (t (halo_spec.mpr ⟨z,mem_singleton_self _,(separation_comm ..).trans_le g⟩)).elim
    rw [zero_mul]
 have hz:=sum_subset (f:=P') (subset_univ S') (fun i _=> he i); change ∑ i:Site m,P' i ≤ _; rw [←hz]
 let X:=tapeQ A.post k σ'; have ht:0 ≤X:=by unfold X tapeQ; positivity
 have hp:0 ≤ γ':=by unfold γ' fareI Lich.Muster.quota tipPay; positivity
 let Y:= ratioB S 1*(ratioB S (3*radiusB x))^(k+1); let K:= (Y:ℝ)*(X*γ'); have hi(jX):P' jX ≤ K := by
    refine le_trans (sum_le_sum (fun w v=> mul_le_mul_of_nonneg_right (debt_p A g z v hK) hp)) ?_; rw [sum_const, nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hearty jX k)) (mul_nonneg ht hp)
 refine (sum_le_sum (fun i _=> hi i)).trans ?_; rw [sum_const,nsmul_eq_mul]; refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show S'.card≤ barkQ A.post k (radiusB x) from ?_)) (by unfold K; positivity)) (le_of_eq ?_)
 · exact (Corona.halo_size {z} L).trans (by unfold S' L barkQ at *; simp)
 unfold K tribute X γ' Y; ring
end hit
end YM.CF.Fief
