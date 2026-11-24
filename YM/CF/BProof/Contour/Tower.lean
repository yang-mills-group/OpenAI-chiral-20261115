import YM.CF.BProof.Contour.Diet
import YM.CF.BProof.Prox.Base

/- Anisotropic core Λ. exactly components with r inflated, captured by overlap. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour.Tower
open Function Filter Moment RG MeasureTheory Finset Relation Push.AbsoluteSums Lattice Grid
open scoped Topology BigOperators Classical ENNReal
variable {n:ℕ}(s:Fin n→Side)(r:ℕ)
local notation "B"=> Grid.Vertex s
def porch(x:B):=Grid.collar ({x}:Sites s) r
lemma porch_m(x y:B): y∈ porch s r x ↔ Grid.dist x y≤ r:=by simp [porch,Grid.dist_symm x]
lemma porch_hit(x y:B) : meets (porch s r) y (porch s r x) ↔ Grid.dist x y≤2*r:=by
 constructor; rintro ⟨z,v,p⟩; apply (Grid.triangle x z y).trans; rw [Grid.dist_symm z y,two_mul]; exact Nat.add_le_add ((porch_m s r ..).1 v) ((porch_m s r ..).1 p) -- tune dots
 intro t; refine ⟨run x y r,(porch_m s r ..).2 ?_,(porch_m s r ..).2 ?_⟩; · simpa using Grid.run_step x y (Nat.zero_le r)
 refine (Grid.dist_symm y _).trans_le ?_; have ht:= Grid.run_step x y (show r≤2*r from by omega); rw [Grid.run_stop x y t] at ht; omega
abbrev CoreX:= Toy (porch s r)
abbrev Comps:=Finset (CoreX s r)
abbrev Exc:= Sites s
def plan : GeomT B (CoreX s r) := ⟨Subtype.val,roofT (porch s r),fun q i h=> hull_sub (porch s r) _ _ h ((porch_m s r i i).2 (by simp)),fun i=> i.property.1⟩
abbrev Contact := toTrain (porch s r)
lemma roads(Q:Sites s)(x y:B) : chain (porch s r) Q x y↔ Grid.PathIn Q (2*r) x y:=by
 unfold chain PathIn bonds EdgeIn; simp_rw [porch_hit]
lemma actual(Q:Sites s): Spark (porch s r) Q ↔ Q.Nonempty∧ Grid.Conn Q (2*r):=by simp_rw [Spark, Grid.Conn, roads]
lemma coveredT(Q:Exc s) : hull (porch s r) Q= Grid.collar Q r:=by ext i; simp only [hull,mem_biUnion,Grid.collar_mem,porch_m, Grid.dist_symm i] -- tune direction
lemma whole(i:CoreX s r): (plan s r).T i= Grid.collar i.val r:= coveredT s r i.val
lemma connected(Q:CoreX s r) : Grid.Conn ((plan s r).T Q) 1:=by
 intro i hi j hj; obtain ⟨x,h,v⟩:= mem_biUnion.mp hi; obtain ⟨y,k,g⟩:=mem_biUnion.mp hj; let B':= (plan s r).T Q; let X:=porch s r; have hx(x:B)(t:x∈ Q.val){u p:B}(g:u∈ X x)(h:p∈ X x): Grid.PathIn B' 1 u p:= Grid.path_mono (hull_sub _ _ x t) le_rfl (Prox.collar_solid r x _ g _ h) -- tune hull metavars
 have hw(y:B)(s': chain X Q.val x y): ∀ j∈ X y, Grid.PathIn B' 1 i j:=by
    induction s' with
    | refl=> exact fun j g=> hx x h v g
    | @tail y z _ hp ih=> obtain ⟨u,p,w,f,e⟩:=hp; exact fun j g=> (ih w f).trans (hx z p e g)
 exact hw y (Q.property.2 _ h _ k) j g
lemma coverE(P:Exc s): hull (plan s r).S (Contact s r P)=P:=ebb_flow (porch s r) P
lemma cover_m(Q:Comps s r)(q:flock (plan s r).T Q): Contact s r (hull (plan s r).S Q)=Q:= pact (porch s r) Q q
lemma orbitF(P:Exc s): flock (plan s r).T (Contact s r P):= creek (porch s r) P
lemma account(P:Exc s)(Q:CoreX s r): Q∈Contact s r P↔ Q.val∈Parts (porch s r) P:=by simp [Contact,toTrain]
section
variable {J: Type*} {X:Vertex s→Type*} [∀ i,MeasurableSpace (X i)] [∀ i,Nonempty (X i)] [Fintype J][DecidableEq J]
variable (P:Pot X) (C:Course P (plan s r))(R:Spice X (plan s r) J)
def landing : ℂ:= ∑ i:Exc s,∫ x,tunic P C R (Contact s r i) x ∂πμ X P.μ P.ν i
lemma contourT: landing s r P C R= contour P C R:=by
 apply sum_nbij' (Contact s r) (hull (plan s r).S); intro i _; exact mem_filter.mpr ⟨mem_univ _,orbitF ..⟩
 exact fun i _=>mem_univ _; exact fun i _=>coverE s r i; exact fun Q h=> cover_m s r Q (mem_filter.mp h).2
 intro i p; unfold food; rw [coverE]
end
private abbrev B₀(n r:ℕ):=((2*r+1)^n:ℕ)
abbrev feeχ(n r:ℕ):ℝ:=9*(B₀ n r)+ 4
def χwage (χ:ℝ)(i:CoreX s r):=Real.exp (-χ*i.val.card)
private lemma homes(x:B) : (porch s r x).card≤B₀ n r:= (Grid.collar_volume ..).trans (by simp)
lemma exp_pay{χ:ℝ}(p:feeχ n r ≤χ): Toll (plan s r).T (χwage s r χ) 4 (1/4):=by
 let A:=porch s r; let w(x:B):=Real.exp (-χ); let k:=B₀ n r
 have hp:Toll A w 5 (1/4):=by
    refine ⟨fun i=> (Real.exp_pos _).le,fun i=> budget_of_sum (fun x=>by unfold hit; split; apply mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le; exact le_rfl) (fun t=>?_)⟩
    have he:(t.filter fun j=> i∈ A j).card≤k:= ((card_le_card (t:= A i) (fun x (h:x∈ Finset.filter _ t)=>by apply (porch_m s r i x).2; rw [Grid.dist_symm]; exact (porch_m s r x i).1 (mem_filter.mp h).2)).trans (homes s r i))
    set W:= t.filter (fun j=> i∈ A j); let z:=Real.exp (-4*(k:ℝ))
    have hf:∀ j∈ W,Real.exp (5*↑(A j).card)*w j≤z:= fun j _=>by
       unfold w z; rw [←Real.exp_add]; apply Real.exp_monotone; have h:(↑(A j).card:ℝ)≤k:= Nat.cast_le.mpr (homes s r j); change 9*(k:ℝ)+4≤χ at p; linarith
    have hw:∑ j∈t,hit A w 5 i j=∑ j∈ W,Real.exp (5*↑(A j).card)*w j:=by unfold W; rw [sum_filter]; apply sum_congr rfl; intro i _; unfold hit; split_ifs<;>rfl
    rw [hw]
    apply (sum_le_sum hf).trans; rw [sum_const,nsmul_eq_mul]; apply le_trans (b:=(k:ℝ)*z); · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; exact_mod_cast he
    unfold z; rw [neg_mul,Real.exp_neg,← div_eq_mul_inv]; apply (div_le_iff₀ (Real.exp_pos _)).2; have hx:= Real.add_one_le_exp (4*(k:ℝ)); linarith
 let V:=hull A; have hu:= counts A (a:=4) hp (by norm_num) (by norm_num); have ht : Toll (roofT A) (payC A w ∘ Subtype.val) 4 (1/4):= ⟨fun i=> hu.nonneg i.val,fun i=>budget_pull Subtype.val Subtype.val_injective (hu.pays i)⟩
 have he: payC A w ∘ Subtype.val = χwage s r χ:=by ext i; simp only [Function.comp,payC,show Spark A i.val from i.property,if_true,wage,w,prod_const, χwage]; rw [←Real.exp_nat_mul]; ring_nf
 rw [he] at ht; exact ht
end YM.CF.BProof.Contour.Tower
