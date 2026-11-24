import YM.SU5.Intrinsic.Coil.Cork

/-! # zero and single-key term at Peer assembly -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[DecidableEq I][Fintype I]{n:Side}
private lemma eerie {Y:Type*}[Fintype Y][DecidableEq Y](S:Finset Y)(q:Y→Finset (Seat n))(p:Ac.Spark q S)(t: ∀ i∈S,∀ j∈S,i≠j → Disjoint (q i) (q j)):
 ∃ x:Y,S={x}:=by
 obtain ⟨x,h⟩:= p.1; refine ⟨x, Subset.antisymm ?_ (singleton_subset_iff.mpr h)⟩
 intro i v; refine mem_singleton.mpr ?_
 have he(y z)(u:Ac.bonds q S y z):y=z:=by obtain ⟨a,b,k,c,d⟩:=u; by_contra p; exact Finset.disjoint_left.mp (t _ a _ b p) c d
 let R:=Ac.chain q S; have H(y z:Y)(r:R y z):y=z:=by
    induction r with| refl=>rfl|tail _ t ih=> exact ih.trans (he _ _ t)
 exact H _ _ (p.2 i v x h)

-- simple presence test for **Heavy**. Useful with Ψ amplification bookkeeping. Keeper shape synth.
namespace Chart.Stoke
variable {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
variable (C:B.Stoke δ P H V a) (T:Blizzard F P H δ b)(L:Finset (I⊕ Force n))(S:Aura n)(D:Support (More n)) (l:List I)
open Push.AbsoluteSums Push.AbsoluteSums.Trees
local notation "Λ"=> B.ledger
variable (Q:ℝ)(f: (I⊕ Force n)→ℝ) (pQ:0≤Q) (hFQ:0≤f)(Him:Sum.elim a b ≤ f) (Ω:Set I)
    (budgetT:∀ i:Force n, b i ≤ Q*f (Sum.inr i))
    (budgetI : ∀ i:I,i∉Ω → a i ≤ Q*f (Sum.inl i))
include C T pQ hFQ Him budgetT budgetI
lemma ready_heavy (p:∀ i∈Ω,∀ j∈Ω,B.anchor i≠ B.anchor j→ Disjoint (B.space i) (B.space j)): Heavy B f a b Q:=by
 intro L X D u q; let A:= B.ledger; let V:= Sum.elim a b
 have ht:0≤V:= fun x=> by cases x; exact C.rate _; exact T.rate _
 have he(i:I⊕Force n)(v:i∈L)(hx:V i ≤ Q*f i): Season.leafCost V L ≤ Q*Season.leafCost f L:=by
    unfold Season.leafCost
    rw [←Finset.mul_prod_erase _ V v,←Finset.mul_prod_erase _ f v,←mul_assoc]; exact mul_le_mul hx (Finset.prod_le_prod (fun i _=>ht i) (fun i _=>Him i)) (prod_nonneg fun i _=>ht i) (mul_nonneg pQ (hFQ i))
 by_cases v: ∃ i∈L,V i ≤ Q*f i; · obtain ⟨i,u,p⟩:=v; exact he i u p
 have h(i:I⊕ Force n)(u:i∈L): ∃ x∈Ω,i=Sum.inl x:= by
    rcases i with i|i; · exact ⟨i,(by by_contra h; exact v ⟨_,u,budgetI i h⟩),rfl⟩
    exact False.elim (v ⟨_,u,budgetT i⟩)
 have l(i)(v:i∈L)(j)(q:j∈L)(e:i≠j):Disjoint (A.seats i) (A.seats j):=by
    obtain ⟨x,z,rfl⟩:=h i v; obtain ⟨y,b,rfl⟩:=h j q; exact p x z y b (u.2.1 _ v _ q e)
 obtain ⟨y,z⟩:=eerie L A.seats (break_h A.seats A.present X L u.1).1 l; obtain ⟨x,b,rfl⟩:=h y (z.symm ▸ mem_singleton_self y)
 exact False.elim (q (mem_image.mpr ⟨x,mem_univ _,z.symm⟩))
omit C T pQ hFQ Him budgetT budgetI
lemma only_old (u:Pun B L S D) (v:L.toLeft=∅):∃ i:Force n,L={Sum.inr i}∧ lordD i=S∧extraD i=D:=by
 let A:= B.ledger; have h(i:I⊕Force n)(p:i∈L):∃ x:Force n,i=Sum.inr x:=by rcases i with i|i; exact False.elim (notMem_empty i (v ▸ mem_toLeft.mpr p)); exact ⟨_,rfl⟩
 have l(i)(v:i∈L)(j)(q:j∈L)(e:i≠j):Disjoint (A.seats i) (A.seats j):=by obtain ⟨x,rfl⟩:= h i v; obtain ⟨y,rfl⟩:= h j q; exact u.2.1 _ v _ q e
 obtain ⟨y,z⟩:=eerie L A.seats (break_h A.seats A.present S L u.1).1 l; obtain ⟨x,rfl⟩:=h y (z.symm ▸ mem_singleton_self y); have h1:=u.tuneSpace; have h2:=u.2.2; rw [z] at h1 h2; exact ⟨x,z,Subtype.ext (by simpa [Album.foot,Chart.ledger] using h1),by simpa [Album.claim,Chart.ledger] using h2⟩
private lemma stated (i:Force n): Pun B ({Sum.inr i} :Finset _) (lordD i) (extraD i):=by
 refine ⟨?_, fun x u y v z=> False.elim (z ((mem_singleton.mp u).trans (mem_singleton.mp v).symm)), ?_⟩
 · simp [Album.melody, rhythm,Chart.ledger]
 simp [Album.claim,Chart.ledger]
include C
private lemma emptyRoll {L:Finset (I⊕Force n)}(u:Pun B L S D) (x:halo δ D⊆ S.val)(p:L.toLeft=∅)(G:Copy n): C.roll u x G l=G:=by
 induction l with| nil=>rfl | cons i l ih=> rw [C.roll_cons,dif_neg (fun h=> notMem_empty i (p ▸ h)),ih]
include T
private lemma regK0 (i:Force n): C.lot {Sum.inr i} F (lordD i) (extraD i) l= F i :=by
 unfold lot
 have hp: ({Sum.inr i}:Finset (I⊕ Force n)).toRight={i}:= by ext; simp
 have hv: ({Sum.inr i}:Finset (I⊕ Force n)).toLeft=∅:=by ext; simp
 split; next h=> rw [C.emptyRoll _ _ _ h.1 h.2 hv,hp,prod_singleton]; -- order tune
 next h => funext V; apply Eq.symm; by_contra t; exact h ⟨stated i,(T.costs i).loaf V t|>.1⟩
lemma baseK : C.issueK F l 0 S D=∑ i∈motV S D,F i:=by
 let T':= (motV S D)
 let S'(v:Force n):Finset (I⊕ Force n):={Sum.inr v}
 unfold issueK; rw [← Finset.sum_subset (f:=fun i:Finset (I⊕ Force n)=> cutL (0:I→ℂ) i • C.lot i F S D l) (subset_univ (T'.image S')) ?_]; swap;
 · intro i _ h; rcases i.toLeft.eq_empty_or_nonempty with p|p
   · unfold lot; split; next v=> obtain ⟨k,t,z,a⟩:= only_old i _ _ v.1 p; exact False.elim (h (t.symm ▸ mem_image_of_mem S' (mem_filter.mpr ⟨mem_univ _,z,a⟩)))
     rw [smul_zero]
   obtain ⟨j,u⟩:=p; rw [cutL,prod_eq_zero u (by rfl),zero_smul]
 rw [sum_image]; refine sum_congr rfl fun i p=>?_ ; rotate_left; · intro i _ j _ p; exact Sum.inr.inj (singleton_injective p)
 obtain ⟨t,u⟩:=(mem_filter.mp p).2; subst S D; change cutL (0:I→ℂ) (S' i) • C.lot _ F (lordD i) (extraD i) l=F i; rw [cutL,regK0 C T]; rw [show (S' i).toLeft=∅ from Finset.ext (by simp [S']), Finset.prod_empty, one_smul]
omit T
end Chart.Stoke
end YM.CF.Coil
open YM.CF.Coil.Chart.Stoke
#print axioms baseK
#print axioms ready_heavy
