import GaugeFieldConstruction.MortarS
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
section
variable {α β γ M:Type*}[Fintype α][Fintype β][Fintype γ]
lemma pour_add [CommSemiring M][DecidableEq γ](f:α→γ)(g:β→γ)(X:α→M)(Y:β→M): PourUp (Sum.elim f g) (Sum.elim X Y)=PourUp f X+PourUp g Y:=by
 funext i; unfold PourUp; simp only [sum_filter,Pi.add_apply,Fintype.sum_sum_type]; congr! 1
-- River order crossing from aggregate line derivative.
end
section
variable {n:Side}{α β:Type}[Fintype α][Fintype β]
variable (Ω:Support (More n))(z:α→Force n)(r:β→Force n)
variable {M:Type*}
def hum [CommSemiring M] (z:α→Force n)(v:α→M):= ∑ i:Finset α with PriceI z Ω i,∏ j∈i, v j
lemma hum_pay {U:Orbit n}{P:BudgetPoint}(h:Rue.FleetS P.threshold U.1)(X:ForceBudget n): fueled P X U=hum (flags P.threshold U.1) id (fun i=> X i U):=by
 let t:=flags P.threshold U.1; have ht:hum t id (fun i=>X i U)=fueled P (PourUp id X) U:=(fueled_split id h).symm
 refine Eq.trans ?_ ht.symm -- tune
 apply congrArg (fun f:ForceBudget n=>fueled P f U); funext i; simp [PourUp,sum_filter]
lemma Hum_split [CommSemiring M] (v:α→M):hum Ω id (PourUp z v)=hum Ω z v:=pricePack z Ω v
lemma twin_pour [CommSemiring M] (x:α→M)(y:β→M):
    hum Ω id (PourUp z x + PourUp r y)=∑ A:Finset α,∑ B:Finset β, if PriceI (Sum.elim z r) Ω (A.disjSum B) then (∏ i∈A,x i)*(∏ i∈B,y i) else 0:=by
 rw[←pour_add,Hum_split,hum,Finset.sum_filter,← Fintype.sum_prod_type' (α₁:=Finset α) (α₂:=Finset β)] -- tune
 symm
 refine sum_bij (fun (p:Finset α × Finset β) _=> p.1.disjSum p.2) (fun _ _=> mem_univ _) ?_ ?_ ?_
 · rintro ⟨a,b⟩ _ ⟨c,d⟩ _ h; dsimp only at h; ext : 1; simpa using congrArg Finset.toLeft h; simpa using congrArg Finset.toRight h
 · exact fun A _=> ⟨⟨A.toLeft,A.toRight⟩,mem_univ _,Finset.toLeft_disjSum_toRight⟩
 rintro ⟨a,b⟩ l; dsimp only; split <;> (try rfl)
 rw [prod_disjSum]; rfl
lemma bare_in (A:Finset α) : PriceI (Sum.elim z r) Ω (A.disjSum ∅) ↔ PriceI z Ω A:=by
 have he: til (Sum.elim z r) (A.disjSum ∅)=til z A:=by
    ext i; simp only [til,Finset.mem_biUnion,Sum.exists]; simp [sealI]
 constructor
 · intro v; exact ⟨fun i h j p t=> v.zone (inl_mem_disjSum.mpr h) (inl_mem_disjSum.mpr p) (fun g=>t (Sum.inl.inj g)),he.symm.trans v.covers⟩
 intro v; refine ⟨?_,he.trans v.covers⟩; rintro (a|a) h (b|b) t e <;> simp at *; exact v.zone h t e -- tune

variable [NormedCommRing M][NormedAlgebra ℂ M](X:α→M)(V:β→M)
open scoped YM.CF.Mew
-- fderiv on finite-dimensional physical fibre
lemma smooth_Hum : Differentiable ℂ (hum (M:=M) Ω (id (α:=Force n))):=by
 have DFin(j:Finset (Force n)):Differentiable ℂ (fun x:Force n→M=> ∏ i∈j,x i):=by
   induction j using Finset.induction with
   | empty=> simp
   | insert i k u h=> simp_rw [prod_insert u]; exact (show Differentiable ℂ (fun x:Force n→M=>x i) from differentiable_apply i).mul h
 refine Differentiable.fun_sum (fun j _=> ?_); exact DFin j
def sparkJet (Y:Force n→M): (Force n→M) →L[ℂ] M:= fderiv ℂ (hum Ω id) Y
lemma pay_lamp (c:ℂ):PourUp r (c • V)=c • PourUp r V:=by
 funext i; unfold PourUp; simp only [Pi.smul_apply,Finset.smul_sum]
lemma tilt_power (c:ℂ) : hum Ω id (PourUp z X+c • PourUp r V)=∑ A:Finset α,∑ B:Finset β, c^B.card • (if PriceI (Sum.elim z r) Ω (A.disjSum B) then (∏ i∈A,X i)*(∏ i∈B,V i) else 0):=by
 rw[←pay_lamp,twin_pour]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; split; swap; · rw [smul_zero]
 rw[←Algebra.mul_smul_comm]
 simp_rw[Pi.smul_apply]; apply congrArg (_ * ·)
 exact (Finset.prod_smul j (fun _=>c) V).trans (by rw[prod_const])
lemma prize_line : sparkJet Ω (PourUp z X) (PourUp r V)=∑ A:Finset α,∑ b:β, if PriceI (Sum.elim z r) Ω (A.disjSum {b}) then (∏ i∈A,X i)*V b else 0 :=by
 let f:= hum (M:=M) Ω (id (α:=Force n)); let Z:= PourUp z X; let W:=PourUp r V; let g(t:ℂ):=Z+t•W
 let φ(A:Finset α)(B:Finset β): M:= if PriceI (Sum.elim z r) Ω (A.disjSum B) then (∏ i∈A,X i)*(∏ i∈B,V i) else 0
 have h: HasDerivAt g W 0:=by
    have e:HasDerivAt g (0+(1:ℂ) • W) 0:=(hasDerivAt_const (0:ℂ) Z).add ((hasDerivAt_id' (0:ℂ)).smul_const W)
    rwa[one_smul,zero_add] at e
 have hx: HasDerivAt (f ∘ g) (sparkJet Ω Z W) 0:=by
    rw [show sparkJet Ω Z W=fderiv ℂ f (g 0) W by unfold g; simp[sparkJet,f]]; exact ((smooth_Hum Ω _).hasFDerivAt).comp_hasDerivAt _ h
 have d (y:M)(m:ℕ): HasDerivAt (fun (t:ℂ)=>t^m • y) (if m=1 then y else 0) 0:= by
    have hx:= (hasDerivAt_pow m (0:ℂ)).smul_const y
    by_cases hz:m=1; · simpa only [if_true,if_pos hz,hz,↓reduceIte,Nat.cast_one,zero_add,le_refl,Nat.sub_self,pow_zero,mul_one,one_smul] using hx
    rw[if_neg hz]; by_cases ht:m=0; · simpa only [ht,Nat.cast_zero, Nat.sub_eq_zero_of_le (Nat.zero_le 1),zero_mul,zero_smul] using hx
    have hh:m-1≠0:=by omega
    simpa only [zero_pow hh,mul_zero,zero_smul] using hx
 have hf: HasDerivAt (f ∘ g) (∑ A:Finset α, ∑ B:Finset β, if B.card=1 then φ A B else 0) (0:ℂ):=by rw [show f ∘ g=fun (c:ℂ)=> ∑ A:Finset α,∑ B:Finset β,c^B.card • φ A B from funext (tilt_power Ω z r X V)]; apply HasDerivAt.fun_sum; intro i h; apply HasDerivAt.fun_sum; intro j h; apply d
 refine (hx.unique hf).trans ?_; apply sum_congr rfl; intro a _; rw[←sum_filter]; symm
 apply sum_bij (fun i h=>{i}) (fun _ _=> mem_filter.mpr ⟨mem_univ _,card_singleton _⟩) (fun _ _ _ _ h=> singleton_inj.mp h) ?_ (fun i _=>by simp[φ]) -- tune rw
 intro b hb; obtain ⟨i,h⟩:=card_eq_one.mp (mem_filter.mp hb).2; exact ⟨i,mem_univ _,h.symm⟩
end
end YM.CF.Scree.Ing
end
