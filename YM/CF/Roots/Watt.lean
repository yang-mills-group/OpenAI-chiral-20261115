import YM.CF.Roots.Hat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}{u t B:ℕ}{C ε η a d:ℝ}
variable {J X:Type}[Fintype J][LinearOrder J][Fintype X][DecidableEq X]
local notation "ζ"=> Finset J
variable (σ:J→Site n)(c: Site n)
variable (Θ:X→ Support n)(F:Finset J→X→ℝ)
variable(Q:Finset (Finset J))(hp:∀ i∈Q,0≤F i)(hu:∀ i∈Q,∀ x:X,F i x≠0→ c ∈ Θ x ∧ poke_F σ (Θ x) i)
local notation "μ'"=> a+1/2
local notation "ϕ"=> dra_k B a
local notation "ψ"=> dra_k B (a+1/2)
local notation "KQ" m:max=> Knot_B (cape_B B) B m σ c
variable (pC:1 ≤ C)(v:8≤ B)(P:Apex (cape_B B) B σ)(W:lamp_B (cape_B B) B t σ)(hz:Nice_B B t C (1/8))(A:ℝ)(pA:∀ i∈Q,∑ x:X,dra_k B (a+1/2) (Θ x)*(F i x) ≤ A)(he:0 ≤ A)
local notation "Jζ"=> Ωb B Θ
include hp hu pC v W hz pA he
variable (ρ:∀ i∈Q, Set.InjOn σ (i:Set J))(ht:∀ i∈Q, 1 < i.card)
include P ρ ht
lemma many_F : ∑ i∈Q,C^i.card * (∑ x:X,ϕ (Θ x)*F i x) ≤ wish_E B A:=by
 have he':=gas_B σ c Θ F Q hp hu pC v W hz A pA he; apply le_trans (Eq.ge ?_) he'
 refine sum_congr rfl fun i p=> congrArg (C^i.card *·) (sum_subset (subset_univ _) fun x _ u=>?_ )
 rw [show F i x=0 from ?_,mul_zero]; by_contra hX; have hx:coverNumber B (Θ x)<B:= lt_of_not_ge (fun t=>u (mem_filter.mpr ⟨mem_univ _,t⟩)); obtain ⟨p1,p2⟩:= hu i p x hX; obtain ⟨u,w,y,m,R⟩:= one_lt_card.mp (ht i p); have he:= Ωperk v _ hx _ _ (p2 u w) (p2 y m); have ht:= P u y fun z=> R (ρ i p w m z); omega
omit ρ ht P
abbrev αB (i: Finset J):Prop:= i.card=1
local notation "ψU"=> reach_B (cape_B B) B σ c
variable (g:∀ i∈Q, i.card=1)
include g
lemma tiny_Q: ∑ i∈Q,C^i.card * (∑ x:X,ϕ (Θ x)*F i x) ≤ (t*C*A+wish_E B A):=by
 let Z:= Q; let U:=univ\Jζ; let K(i):=F i; let tE(i:ζ):= C^i.card*(∑ x∈ U,ϕ (Θ x)*K i x); -- infer i type
 have hQ: (∑ i∈Q,tE i) ≤ t*C*A:=by
    let L:= (ψU).image (fun i=>({i}:ζ)); let S:=Q∩L
    have hs:S.card ≤ t:= (card_le_card inter_subset_right).trans (le_trans card_image_le (W c))
    have hu'(i:ζ)(q:i∈Q): tE i ≤ C*A:=by
       unfold tE; rw [g i q,pow_one]; refine mul_le_mul_of_nonneg_left ((sum_le_sum (g:=fun x=>ψ (Θ x)*F i x) (fun x _=>?_)).trans ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _=>mul_nonneg (Real.exp_pos _).le (hp i q x))).trans (pA i q))) (zero_le_one.trans pC)
       exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))) (hp i q _)
    have hh: (∑ i∈ S,tE i)=∑ i∈ Q,tE i:=by
       refine sum_subset inter_subset_left (fun i w p=>?_); obtain ⟨j,u⟩:= card_eq_one.mp (g i w); unfold tE; rw [sum_eq_zero ?_,mul_zero]; intro x t; rw [show K i x=0 from ?_, mul_zero]
       by_contra hX; have hx:=hu i w x hX; apply p; refine mem_inter.mpr ⟨w,mem_image.mpr ⟨j,?_,u.symm⟩⟩; have ht: coverNumber B (Θ x)<B:=lt_of_not_ge (fun v=>(mem_sdiff.mp t).2 (mem_filter.mpr ⟨mem_univ _,v⟩))
       exact mem_filter.mpr ⟨mem_univ _, Ωperk v _ ht _ _ hx.1 (hx.2 j (by simp [u]))⟩ -- shadow v
    rw [←hh]; refine le_trans (sum_le_sum fun i w=>hu' _ (mem_of_mem_inter_left w)) ?_; have hT:0 ≤ C:=zero_le_one.trans pC; rw [Finset.sum_const,nsmul_eq_mul,mul_assoc (↑_ :ℝ) C]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs) (mul_nonneg hT he)
 apply le_trans _ (add_le_add hQ (gas_B σ c Θ F Q hp hu pC v W hz A pA he)); rw [←sum_add_distrib]; apply le_of_eq; apply sum_congr rfl; intro i w; unfold tE; rw [←mul_add,Finset.sum_sdiff (subset_univ _)]; -- unfold K
end YM.CF.Roots
