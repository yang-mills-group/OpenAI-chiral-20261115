import YM.CF.Roots.Watt
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
/- K4r version of Roots lamp,gas,many,tiny. -/
open Real
variable (Θ:X→ Support n)(F:Finset J→X→ℝ)
variable(Q:Finset (Finset J))(hp:∀ i∈Q,0≤F i)(hu:∀ i∈Q,∀ x:X,F i x≠0→ c ∈ Θ x ∧ poke_F σ (Θ x) i)
local notation "μ'"=> a+1/8
local notation "ϕ"=> dra_k B a
local notation "ψ"=> dra_k B (a+1/8)
local notation "KQ" m:max=> Knot_B (cape_B B) B m σ c
variable (pC:1 ≤ C)(v:8≤ B)(P:Apex (cape_B B) B σ)(W:lamp_B (cape_B B) B t σ)(hz:Nice_B B t C (1/32))(A:ℝ)(pA:∀ i∈Q,∑ x:X,dra_k B (a+1/8) (Θ x)*(F i x) ≤ A)(he:0 ≤ A)
include hp
include hu pC v W hz pA he
-- outer.Billy
local notation "ΦN" m:max=> glaze_B B m Θ
set_option maxHeartbeats 800000 in
lemma lampΩ (m:ℕ)(h:B≤ m): (∑ i∈Q,C^i.card *(∑ x∈ΦN m,ϕ (Θ x)*F i x)) ≤ Real.exp ((-(1/16:ℝ))*B) * Real.exp (-(1/32:ℝ)*(m:ℝ)) * A:=by
 let K:= KQ m; let Tω(i:ζ):= C^i.card * (∑ x∈ΦN m,ϕ (Θ x)*F i x); let E:=Q∩K
 have hh: (∑ i∈E,Tω i)=∑ i∈Q,Tω i:= by
    apply Finset.sum_subset (inter_subset_left); intro i p w; let hq:=hp i p
    unfold Tω; rw [sum_eq_zero ?_,mul_zero]; intro x b; suffices g:F i x=0 by rw [g,mul_zero]
    by_contra q; obtain ⟨l,e⟩:= hu i p x q; exact w (mem_inter.mpr ⟨p,kos σ c i (Θ x) e l (cape_B B) m (mem_filter.mp b).2.le⟩)
 let Z:=Real.exp (-(1/8:ℝ)*m); have hv(i:ζ)(p:i∈ E):Tω i ≤ (C^i.card) *(Z*A):=by
    have hg:0 ≤ C:=zero_le_one.trans pC
    unfold Tω; apply mul_le_mul_of_nonneg_left _ (by positivity); have hd':= (mem_inter.mp p).1; have hs':∑ x∈ ΦN m,ψ (Θ x)*F i x ≤ A:= (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _=>mul_nonneg (Real.exp_pos _).le (hp i hd' x))).trans (pA _ hd')
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hs' (Real.exp_pos _).le); rw [Finset.mul_sum]; apply le_of_eq; apply sum_congr rfl; intro x u; rw [←mul_assoc]; unfold dra_k; rw [(mem_filter.mp u).2]; refine congrArg (· *F i x) ?_; unfold Z; rw [←Real.exp_add]; congr 1; ring
 change (∑ i∈Q,Tω i) ≤_; rw [←hh]; refine (sum_le_sum hv).trans ?_; rw [←Finset.sum_mul]; let t:=Real.exp ((1/32:ℝ)*m); have hT:∑ i∈E,C^i.card≤ t := (Finset.sum_le_sum_of_subset_of_nonneg (show E⊆ K from inter_subset_right) fun i _ _=>pow_nonneg (zero_le_one.trans pC) _).trans (rentV σ c (by omega) W pC hz m h)
 refine (mul_le_mul_of_nonneg_right hT (mul_nonneg (Real.exp_pos _).le he)).trans ?_; rw [←mul_assoc t]; refine mul_le_mul_of_nonneg_right ?_ he; unfold t; rw [←Real.exp_add,←Real.exp_add]; exact Real.exp_monotone (by have hp:(B:ℝ)≤ m:=Nat.cast_le.mpr h; linarith)
local notation "LK"=> Real.exp ((-(1/16:ℝ))*B)
abbrev Zprice:= (1-Real.exp (-(1/32:ℝ)))⁻¹
abbrev hope_E(B:ℕ)(A:ℝ):= Real.exp ((-(1/16:ℝ))*B)*Zprice*A
local notation "Jζ"=> Ωb B Θ
lemma gas_Q : ∑ i∈Q,C^i.card *(∑ x∈Jζ,ϕ (Θ x)*F i x) ≤ hope_E B A:=by
 let D:= (Jζ).image fun x=> coverNumber B (Θ x); let G(i x):=ϕ (Θ x)*F i x
 have he(i):∑ m∈D,(∑ x∈ΦN m,G i x)=∑ x∈Jζ,G i x:=by
    rw [←Finset.sum_fiberwise_of_maps_to (s:=Jζ) (t:=D) (g:=fun x=>coverNumber B (Θ x)) (fun i h=> mem_image_of_mem _ h)]; apply sum_congr rfl; intro m v; obtain ⟨x,u,rfl⟩:=mem_image.mp v; congr 1; ext t; simp only [Ωb,glaze_B,mem_filter,mem_univ,true_and]; exact ⟨fun z=>⟨z ▸ (mem_filter.mp u).2,z⟩,And.right⟩ -- tune
 simp_rw [show ∀ i, (∑ x∈Jζ,ϕ (Θ x)*F i x)=∑ m∈D,∑ x∈ΦN m,G i x from fun i=> (he i).symm, Finset.mul_sum]; rw [Finset.sum_comm]; refine le_trans (sum_le_sum (g:=fun m:ℕ=>LK*Real.exp (-(1/32:ℝ)*(m:ℝ))*A) (fun i h=>?_)) ?_ -- name he shadow positivity
 · have hx: B≤ i:=by obtain ⟨q,r,rfl⟩:=mem_image.mp h; exact (mem_filter.mp r).2
   simp_rw [←Finset.mul_sum]; exact lampΩ σ c Θ F Q hp hu pC v W hz A pA (by assumption) i hx
 rw [←sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) (by assumption); let U:=Real.exp (-(1/32:ℝ)); have ht:‖U‖<1:=by unfold U; rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; norm_num
 have hs:∑' i:ℕ,U^i=Zprice:= tsum_geometric_of_norm_lt_one ht; rw [←hs]; simp_rw [mul_comm (-(1/32:ℝ)),Real.exp_nat_mul]; exact Summable.sum_le_tsum D (fun i _=>pow_nonneg (Real.exp_pos _).le i) (summable_geometric_of_norm_lt_one ht)
variable (ρ:∀ i∈Q, Set.InjOn σ (i:Set J))(ht:∀ i∈Q, 1 < i.card)
include P ρ ht
lemma manyτ : ∑ i∈Q,C^i.card * (∑ x:X,ϕ (Θ x)*F i x) ≤ hope_E B A:=by
 have he':=gas_Q σ c Θ F Q hp hu pC v W hz A pA he; apply le_trans (Eq.ge ?_) he'
 refine sum_congr rfl fun i p=> congrArg (C^i.card *·) (sum_subset (subset_univ _) fun x _ u=>?_ )
 rw [show F i x=0 from ?_,mul_zero]; by_contra hX; have hx:coverNumber B (Θ x)<B:= lt_of_not_ge (fun t=>u (mem_filter.mpr ⟨mem_univ _,t⟩)); obtain ⟨p1,p2⟩:= hu i p x hX; obtain ⟨u,w,y,m,R⟩:= one_lt_card.mp (ht i p); have he:= Ωperk v _ hx _ _ (p2 u w) (p2 y m); have ht:= P u y fun z=> R (ρ i p w m z); omega
omit ρ ht P
local notation "ψU"=> reach_B (cape_B B) B σ c
variable (g:∀ i∈Q, i.card=1)
include g
lemma tinyτ: ∑ i∈Q,C^i.card * (∑ x:X,ϕ (Θ x)*F i x) ≤ (t*C*A+hope_E B A):=by
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
 apply le_trans _ (add_le_add hQ (gas_Q σ c Θ F Q hp hu pC v W hz A pA he)); rw [←sum_add_distrib]; apply le_of_eq; apply sum_congr rfl; intro i w; unfold tE; rw [←mul_add,Finset.sum_sdiff (subset_univ _)]; -- unfold K
end YM.CF.Roots

