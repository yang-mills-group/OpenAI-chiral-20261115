import YM.CF.Roots.Cost
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
lemma kos (U:ζ)(Y:Support n)(p:poke_F σ Y U)(h:c∈Y)(s t:ℕ)(v:coverNumber B Y ≤ t): U∈Knot_B s B t σ c:=mem_filter.mpr ⟨mem_univ _,Y,h,p,v⟩
open Real
lemma rentV (p:B>0)(v:lamp_B (cape_B B) B t σ)(hu:1 ≤ C)(hx:Nice_B B t C ε)(m:ℕ)(h:B≤ m): (∑ i∈Knot_B (cape_B B) B m σ c, C^i.card) ≤ Real.exp (ε*(m:ℝ)):=by
 let K:= Knot_B (cape_B B) B m σ c; let u:=(chip_B B m / cape_B B +1)*t; obtain ⟨hf,hR⟩:= energy_E _ m B t c σ (by unfold cape_B; positivity) v
 let A:= cape_B B; let U:=pearl (chip_B B m+B); let L:= pearl A; let k:= (chip_B B m)/A; have hc:0 ≤ C:=zero_le_one.trans hu
 change ∑ i∈K,_≤_; refine (sum_le_sum (g:=fun _=>C^u) (fun i w=> pow_le_pow_right₀ hu (hR i w))).trans ?_
 simp only [sum_const,nsmul_eq_mul]; have hp:(K.card:ℝ) ≤ U*(L:ℝ)^k * (2:ℝ)^u:=by exact_mod_cast hf
 exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans ((by dsimp only [rentP]; rw [mul_pow,mul_assoc] : _ = rentP C B m t).trans_le (hx m h)) -- tune maybe eq orientation syntax.
abbrev coDay (B:ℕ):=cape_B B+B
-- approximate no collision.Sep tune with σ not inj global
abbrev Apex(s B:ℕ)(σ:J→Site n):Prop:=∀ i j,σ i ≠ σ j → s+s+B+B< separation (σ i) (σ j)
abbrev Force_M(B:ℕ)(σ:J→Site n)(t:ℕ):Prop:= Apex (cape_B B) B σ ∧ lamp_B (cape_B B) B t σ
abbrev clusterP (T t: Site n):= T=t
lemma Ωperk (v:8≤ B) (Y:Support n)(p:coverNumber B Y<B)(x y:Site n)(h:x∈Y)(g:y∈Y): separation x y ≤ B+cape_B B:=by
 apply (extent _ _ h g).trans; have hx:=Nat.mul_le_mul_right (4*B+2) p.le; have ht:8*B^2 ≤ cape_B B:= by unfold cape_B; nlinarith
 nlinarith
variable (Θ:X→ Support n)(F:Finset J→X→ℝ)
variable(Q:Finset (Finset J))(hp:∀ i∈Q,0≤F i)(hu:∀ i∈Q,∀ x:X,F i x≠0→ c ∈ Θ x ∧ poke_F σ (Θ x) i)
abbrev dra_k(B:ℕ)(s:ℝ)(X:Support n):=Real.exp (s*(coverNumber B X:ℝ))
local notation "μ'"=> a+1/2
local notation "ϕ"=> dra_k B a
local notation "ψ"=> dra_k B (a+1/2)
local notation "KQ" m:max=> Knot_B (cape_B B) B m σ c
variable (pC:1 ≤ C)(v:8≤ B)(P:Apex (cape_B B) B σ)(W:lamp_B (cape_B B) B t σ)(hz:Nice_B B t C (1/8))(A:ℝ)(pA:∀ i∈Q,∑ x:X,dra_k B (a+1/2) (Θ x)*(F i x) ≤ A)(he:0 ≤ A)
include hp
private lemma uL_B (i:ζ)(p:i∈Q)(x:X): 0 ≤ϕ (Θ x)*F i x:=mul_nonneg (Real.exp_pos _).le (hp i p x)
include hu pC v W hz pA he
-- outer.Billy
abbrev glaze_B(B m:ℕ)(Θ:X→ Support n):= Finset.univ.filter fun x:X=>coverNumber B (Θ x)=m
local notation "ΦN" m:max=> glaze_B B m Θ
set_option maxHeartbeats 800000 in
lemma lamp_F (m:ℕ)(h:B≤ m): (∑ i∈Q,C^i.card *(∑ x∈ΦN m,ϕ (Θ x)*F i x)) ≤ Real.exp ((-(1/4:ℝ))*B) * Real.exp (-(1/8:ℝ)*(m:ℝ)) * A:=by
 let K:= KQ m; let Tω(i:ζ):= C^i.card * (∑ x∈ΦN m,ϕ (Θ x)*F i x); let E:=Q∩K
 have hh: (∑ i∈E,Tω i)=∑ i∈Q,Tω i:= by
    apply Finset.sum_subset (inter_subset_left); intro i p w; let hq:=hp i p
    unfold Tω; rw [sum_eq_zero ?_,mul_zero]; intro x b; suffices g:F i x=0 by rw [g,mul_zero]
    by_contra q; obtain ⟨l,e⟩:= hu i p x q; exact w (mem_inter.mpr ⟨p,kos σ c i (Θ x) e l (cape_B B) m (mem_filter.mp b).2.le⟩)
 let Z:=Real.exp (-(1/2:ℝ)*m); have hv(i:ζ)(p:i∈ E):Tω i ≤ (C^i.card) *(Z*A):=by
    have hg:0 ≤ C:=zero_le_one.trans pC
    unfold Tω; apply mul_le_mul_of_nonneg_left _ (by positivity); have hd':= (mem_inter.mp p).1; have hs':∑ x∈ ΦN m,ψ (Θ x)*F i x ≤ A:= (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _=>mul_nonneg (Real.exp_pos _).le (hp i hd' x))).trans (pA _ hd')
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hs' (Real.exp_pos _).le); rw [Finset.mul_sum]; apply le_of_eq; apply sum_congr rfl; intro x u; rw [←mul_assoc]; unfold dra_k; rw [(mem_filter.mp u).2]; refine congrArg (· *F i x) ?_; unfold Z; rw [←Real.exp_add]; congr 1; ring
 change (∑ i∈Q,Tω i) ≤_; rw [←hh]; refine (sum_le_sum hv).trans ?_; rw [←Finset.sum_mul]; let t:=Real.exp ((1/8:ℝ)*m); have hT:∑ i∈E,C^i.card≤ t := (Finset.sum_le_sum_of_subset_of_nonneg (show E⊆ K from inter_subset_right) fun i _ _=>pow_nonneg (zero_le_one.trans pC) _).trans (rentV σ c (by omega) W pC hz m h)
 refine (mul_le_mul_of_nonneg_right hT (mul_nonneg (Real.exp_pos _).le he)).trans ?_; rw [←mul_assoc t]; refine mul_le_mul_of_nonneg_right ?_ he; unfold t; rw [←Real.exp_add,←Real.exp_add]; exact Real.exp_monotone (by have hp:(B:ℝ)≤ m:=Nat.cast_le.mpr h; linarith)
abbrev decay_o(B:ℕ):=Real.exp ((-(1/4:ℝ))*B)
local notation "LK"=> Real.exp ((-(1/4:ℝ))*B)
abbrev KZ:= (1-Real.exp (-(1/8:ℝ)))⁻¹
abbrev wish_E(B:ℕ)(A:ℝ):= Real.exp ((-(1/4:ℝ))*B)*KZ*A
abbrev Ωb(B:ℕ)(Θ:X→ Support n):= univ.filter fun x:X=> B≤ coverNumber B (Θ x)
local notation "Jζ"=> Ωb B Θ
lemma gas_B : ∑ i∈Q,C^i.card *(∑ x∈Jζ,ϕ (Θ x)*F i x) ≤ wish_E B A:=by
 let D:= (Jζ).image fun x=> coverNumber B (Θ x); let G(i x):=ϕ (Θ x)*F i x
 have he(i):∑ m∈D,(∑ x∈ΦN m,G i x)=∑ x∈Jζ,G i x:=by
    rw [←Finset.sum_fiberwise_of_maps_to (s:=Jζ) (t:=D) (g:=fun x=>coverNumber B (Θ x)) (fun i h=> mem_image_of_mem _ h)]; apply sum_congr rfl; intro m v; obtain ⟨x,u,rfl⟩:=mem_image.mp v; congr 1; ext t; simp only [Ωb,glaze_B,mem_filter,mem_univ,true_and]; exact ⟨fun z=>⟨z ▸ (mem_filter.mp u).2,z⟩,And.right⟩ -- tune
 simp_rw [show ∀ i, (∑ x∈Jζ,ϕ (Θ x)*F i x)=∑ m∈D,∑ x∈ΦN m,G i x from fun i=> (he i).symm, Finset.mul_sum]; rw [Finset.sum_comm]; refine le_trans (sum_le_sum (g:=fun m:ℕ=>LK*Real.exp (-(1/8:ℝ)*(m:ℝ))*A) (fun i h=>?_)) ?_ -- name he shadow positivity
 · have hx: B≤ i:=by obtain ⟨q,r,rfl⟩:=mem_image.mp h; exact (mem_filter.mp r).2
   simp_rw [←Finset.mul_sum]; exact lamp_F σ c Θ F Q hp hu pC v W hz A pA (by assumption) i hx
 rw [←sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) (by assumption); let U:=Real.exp (-(1/8:ℝ)); have ht:‖U‖<1:=by unfold U; rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; norm_num
 have hs:∑' i:ℕ,U^i=KZ:= tsum_geometric_of_norm_lt_one ht; rw [←hs]; simp_rw [mul_comm (-(1/8:ℝ)),Real.exp_nat_mul]; exact Summable.sum_le_tsum D (fun i _=>pow_nonneg (Real.exp_pos _).le i) (summable_geometric_of_norm_lt_one ht)
end YM.CF.Roots
