import YM.CF.Leaf.Warp
import YM.CF.Neon.Ten
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre PowerSeries Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι:Type}[LinearOrder ι][Fintype ι]{A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
variable {N:Side}{X Y Z:Aura N}{δ:ℕ}(K:Rinse (Seat N) (Copy N)){Γ: Aura N→ℝ}{M: Orbit N→ Aura N→ FC (Dwell N)}{H:ℝ}{P:BudgetPoint} (T:Pitch P H δ K Γ M)
variable {v₀:ℝ}(hv:1 ≤ H)
variable (E:Aura N→ Copy N)(I:Aura N→ℝ)(pE:∀ X,Span_K P H X (E X) (I X))
variable (x:Orbit N)(z:Rue.FleetS P.threshold x.1)(u:flags P.threshold x.1=∅)
variable {v:leaf (Seat N)→ℝ}{ℓ w' s r a c d e b':ℝ}
variable (S:ι→Bag N)(Q:ι→ Aura N→ℝ)(p:∀ i,Bias δ (S i) P H (Q i))(w:Key ι)(hp:w∈hill ι)
variable (σ:ι→Seat N)(pS:∀ i X,σ i∉X.val→ S i X=0)(B':Ids N)
variable (ht:∀ i,∀ X Y:Aura N,X.val⊆Y.val→∀ V, V.1∈ Sour.σX P Y ∅ →∀ A:Ids N,S i X (V.1,A)= S i X V)
variable (he:Bake.Turf E)
abbrev can_X (X:Aura N):= πU (θlens S Q p w) E X
private lemma κfee(X:Aura N)(j:ℕ): coeff (j+1) (can_X E S Q p w X)=let T:=θlens S Q p w; let F:= πU T E; ((j:ℝ)+1)⁻¹ • ((if j=0 then ξA T X else 0) + coeff j (vertexL F (ζA T) X)+coeff j (vertexD F (κA T) X)):=by
  rw [can_X,πU,bud_L,sprig]; simp_rw [coneU,map_add, coeff_C]
private lemma α_p(U:Aura N→PowerSeries (Copy N))(X:Aura N)(i:ℕ):coeff i (vertexL U (ζA K) X)=Ktw (fun X Y=>ζA K X Y (coeff i (U Y))) X:=PowerSeries.coeff_mk _ _
private lemma β_p(U:Aura N→PowerSeries (Copy N))(X:Aura N)(i:ℕ):coeff i (vertexD U (κA K) X)=Kth (fun X Y Z=>∑ j∈ antidiagonal i, κA K X Y Z (coeff j.1 (U Y)) (coeff j.2 (U Z))) X:=PowerSeries.coeff_mk _ _
lemma riseQ(X:Aura N)(i:ℕ):River fun w:Key ι=> coeff i (can_X E S Q p w X) x:=by
 induction i using Nat.strong_induction_on generalizing X with
 |h i ih=> cases i with
    |zero=> simp_rw [show ∀ j:Key ι,coeff 0 (can_X E S Q p j X)=E X from fun j=>by rw [can_X,πU,bud_L,tick_r]] -- simp LOOP bud_L!
            exact zeroR _
    |succ i=> simp_rw [κfee,α_p,β_p,Pi.smul_apply,Pi.add_apply]; refine Rive.bScale _ (dub_V (dub_V ?_ ?_) ?_) _
              · split; exact rent_X S Q p x _ (zeroR _) _ _ _; exact zeroR _
              · unfold Ktw; simp_rw [Finset.sum_apply]; apply tick_sum; intro Y _; apply tick_sum; intro Z _; split; exact rule_ζ S Q p x _ _ _ (ih _ (by omega:i< i+1) Z); exact zeroR _
              unfold Kth; simp_rw [Finset.sum_apply]; apply tick_sum; intro Y _; apply tick_sum; intro Z _; apply tick_sum; intro U _; split; swap; exact zeroR _
              simp_rw [Finset.sum_apply]; refine (tip_bank _ _ (fun j v=>?_)).1; have he:=mem_antidiagonal.mp v; exact rule_κ S Q p x _ _ _ _ _ (ih j.1 (by omega) Z) (ih j.2 (by omega) U)
abbrev vwP(X:Aura N)(i:ℕ):=coeff i (huu_SK (θlens S Q p w) E X)
lemma scopeK(X:Aura N)(i:ℕ): River fun j:Key ι => vwP E S Q p j X i x:=by
 unfold vwP huu_SK; cases i; · simp_rw [tick_r]; exact zeroR _
 rename_i j; simp_rw [sprig,Pi.smul_apply,map_add,Pi.add_apply,α_p,β_p]; refine Rive.bScale _ (dub_V ?_ ?_) _
 · unfold Ktw; simp_rw [Finset.sum_apply]; apply tick_sum; intro Y _; apply tick_sum; intro Z _; split; exact rule_ζ _ _ _ _ _ _ _ (riseQ E x S Q p Z j); exact zeroR _
 unfold Kth; simp_rw [Finset.sum_apply]; apply tick_sum; intro Y _; apply tick_sum; intro Z _; apply tick_sum; intro U _; split; swap; exact zeroR _
 simp_rw [Finset.sum_apply]; exact (tip_bank _ _ (fun j _=>rule_κ _ _ _ _ _ _ _ _ _ (riseQ E x S Q p Z j.1) (riseQ E x S Q p U j.2))).1 -- signature check order
include he ht pS
-- tag coherent despite momentum purchases.B.Call.Proof pointer dependence no cheating.
lemma duskQ(X:Aura N)(i:ℕ): let W:=(x.1,B'); coeff i (can_X E S Q p w X) W = coeff i (can_X E S Q p w X) x:=by
 intro W; induction i using Nat.strong_induction_on generalizing X with
 |h i ih=>
   cases i with
   |zero=> rw [can_X,πU,bud_L,tick_r]; exact (he X x B').symm
   |succ i=>
      let V:=θlens S Q p w; let Q':=πU V E
      have ha(X Y:Aura N)(F G:Copy N)(t:F W=G x):= veer_K S Q p w σ pS x B' ht X Y F G t -- order V argument? veer_K signatures
      have hb(Y X Z:Aura N)(F G:Copy N)(t:F W=F x)(u:G W=G x): κA V X Y Z F G W= κA V X Y Z F G x:=by
         let P':=αK (αK X Y) Z; unfold κA; simp only [Pi.mul_apply,Pi.smul_apply,Pi.add_apply,Pi.sub_apply]; rw [show go_K (X:=P') V X (F*G) W= _ from ha _ _ _ (F*G) (show _=F x*G x from congrArg₂ (·*·) t u), show go_K (X:=P') V X G W= _ from ha _ _ _ _ u,show go_K (X:=P') V X F W= _ from ha _ _ _ _ t,show go_K (X:=P') V X 1 W=go_K (X:=P') V X 1 x from ha _ _ _ _ rfl,t,u]
      have hβ(Y X:Aura N)(F:Copy N)(t:F W=F x): ζA V X Y F W= ζA V X Y F x:=by
         let P':=αK X Y; unfold ζA; simp only [Pi.sub_apply, Pi.mul_apply]; rw [show go_K (X:=P') V X F W= _ from ha _ _ _ _ t, show go_K (X:=P') V X 1 W=go_K (X:=P') V X 1 x from ha _ _ _ _ rfl,t]
      rw [κfee]; simp only [α_p,β_p,Ktw,Kth,Pi.smul_apply, Pi.add_apply, Finset.sum_apply]; congr 1; apply congrArg₂ (·+·); apply congrArg₂ (·+·); split; exact ha _ _ _ _ rfl; rfl
      · apply sum_congr rfl; intro Y _; apply sum_congr rfl; intro Z _; split; exact hβ _ _ _ (ih _ (by omega:i< i+1) Z); rfl
      apply sum_congr rfl; intro Y _; apply sum_congr rfl; intro Z _; apply sum_congr rfl; intro U _; split; swap; rfl
      rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j p; have he:= mem_antidiagonal.mp p; exact hb _ _ _ _ _ (ih j.1 (by omega) Z) (ih j.2 (by omega) U)
lemma sugar_V(X:Aura N)(i:ℕ): vwP E S Q p w X i x= vwP E S Q p w X i (x.1,B'):=by
 let R:= θlens S Q p w; have hw:ξA R X x= ξA R X (x.1,B'):= (veer_K S Q p w σ pS x B' ht X X 1 1 rfl).symm -- later
 have hp:= (duskQ E x S Q p w σ pS B' ht he X i).symm; change coeff i (πU R E X) x=coeff i (πU R E X) (x.1,B') at hp; rw [Leaf.born_p,map_add,map_add,coeff_mk,coeff_C] at hp; simp only [Pi.add_apply] at hp; split_ifs at hp <;> simpa only [Pi.zero_apply,hw, he X x B',add_right_inj] using hp
lemma ass_U(i:ℕ)(X:Aura N) : Hush σ X.val (fun j:Key ι=> coeff i (can_X E S Q p j X)):=by
 induction i using Nat.strong_induction_on generalizing X with
 |h i ih=>
   cases i with
   |zero=> intro x p y t h; dsimp only; rw [can_X,can_X,πU,πU,bud_L,bud_L,tick_r,tick_r]
   |succ i =>
      intro x v y u g; have hv(Y:Aura N)(p':Y.val ⊆ X.val):= hut_Y S Q p σ pS ht X Y ∅ (0:Copy N) x v y u (fun i t=> g i (p' t))
      let A:=θlens S Q p x; let B:=θlens S Q p y
      have ha(Y:Aura N)(D:Aura N)(R:Copy N)(p':Y.val ⊆ X.val): go_K (X:=D) A Y R=go_K (X:=D) B Y R:= hut_Y S Q p σ pS ht D Y ∅ R x v y u (fun i t=> g i (p' t))
      have ht'(Y:Aura N)(j:ℕ)(t:j< i+1)(z:Y.val⊆X.val): coeff j (πU A E Y)=coeff j (πU B E Y):=ih j t Y x v y u (fun i q=> g i (z q))
      dsimp only; rw [κfee,κfee]; simp only [α_p,β_p]; congr 1; apply congrArg₂ (·+·); apply congrArg₂ (·+·); split; exact ha _ _ _ le_rfl; rfl
      · apply sum_congr rfl; intro Y _; apply sum_congr rfl; intro Z _; split_ifs with h; swap; rfl
        have hZ:Z.val⊆X.val:=h.symm ▸ subset_union_right; have hY:Y.val⊆X.val:=h.symm ▸ subset_union_left
        let F:=coeff i (πU B E Z); change ζA A _ _ _= ζA B _ _ _; simp only [ζA]; rw [ht' Z i (by omega) hZ, ha Y (αK Y Z) 1 hY, ha Y (αK Y Z) F hY]
      apply sum_congr rfl; intro Y _; apply sum_congr rfl; intro Z _; apply sum_congr rfl; intro U _; split_ifs with h; swap; rfl
      have hY:(αK Y Z).val⊆ X.val:= h.symm ▸ subset_union_left; have hZ:Z.val⊆ X.val:=subset_trans subset_union_right hY; have hU:U.val⊆X.val:=h.symm ▸ subset_union_right; have hp:Y.val ⊆X.val:=subset_trans subset_union_left hY
      apply sum_congr rfl; intro j f; have hh:=mem_antidiagonal.mp f
      let k:=αK (αK Y Z) U; let F:=coeff j.1 (πU B E Z); let G:=coeff j.2 (πU B E U); change κA A _ _ _ _ _=κA B _ _ _ _ _; simp only [κA]; rw [ht' Z j.1 (by omega) hZ,ht' U j.2 (by omega) hU,ha _ k (F*G) hp, ha _ k F hp,ha _ k G hp,ha _ k 1 hp]
lemma ass_P(i:ℕ)(X:Aura N): Hush σ X.val (fun j:Key ι=> vwP E S Q p j X i):=by
 intro x hx y hy h; have hp:=ass_U E S Q p σ pS ht he i X x hx y hy h; change coeff _ (πU _ _ _)=coeff _ (πU _ _ _) at hp; rw [born_p,born_p,map_add,map_add,map_add,map_add] at hp; rw [show ξA (θlens S Q p x) X= _ from hut_Y S Q p σ pS ht X X ∅ 1 x hx y hy h] at hp; exact add_left_cancel hp
end YM.CF.Leaf
