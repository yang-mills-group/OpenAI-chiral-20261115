import YM.CF.Leaf.Reeve
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre PowerSeries Vow
open RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[LinearOrder ι][Fintype ι]{A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
lemma νall(F:leaf A→leaf A→ B) : ∑ X: leaf A, Ktw F X=∑ X:leaf A,∑ Y∈Cadre.blaze X,F X Y:=by unfold Ktw; rw [sum_comm]; apply sum_congr rfl; intro X _; rw [sum_comm]; simp
lemma υall(F:leaf A→leaf A→leaf A→ B):∑ X:leaf A,Kth F X=∑ X:leaf A,∑ Y∈Cadre.blaze X,∑ Z∈Cadre.blaze X,F X Y Z:=by unfold Kth; rw [sum_comm]; refine sum_congr rfl fun X _=>?_ ; rw [sum_comm]; apply sum_congr rfl; intro Y _; rw [sum_comm]; simp
lemma swing_u(X:FC ι)(F G:Dough ι): bump (bump X F.val) G.val=bump (bump X G.val) F.val:=by
 rw [bump_r,bump_r, show F.val*G.val=G.val*F.val from congrArg Subtype.val (mul_comm F G )]; abel
-- evaluated coefficients. no assumed dependence on outside signature at TRUE Flags.P.Local pressure collapsed.
variable {N:Side}{X Y Z:Aura N}{δ:ℕ}(K:Rinse (Seat N) (Copy N)){Γ: Aura N→ℝ}{M:Orbit N→ Aura N→ FC (Dwell N)}{H:ℝ}{P:BudgetPoint} (T:Pitch P H δ K Γ M)
variable {v₀:ℝ}(hv:1 ≤ H)
variable (E:Aura N→ Copy N)(I:Aura N→ℝ)(pE:∀ X,Span_K P H X (E X) (I X))
variable (x:Orbit N)(z:Rue.FleetS P.threshold x.1)(u:flags P.threshold x.1=∅)
abbrev sailW(X:Aura N): PowerSeries (Cipher N):= fL (πU K E X) x
-- no local notation
abbrev bill_T:=∑ X:Aura N,Leaf.sailW K E x X
abbrev Qo(M:Orbit N→ Aura N→ FC (Dwell N))(V:Orbit N): FC (Dwell N):= ∑ Y: Aura N,M V Y
include z u T hv pE
lemma break_P (i:ℕ): let Q:= Qo M x; let F:= bill_T K E x; let f:=fun i=> (coeff i F).val
 ((coeff i (derivative (Cipher N) F)).val) = Sault.rind ((if i=0 then Q else 0)+bump Q (f i)+(∑ j∈ antidiagonal i,(2:ℝ)⁻¹ • bump (bump Q (f j.1)) (f j.2))):=by
 intro Q F f; let U:=πU K E; let V:=coneU (ζA K) (κA K) (ξA K) (πU K E); let S:=sailW K E x
 have he(X: Aura N): coeff i (derivative (Cipher N) (S X))=coeff i (V X) x:=by
    have hp: derivative (Copy N) (U X)= V X:=by unfold U V πU; nth_rw 1 [bud_L]; rw [Cadre.tide]
    change coeff i (derivative (Cipher N) (fL (U X) x))= _; rw [←hp,coeff_derivative,fP,coeff_derivative,Pi.mul_apply]; rfl
 have ht: coeff i (derivative (Cipher N) F) = ∑ X:Aura N, coeff i (V X) x:=by
    unfold F bill_T; rw [map_sum,map_sum]; exact sum_congr rfl fun X _=> he X -- map_sum derivative LinearMap add?
 let ν (X:Aura N)(i:ℕ):=coeff i (πU K E X); let R(X:Aura N):=M x X
 let D(k:ℕ)(X:Aura N):=ν X k x
 have hk (k:ℕ) (X Y:Aura N)(u:Disjoint X.val Y.val): bump (R X) (D k Y).val=0:=by
    apply sub_eq_zero.mpr; let U:=life ( (era_K K T hv E I pE k Y).lit x); refine (T.edge x X|>.apart U ?_).trans (one_smul ..)
    exact Finset.disjoint_left.mpr fun i h=> fun p=> Finset.disjoint_left.mp u (mem_filter.mp h).2 (mem_filter.mp p).2 -- implicit i arg
 have hb(i:ℕ): f i=∑ X:Aura N,(D i X).val:=by
    let B:=Dough (Dwell N); unfold f F bill_T; rw [map_sum,show Subtype.val (∑ X:Aura N,coeff i (Leaf.sailW K E x X))= _ from map_sum B.val _ univ]; refine sum_congr rfl fun _ _=>?_ ; exact congrArg Subtype.val (fP ..) -- tune
 have hu(i j:ℕ)(X Y Z:Aura N)(p:Disjoint X.val Z.val): bump (bump (R X) (D i Y).val) (D j Z).val=0:=by rw [swing_u,hk j X Z p]; simp [bump]
 let Hφ(X:Aura N):=ξA K X
 let hZ(X Y:Aura N):= ζA K X Y (ν Y i); let hM(X Y Z:Aura N):=∑ j∈ antidiagonal i,κA K X Y Z (ν Y j.1) (ν Z j.2)
 have hp:∑ X:Aura N,coeff i (V X)=(∑ X:Aura N,if i=0 then Hφ X else 0)+ (∑ X:Aura N,∑ Y∈Cadre.blaze X,hZ X Y)+(∑ X:Aura N,∑ Y∈Cadre.blaze X, ∑ Z∈Cadre.blaze X,hM X Y Z):=by
    rw [←νall,←υall]; unfold V Hφ hM hZ ν coneU vertexL vertexD; simp_rw [map_add,coeff_mk,coeff_C,sum_add_distrib]
 let Ψ:Copy N→+FC (Dwell N):={ toFun:=fun f=>(f x).val,map_zero':=rfl,map_add':=fun _ _=>rfl }
 rw [ht,←Finset.sum_apply]; change Ψ _= _ ; rw [hp,map_add,map_add]; unfold Sault.rind; rw [map_add,map_add]; refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ ?_) ?_
 · split_ifs with h; · rw [map_sum]; change _= (Pastry.cane _).eval (∑ Y:Aura N,R Y); rw [map_sum]; exact sum_congr rfl fun X _=> Ω_Q K T hv x z u X -- pE not included in Reign.
   rw [sum_const_zero,map_zero,map_zero]
 · unfold Q Qo; simp_rw [σq,map_sum]; refine sum_congr rfl fun X _=>?_ ; rw [hb]; simp_rw [σb,map_sum]
   let h(Y:Aura N)(p:Y∈Cadre.blaze X): Ψ (hZ X Y)= Sault.rind (bump (R X) (D i Y).val):= Ω_u K T hv x z u _ _ _ (era_K K T hv E I pE _ _)
   rw [sum_congr (g:=fun Y=>Sault.rind (bump (R X) (D i Y).val)) rfl h]; apply sum_subset (subset_univ _); intro Y _ h; have he:Disjoint X.val Y.val:=by by_contra l; exact h (mem_filter.mpr ⟨mem_univ _,l⟩)
   rw [hk _ X Y he, Sault.rind,map_zero]
 unfold Q Qo; simp_rw [σq,map_sum, smul_sum,hM]; simp_rw [map_sum]; rw [sum_comm (s:=antidiagonal i)]; apply sum_congr rfl; intro X _
 simp_rw [sum_comm (s:= Cadre.blaze X) (t:=antidiagonal i)]; apply sum_congr rfl; intro τ t; -- order may nested fZ
 let Ω(Y Z:Aura N):= Sault.rind ((2:ℝ)⁻¹ • bump (bump (R X) (D τ.1 Y).val) (D τ.2 Z).val)
 simp_rw [hb,σb, smul_sum,map_sum]; simp_rw [σq,smul_sum,map_sum]; conv_rhs=> rw [sum_comm]
 refine Eq.trans (b:=∑ Y∈Cadre.blaze X,∑ Z∈Cadre.blaze X,Ω Y Z) ?_ ?_
 · change _=(∑ Y∈Cadre.blaze X,∑ Z∈Cadre.blaze X,Ω Y Z); exact sum_congr rfl (fun i _=>sum_congr rfl fun Z _=>Ω_c K T hv x z u _ _ _ _ _ (era_K K T hv E I pE _ _) (era_K K T hv E I pE _ _))
 · change _=∑ Y:Aura N,∑ Z:Aura N,Ω Y Z
   apply Eq.trans (sum_congr (g:=fun Y=>∑ Z:Aura N,Ω Y Z) rfl ?_) (sum_subset (subset_univ _) ?_)
   · intro Y _; refine sum_subset (subset_univ _) ?_; intro Z _ p; have he: Disjoint X.val Z.val:=by by_contra l; exact p (mem_filter.mpr ⟨mem_univ _,l⟩)
     unfold Ω; rw [hu _ _ X Y Z he,smul_zero,Sault.rind,map_zero]
   · intro Z _ p; have he:Disjoint X.val Z.val:=by by_contra l; exact p (mem_filter.mpr ⟨mem_univ _,l⟩); -- tune semicolon
     apply sum_eq_zero; intro i _; unfold Ω; rw [hk _ X Z he]; simp [bump,Sault.rind]
end YM.CF.Leaf
