import YM.SU5.Relativistic.Featsby
/-!
# Skill concern isolated. BEFORE Preparation chosen. choose at arbitrary budget.
Given small static τ targets (slab gap), event fills uniform. strict.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
-- no selecting β after seeing ℓ; buy via post-parameters allowable by Supplier. slab externally any gap au
structure Income (S:Side)(L μ D₀:ℕ)(q:ℤ)(d':ℕ)(V R E:ℝ): Prop where
 since:0<E
 shy:E≤1
 get :∃ (a:ℝ)(A:ℕ)(F:Waxy)(s:Finset ℤ)(Z Z' C ε:ℝ),D₀≤A ∧ μ≤A ∧ q≤A ∧ 0≤a ∧
    a*sunSp S L d' A ≥ V ∧ 5*(E*(C+4)*meridiem C) ≤ Real.exp (-2*(a+meridiem C)) ∧
    (∀ i∈s,q ≤ i) ∧ s⊆ TwistT A ∧ 0<C ∧ 0≤Z ∧ Z'+Z≤ C ∧ 0<ε ∧
    (ε*C+3*Z)+2*R*(ε*C+3*Z) ≤ E^3 ∧
    (∀ i∈ plusHalf, ∀ j:ℤ,j∉s→ F i j=0) ∧
    (∀ P:Finset WalkA, ∑ k∈P,‖F 2 0 ((d':ℤ) • k)-(if k=0 then 1 else 0)‖^2 ≤ Z^2) ∧ (∀ n:Side, ∀ o:Cover,∀ s:SU.Slot, ‖strum n o A F s‖ ≤ Z') ∧
    (∀ᶠ N in atTop,∀ (M:Jill.Male),N ≤ M.val.val → ∀ n:Side,∀ f:SU.Slot,∀ o:Cover,let X:=strum n o A F f; ‖acts (spar 4 M (1:Pane n)) X-X‖≤Z)
variable {S:Side}{V R:ℝ}{L μ d:ℕ}
-- choose exponential E along V alone & width; pick tape once. multiplier constants BEFORE choosing A. ensure eps budget denominators.
private lemma fences (S:Side)(L d:ℕ):∀ A:ℕ, barrier S L d A ≤ barrier S L d 0 *(A+1):=by
 intro A; let ℓ:= 4*(8*(d+1)+1); let v:=16*S.val*12
 have he(a): barrier S L d a=4*(v*(a+1)+L)*ℓ^3:=by unfold barrier heightB v ℓ; ring
 rw [he,he, show 4*(v*(0+1)+L)*ℓ^3*(A+1)=4*(v*(A+1)+L*(A+1))*ℓ^3 from (by ring)]; gcongr; exact Nat.le_mul_of_pos_right _ (by omega)
private lemma slower_loop (c B:ℝ)(p:0<c) : ∀ᶠ n:ℕ in atTop,B ≤ Real.exp (c*n):= (Real.tendsto_exp_atTop.comp (tendsto_atTop_atTop_of_monotone (fun i j (h:i≤j)=> mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) p.le) (fun k=> by obtain ⟨n,h'⟩:= exists_nat_gt (k/c); exact ⟨n,le_trans ((div_le_iff₀ p).mp h'.le) (le_of_eq (mul_comm ..))⟩))).eventually_ge_atTop B -- annotate fn ℕ→ℝ
private lemma emceed(q:ℤ)(d L B0:ℕ)(p:9≤d)(μ:ℕ)(V:ℝ)(t:0<R)(S:Side) : ∃ e:ℝ, Income S L μ B0 q d V R e:=by
 let f(A:ℕ):ℝ:= |V| *(barrier S L d A:ℝ); let C:= |V| *(barrier S L d 0:ℝ); let g:= 2*C+1
 have hc:0≤C:=by unfold C; positivity
 have hρ:0<g:=by unfold g; linarith
 have ht(A:ℕ): f A≤ C*((A:ℝ)+1):=by unfold f C; rw [mul_assoc]; gcongr; exact_mod_cast fences S L d A
 -- arbitrary rate r>3*g
 let r:=3*g + 1; obtain ⟨s,c,R',v,P⟩:=houses (2*r) (by unfold r; positivity) d p q
 obtain ⟨C',e,U⟩:=Solstice P (by unfold r; positivity) (by omega : 0<d)
 let X:=2*C'; let K:=meridiem X; have hp:0<X:=by unfold X; positivity
 let E(A:ℕ):=Real.exp (-g*A)
 -- asymptotic constraints
 have hx:∀ᶠ A:ℕ in atTop, 5*(E A*(X+4)*K)≤Real.exp (-2*(f A+K)):=by
    let V' := Real.exp (2*(C+K)); have he:=slower_loop 1 (V'*(5*(X+4)*K)) zero_lt_one
    filter_upwards [he] with A q
    rw [one_mul] at q
    have hw: 5*(X+4)*K≤ Real.exp ((A:ℝ) - 2*(C+K)):=by
       rw [Real.exp_sub]; apply (le_div_iff₀ (Real.exp_pos _)).mpr; rw [mul_comm]; exact q
    rw [show 5*(E A*(X+4)*K)=E A*(5*(X+4)*K) from by ring]; unfold E; apply (mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le).trans; rw [←Real.exp_add]; apply Real.exp_le_exp_of_le
    have he:-g*A+(A-2*(C+K))= -2*(C*((A:ℝ)+1)+K):=by unfold g; ring
    rw [he]; linarith only [ht A]
 let Z(n:ℕ):= C'*spangle r n
 have hS:∀ᶠ A:ℕ in atTop, (3*Z A)+2*R*(3*Z A) < E A^3:=by
    let Y:=(3*C'+2*R*(3*C')); filter_upwards [slower_loop 1 (Y+1) zero_lt_one] with A h
    have hA: Y< Real.exp ((A:ℕ):ℝ):=(lt_add_one _).trans_le (by simpa only [one_mul] using h)
    unfold Z; rw [show 3*(C'*_)+2*R*(3*(C'*spangle r A))=Y*spangle r A from by unfold Y; ring]; refine lt_of_lt_of_eq (mul_lt_mul_of_pos_right hA (spangle_pos ..)) ?_
    unfold spangle E; rw [←Real.exp_add, ←Real.exp_nat_mul,Int.natAbs_natCast]; congr 1; unfold r; push_cast; ring
 obtain ⟨A,⟨⟨u,v₀⟩,hu⟩,H⟩:= (((hx.and hS).and (eventually_ge_atTop (B0+μ+q.natAbs))).and ((eventually_all_finset s).mpr (fun i _=> (eventually_ge_atTop i.natAbs).mono (fun n t=> (show i ∈ TwistT n from mem_Icc.mpr ⟨by omega,by omega⟩))))).exists -- tune
 obtain ⟨F,hf,hs,t₀,z⟩:= U A
 let ε:=(E A^3-(3*Z A+2*R*(3*Z A)))/(X+2*R*X)
 have he:0<X+2*R*X:=by positivity
 have hp':ε*(X+2*R*X)=(E A^3-(3*Z A+2*R*(3*Z A))):= div_mul_cancel₀ _ he.ne'
 refine ⟨E A,Real.exp_pos _,Real.exp_le_one_iff.mpr (show -g*(A:ℝ)≤0 from mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), f A,A,F,s,Z A,C',X,ε,by omega,by omega,by omega,by unfold f; positivity,?_,u,v,(fun i p=> H i p),hp,(mul_pos e (spangle_pos ..)).le,?_,div_pos (sub_pos.mpr v₀) he,?_,hs,t₀,hf,z⟩
 · unfold f sunSp; rw [mul_assoc,mul_inv_cancel₀ (by exact_mod_cast (barrier_pos ..).ne'),mul_one]; exact le_abs_self _
 · have hv:spangle r A ≤1:=Real.exp_le_one_iff.mpr (show -r*(↑(A:ℤ).natAbs:ℝ)≤0 from mul_nonpos_of_nonpos_of_nonneg (by unfold r; linarith only [hρ]) (by positivity)); unfold X Z; nlinarith only [hv,e]
 nlinarith only [hp']

theorem supplied (p:9≤d)(t:0<R)(S:Side)(L μ B:ℕ)(q:ℤ)(V:ℝ):∃ e,Income S L μ B q d V R e:= emceed q d L B p μ V t S
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.supplied
