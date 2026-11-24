import YM.CF.Sault.Faro
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- π_map vacuum.Span.Key.L
-- Sector even.E.G
variable {A B: FC n}{p:Bool}{S T U:Finset n}
open Fock
lemma lift_v(h:Fock.Sector S p A)(g:S⊆T):Fock.Sector T p A:=by
 induction h with |one=>apply Fock.Sector.one|zero=>apply Fock.Sector.zero|up i k=> exact Fock.Sector.up _ (g k)|down i k=> exact Fock.Sector.down _ (g k)|scale _ v ih=> exact ih.scale v|add _ _ ih ik=> exact ih.add ik|mul _ _ ih ik=> exact ih.mul ik
lemma spin_v (h:Fock.Sector S false A)(i:Finset n)(w:A i ∅≠0):i∈ Wheat S:=by
 refine mem_filter.mpr ⟨mem_powerset.mpr ?_,?_⟩
 · intro j hj; by_contra p; exact notMem_empty j ((h.dotGrade i ∅ w j p).mpr hj)
 have he:=h.grade_diag
 let Z: UNI n := phaseU (-1) (by simp); let Q:=quant Z.val
 have hp:star Q=Q:=by unfold Q; rw [←quant_star,show Z.val=(-1:ℂ) • 1 from rfl,star_smul]; simp
 rw [twist_formula] at he; change Q*A*(star Q)=(1:ℂ) • A at he
 have ht:Z.val=Matrix.diagonal fun _:n=> -1:=by change ((-1:ℂ) • (1:Op n))= _; ext i j; by_cases h:i=j <;> simp [h]
 rw [one_smul,hp] at he; unfold Q at he; rw [ht,quant_diag] at he
 have hu:= Matrix.ext_iff.mpr he i ∅; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Finset.prod_const,card_empty,pow_zero,mul_one] at hu
 rw [←one_mul (A i ∅)] at hu; have hb: (-1:ℂ)^i.card=1:=by apply mul_right_cancel₀ w; simpa only [one_mul] using hu
 by_contra hv; rw [(Nat.not_even_iff_odd.mp hv).neg_pow] at hb; norm_num at hb
lemma yarn(h:S⊆T):Fock.Sector T (decide (¬ Even S.card)) (poke S):=by
 induction S using Finset.induction_on with
 | empty=> rw [poke,Poly.tag_void]; exact (by simp; exact Fock.Sector.one)
 | insert i S g ih=>
    obtain ⟨u,v⟩:=insert_subset_iff.mp h; unfold poke; rw [Poly.tag_any _ _ _ g,card_insert_of_notMem g]; rw [show decide (¬ Even (S.card+1))=true.xor (decide (¬Even S.card)) from ?_]; exact ((Fock.Sector.up _ u).mul (ih v)).scale _; by_cases h':Even S.card <;> simp [Nat.even_add,h'] -- tune
lemma life (p:Flour S A):Fock.Sector S false A:=by rw [p.pin]; apply Fock.Sector.sumS; intro i u; obtain ⟨h,w⟩:=mem_filter.mp u; have hv:=yarn (mem_powerset.mp h); rw [decide_eq_false (not_not_intro w)] at hv; exact hv.scale _
-- compress exact action for all parities via vacuum
abbrev rind (F:FC n):FC n:= (Pastry.cane n).eval F
lemma rank_a(F:FC n):rind F=∑ i:Finset n,crumb F i • poke i:=rfl
lemma skit (A:FC n):spanP n (rind A):=by rw [rank_a]; exact snack fun i _=> spanS (spanPt i) _
lemma sky (p:Scree.spanP n A) (w:Scree.spanP n B)(h:acts A (vacuum _)=acts B (vacuum _)):A=B:=by refine p.trans (Eq.trans ?_ w.symm); exact sum_congr rfl (fun i _=>by rw [col,col,h])
lemma tileL(F:FC n):acts (rind F) (vacuum _)=acts F (vacuum _):=by rw [rank_a,act_sum]; refine Eq.trans (Finset.sum_congr rfl ?_) (basis_expand (acts F (vacuum _))); intro i _; rw [act_smul,poked,col]
lemma light_e (h:Fock.Sector S false A): Flour S (rind A):=by rw [rank_a]; apply Flour.sum; intro i _; by_cases p:crumb A i=0; rw [p,zero_smul]; exact Flour.trivial; exact (Flour.point (spin_v h i p)).smul _
-- move factors past local.K formally Ext
lemma pert (h:Fock.Sector S false B)(p:Flour T A)(g:Disjoint S T)(F:FC n): rind (B*(A*F))=A*rind (B*F):=by
 apply sky (skit _) (spanT p.allP (skit _)); rw [tileL, ←mul_assoc B A, (h.apart (life p) g),show Fock.Sector.grainB false false= _ from (show Fock.Sector.grainB false false=1 from rfl),one_smul,mul_assoc,act_mul,act_mul A,tileL]
variable (b r:Bool)(V:UNI n)
lemma plower (A: FC (LeanV n)):sauce b r V (rind A)=rind (sauce b r V A):=by
 let U:= (spice V r); let P:=quantU U; let Q:=acts P.val; let R:=b.xor r; let y:=vacuum (LeanV n)
 have hu: (acts P.val) y=y:=quant_vac ..; have hp (K:FC (LeanV n)): Q (dove R (acts K y))=acts (sauce b r V K) y:=by rw [dove_acts,dove_base]; unfold Q; rw [Fock.swivel,hu]; rfl
 apply sky _ (skit _)
 · rw [tileL,←hp,←hp,tileL]
 rw [rank_a,sauce,singT,win_sum,map_sum]; apply snack; intro i _; rw [win_c,twist_scalar]; exact spanS (sauceS b r V i) _
end YM.CF.Sault
