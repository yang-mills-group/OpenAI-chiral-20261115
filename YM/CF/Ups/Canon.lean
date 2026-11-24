import YM.CF.Ups.Trim
set_option autoImplicit false
set_option maxHeartbeats 780000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Reed
open Function Filter Metric Cube Finset Fock Lattice Emu Skye SU Rush Lat Dial Scroll Spire MeasureTheory Pyx Tulip Push.SectorMeasure
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
local notation "Ξ"=> Single N
local notation "QH"=> halfS N
abbrev RuleP(N:Side)(p:Bool)(R:FC (Single N)):Prop:= Fine (halfS N) univ p R
lemma symψ (g:Seat N→ E){p:Bool}{t:FC (Single N)}(z:RuleP N p t): RuleP N p (twist (quantU (tradew N g)) t):=by
 let S:=tradew N g; let G:= twist (quantU S); have hv(i j: Single N)(p:S.val i j≠0): i.1=j.1:=by by_contra h; apply p; exact if_neg h
 induction z with
 |empty=> rw [map_zero]; exact Fine.empty _
 |one=>rw [show twist (quantU (tradew N g)) 1=_ from (by rw [twist_formula, mul_one]; exact (quantU (tradew N g)).property.2 : (twist (quantU (tradew N g))) 1=1)]; exact Fine.one
 |seed i q=>
    by_cases v:i∈ halfS N
    · rw [show (think (halfS N)).term i=put i from if_pos v,←create_put,twist_create]; refine Emu.keyQ (x:=(false,(acts S.val (basisKet i)))) ?_; change acts (tickA N) _=_; apply PiLp.ext; intro j; rw [upper_q, cut_apply]; change _= (acts _ (basisKet i)).ofLp j; split
      · rfl
      next p => rw [basis_act]; change 0 = _; by_contra g'; exact p (mem_filter.mpr ⟨mem_univ _, (congrArg Prod.snd (hv j i (Ne.symm g'))) ▸ ((mem_filter.mp v).2)⟩)
    rw [show (think (halfS N)).term i= -takeF i from if_neg v, map_neg,←remove_take,twist_remove]; suffices g:Fine (halfS N) univ true (remove (acts S.val (basisKet i))) by simpa only [neg_one_smul] using (g.scale (-1));
    refine Emu.keyQ (x:=(true,(acts S.val (basisKet i)))) ?_; change acts (tickA N) _= 0; apply PiLp.ext; intro j; rw [upper_q,cut_apply]; split; next p=> rw [basis_act]; change S.val j i=0; by_contra hp; exact v (mem_filter.mpr ⟨mem_univ _, (congrArg Prod.snd (hv j i hp)) ▸ ((mem_filter.mp p).2)⟩)
    rfl
 | add _ _ h i=> rw [map_add]; exact h.add i
 | scale _ i h=> rw [twist_scalar]; exact h.scale _
 | grow _ _ h i=> rw [map_mul]; exact h.grow i
abbrev ScalarC {Z:Type}{N:Side}(O:Z→ Scree.Phys N→L[ℝ]ℂ):Prop:=∀ i x (c:ℂ),O i (c • x)=c • O i x -- add K var
local instance(n:Side): MeasurableSpace (FC (Single n)):= borel _
local instance(n:Side): BorelSpace (FC (Single n)):= ⟨rfl⟩
structure LampC {Z:Type}[MeasurableSpace Z](O: Z→Scree.Phys N→L[ℝ] ℂ)(A B: Z→ FC (Single N)):Prop where
 pE : RG.Envelope A
 pO : RG.Envelope B
 cryE(i:Z): RuleP N false (A i)
 cryO(i:Z): RuleP N true (B i)
 lamp(i:Z)(U:Scree.Phys N): inner ℂ (mateK N) (acts (A i+B i) U)=O i U
variable (O:Orbit N→Scree.Phys N→L[ℝ]ℂ)(p:Pyx.BoundedT O)(h:ScalarC O)
lemma fine_sub {I:Type}[LinearOrder I][Fintype I] {X:Finset I}{p:Bool}{A B:FC I}(h: Fine X univ p A)(g:Fine X univ p B): Fine X univ p (A-B):= by simpa [sub_eq_add_neg] using h.add (g.scale (-1))
lemma insight {Y Z W X:FC (Single N)} (p:RuleP N true Y)(g:RuleP N true Z)(t:RuleP N false W)(h:RuleP N false X)(Q:∀ x: Wave (Single N),inner ℂ (mateK N) (acts (W+Y) x)=inner ℂ (mateK N) (acts (X+Z) x)): Y=Z ∧ W=X:=by
 have hh:= zeros_Q QH (Y-Z) (W-X) (fine_sub p g) (fine_sub t h) (mateK N) (upper_q N ▸ tickB N) fun z=>show _=0 from (by rw [show Y-Z+(W-X)=W+Y-(X+Z) from by abel,act_sub,inner_sub_right, Q,sub_self]); exact ⟨sub_eq_zero.mp hh.1,sub_eq_zero.mp hh.2⟩
variable {I:Type}[MeasurableSpace I] (O':I→Scree.Phys N →L[ℝ]ℂ)(hc:ScalarC O')(p':∀ x:Scree.Phys N,RG.Envelope fun i:I=>O' i x)
include hc p'
lemma clan_PS :∃ A B,LampC O' A B:=by
 choose f A hx hv using zest_A QH; let Y:=mateK N; obtain ⟨hY,pY⟩:= contrast_K QH Y (upper_q N ▸ tickB N)
 let c:=Y.ofLp QH; let W(i:I)(j:Finset Ξ):ℂ:= O' i (basisKet j)*(star c)⁻¹; let Tq(k:Bool)(i:I):FC Ξ:=∑ j:Finset Ξ with f j=k,W i j • A j
 have hV(i k):RuleP N k (Tq k i):= Fine.sumF _ _ (fun j u=> (mem_filter.mp u).2 ▸ (hx j).scale _)

 have ht(k:Bool): RG.Envelope (Tq k):= by
    -- all,i.Tq
    unfold Tq; simp_rw [sum_filter]; refine Env.total (g:=fun j (i:I)=> if f j=k then W i j • A j else 0) _ ?_; intro i; split_ifs; exact Girt.pole_w _ (fun v:ℂ=>(v*(star c)⁻¹) • A i) (by fun_prop) (p' (basisKet i)); exact Girt.rite_c _
 refine ⟨_,_,ht false,ht true,fun i=>hV i false,fun i=>hV i true,fun i x=>?_⟩
 have hh(i:I): Tq false i+Tq true i=∑ j,W i j • A j:=by unfold Tq; rw [sum_filter,sum_filter,← sum_add_distrib]; apply sum_congr rfl; intro i _; cases (f i)<;> simp
 let z(x:Finset Ξ):=inner ℂ (basisKet x) Y; change inner ℂ Y (acts _ x)=_; rw [hh]; simp_rw [act_sum,inner_sum]; nth_rw 2 [← basis_expand x]; rw [map_sum]; apply sum_congr rfl; intro j _
 rw [act_smul,inner_smul_right,hc,←act_inner,hY] -- delete hx
 rw [map_smul,hv, inner_smul_left, basis_inner]; change W i j*(star c*x.ofLp j)= (x.ofLp j)* O' i (basisKet j); unfold W; have hp:star c ≠0:= star_ne_zero.mpr pY; field_simp
end YM.CF.Reed
