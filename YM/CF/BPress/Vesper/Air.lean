import YM.CF.BPress.Vesper.Sail
/-! B-Jrep Fourier in full integral. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Cube Lat SU Spin Spin.Paint Chalk Lily Skye Scree Branch Tenant DoughBag Tulip Dial Wheel --
variable {N: Side}(V: Site N→ℂ)(A:PanelA N)
def dpanel : PanelA N:= ⟨fun i=>1+ V i • A.val i,fun i=> Sector.one.add ((A.property i).scale _)⟩
variable (S:Support N)
abbrev segP (V:Site N→ℂ)(T:Support N) := ∏ i∈T,V i
theorem expansionO:tomes S (dpanel V A)=∑ i∈S.powerset,segP V i • tomes i A:=by
 induction S using Finset.induction_on with| empty=> simp [segP]|@insert i S h ih=>
  rw [brick _ _ i h, ih, sum_powerset_insert h]; change ( (1:FC (Single N))+ V i • _)*_= _; rw [add_mul, one_mul,mul_sum]; apply congrArg; apply sum_congr rfl; intro T v; have e:i∉T:=mt (fun w=>mem_powerset.mp v w) h; rw [show segP V (insert i T)=V i*segP V T from prod_insert e,brick _ _ _ e, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_smul] -- tune powerset order
variable (ε:ℂ)
def yKick(y:ActY N)(i:Site N):ℂ:=if i∈ S then ε*(y i:ℂ) else 0
lemma wfi (s:Support N) (b:s ∈ S.powerset)(Y:ActY N): segP (yKick S ε Y) s= Wheel.ζ s Y*ε^s.card:= by
 unfold segP; rw [prod_congr rfl (g:=fun i=>(Y i:ℂ)*ε) (by intro i w; rw [yKick,if_pos (mem_powerset.mp b w),mul_comm]), prod_mul_distrib,prod_const]; rfl
variable (a b: Wave (Single N))
lemma concert (x:ActY N): spinInner a b (tomes univ (dpanel (yKick S ε x) A))=∑ t∈ S.powerset,Wheel.ζ t x * (ε^t.card*spinInner a b (tomes t A)):=by
 let T:=dpanel (yKick S ε x) A; rw [show tomes univ T=tomes S T from ?_]; swap
 · have he:T=pal S T:=by apply Subtype.ext; funext i; by_cases h:i∈S; exact (if_pos h).symm; change _= if i∈S then _ else _; rw [if_neg h]; change 1+ yKick S ε x i • _= _; rw [yKick,if_neg h,zero_smul,add_zero]
   nth_rw 1 [he]; rw [Chalk.rent,univ_inter]
 unfold T; rw [expansionO,spinInner,act_sum,inner_sum]; apply sum_congr rfl; intro i u; rw [wfi S ε i u x, act_smul,inner_smul_right, mul_assoc] -- tune args A absent
variable {P Q:Paint (More N)} {T U W: Support N}(X: Vase P Q T U W)(R:GramM N)(f:Orbit N)(H:Op (Single N))(Z:ActY N)(c:Rod N)
abbrev bill_phase (ε:ℂ)(Z:ActY N)(W:Support N):= (Wheel.ζ W Z)⁻¹ * (ε⁻¹)^W.card -- tune implicit
include X
lemma windY (t:ε≠0): (∫ x,bill_phase ε x W * spinInner (holdα T P) b (tomes univ (oceans P Q (yKick W ε x) U))∂coin (Site N))=inner ℂ (holdα U Q) b:=by
 let F(t):=ε^(t:Support N).card*spinInner (holdα T P) b (tomes t (byJ P Q U)); have he(p:ActY N): oceans P Q (yKick W ε p) U=dpanel (yKick W ε p) (byJ P Q U):=rfl; simp_rw [he,concert, bill_phase]; rw [show (∫ x:ActY N,_∂coin (Site N))=ε⁻¹^W.card*(∫ x,(Wheel.ζ W x)⁻¹ *(∑ t∈W.powerset, Wheel.ζ t x * F t)∂coin (Site N)) from ?_, show (∫ x,(Wheel.ζ W x)⁻¹ *(∑ t∈W.powerset, Wheel.ζ t x * F t)∂coin (Site N))=_ from order_f W.powerset (fun x=>x) W F]; -- tune
 · simp only [sum_ite_eq',mem_powerset,ite_true, Subset.refl]; unfold F; rw [inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ t)]; exact redeem X b
 rw [← integral_const_mul]; apply integral_congr_ae; apply Eventually.of_forall; intro x; dsimp only; rw [mul_comm (Wheel.ζ W x)⁻¹, mul_assoc]
abbrev engross (P Q: Paint (More N))(T U W:Support N):= bill_phase ε Z W * spinInner (holdα T P) b (opus R f 1 (ringF c) P Q H (yKick W ε Z) U)
lemma sky (t:ε≠0): (∫ x,engross ε b R f H x c P Q T U W∂coin (Site N))=spinInner (holdα U Q) b (strength R f 1 (ringF c) H):=by unfold engross spinInner opus; simp_rw [act_mul]; exact windY ε _ X t -- tune
lemma phase_integral (p:ε≠0)(h:IsStarProjection H): spinInner (holdα U Q) b (tank H (R.board f))= ∫ z: Rod N, (Wheel.ζ (trueFlags R f) z)⁻¹ * (∫ x, engross ε b R f H x z P Q T U W ∂coin (Site N)) ∂coin (Site (More N)):= by simp_rw [sky ε _ X R f H _ p]; exact (discharge R f H _ b h).symm -- tune wildcard simp_rw
end YM.CF.BPress.Vesper
#print axioms YM.CF.BPress.Vesper.phase_integral
