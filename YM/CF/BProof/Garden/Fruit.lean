import YM.CF.BProof.Garden.Pollen
import YM.CF.Scree.Locus
import YM.CF.Pastry.Bliss
/-! Phase integral eq:B-Oexpect, recovering the single physical pairing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset MeasureTheory Lattice Lat Spin Tulip Tenant
open Cube Dial Scree Skye Pastry
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator ENNReal ComplexConjugate Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
def whole (D:GramM N)(x:Orbit N): Cipher N:= exponentL D.p D.F x.1 + exponentL D.p D.slip x.1
def fair (i:Finset (Force N)):= Set.PairwiseDisjoint (i:Set _) (fun x:Force N=> x.val.1.val.2)
noncomputable scoped instance (i:Finset (Force N)):Decidable (fair i):=Classical.propDecidable _
lemma fairLess {i:Finset (Force N)}(f:fair i): Set.PairwiseDisjoint (i:Set _) (fun x:Force N=> x.val.2):=fun j u k v e=>(f u v e).mono j.property.2 k.property.2
abbrev corn(i:Finset (Force N)):= i.biUnion fun j=> j.val.2
def aster (D:GramM N)(x:Orbit N)(f:Pollen (Site (More N)))(j:Force N): Cipher N:= hollow (style j.val.2 f)*Scree.clamp D.p j (D.K j) x
def red (D:GramM N)(x:Orbit N)(f:Pollen (Site (More N))): Cipher N:= ∑ i:Finset (Force N), if fair i then ∏ j∈i,aster D x f j else 0
def boardF (D:GramM N)(x:Orbit N)(f:Pollen (Site (More N))) := exp (whole D x)*red D x f
lemma hullOne{I:Type*}[Fintype I][LinearOrder I]:Pastry.hollow (n:=I) 1=1:=Subtype.ext (one_smul ..)
lemma hullMul{I:Type*}[Fintype I][LinearOrder I](c d:ℂ) : hollow (n:=I) (c*d)=hollow c * hollow d:= Subtype.ext (show (c*d) • (1:FC I)= (c • (1:FC I))*(d • (1:FC I)) from (by rw [mul_smul,Algebra.smul_mul_assoc,one_mul]))
lemma asters (D:GramM N)(x:Orbit N)(f:Pollen (Site (More N)))(i:Finset (Force N))(g:fair i): (∏ j∈i,aster D x f j)= hollow (style (corn i) f) * (∏ j∈i,Scree.clamp D.p j (D.K j) x):=by
 unfold aster; rw [prod_mul_distrib]; congr 1; unfold corn; induction i using Finset.induction_on with
 | empty=> simp only [prod_empty,biUnion_empty,style_zero,hullOne] -- tune
 | insert y i hi ih=>
   rw [prod_insert hi, ih (show fair i from Set.Pairwise.mono (coe_subset.mpr (subset_insert ..)) g), biUnion_insert, monet,hullMul]; rw [disjoint_biUnion_right]; intro j hj; exact fairLess g (show y∈ (↑(insert y i):Set _) from mem_insert_self ..) (show j∈ (↑(insert y i): Set _) from mem_insert_of_mem hj) (by rintro rfl; contradiction)
lemma zscore(D:GramM N)(x:Orbit N){P:Op (Single N)} (h:IsStarProjection P)(Y R: Wave (Single N)) : (∫ f,star (style (RG.flags D.p.threshold x.1) f)*inner ℂ Y (acts (tank P (boardF D x f)) R) ∂gold (Site (More N)))=inner ℂ Y (acts (tank P (D.board x)) R):=by
 let M:=Orbit N; let V:= nursery P h; let A: Finset (Site (More N)) := RG.flags D.p.threshold x.1; let T:=Finset (Force N); let G:= whole D x; let K(i:Finset (Force N)):= exp G * (∏ j∈i,Scree.clamp D.p j (D.K j) x); let Ω(i:Finset (Force N)):= inner ℂ Y (acts (V.cook (K i)) R); let X(f:Pollen (Site (More N))) (i:T):ℂ:= if fair i then style (corn i) f*Ω i else 0; have hx(f): inner ℂ Y (acts (tank P (boardF D x f)) R) = ∑ i:T,X f i:=by
    unfold boardF red; rw [tank_eq P _ h,mul_sum,map_sum,act_sum,inner_sum]; apply sum_congr rfl; intro i _; unfold X; split; rename_i g; · rw [asters D x f i g,mul_left_comm (exp _),map_mul,cookH, Algebra.smul_mul_assoc,one_mul,act_smul, inner_smul_right]; -- tune cod
    rw [mul_zero,map_zero,act_zero,inner_zero_right]
 let W(i: Finset (Force N))(f:Pollen (Site (More N))):ℂ:= star (style A f)*X f i; simp_rw [hx,mul_sum]; change (∫ f,∑ i,W i f ∂_)=_; rw [integral_finsetSum]; unfold GramM.board fueled; rw [tank_eq P _ h,mul_sum,map_sum,act_sum,inner_sum]; apply sum_congr rfl
 · intro i _; unfold W X; by_cases k:fair i; · simp only [k,if_true]; rw [show (∫ f, star (style A f)* (style (corn i) f*Ω i) ∂gold (Site (More N)))=(if A=corn i then 1 else 0)*Ω i from (by simp_rw [← mul_assoc]; rw [integral_mul_const,poppy])]; by_cases u:A=corn i; rw [if_pos u,if_pos ⟨u.symm,k⟩,one_mul]; rfl; rw [if_neg u,if_neg (fun t=>u t.1.symm),mul_zero,map_zero,act_zero,inner_zero_right,zero_mul]
   simp only [k,if_false,mul_zero]; rw [if_neg (fun t=>k t.2),mul_zero,map_zero,act_zero,inner_zero_right]; exact integral_zero .. -- tune
 intro i _; apply cIntegrable; unfold W X; by_cases f:fair i<;>simp only [f,↓reduceIte]<;> fun_prop
abbrev Fields (N:Side):= Pollen (Site (More N))×Pollen (Site N)
def outFuel (D:GramM N)(x:Orbit N)(Z:Pollen (Site (More N))):ℂ:=star (style (RG.flags D.p.threshold x.1) Z)
def outPay (ε:ℂ)(M:Support N)(y:Pollen (Site N)):ℂ:=ε⁻¹^M.card*star (style M y)
def values (D:GramM N)(x:Orbit N)(P:Op (Single N))(ε:ℂ)(S:Support N)(J:Plant N)(R Y:Phys N)(f:Fields N):ℂ:= inner ℂ Y (acts ((optional ε f.2 J).prod S) (acts (tank P (boardF D x f.1)) R))
def gardenF(N:Side):Measure (Fields N):= (gold (Site (More N))).prod (gold (Site N))
instance : IsProbabilityMeasure (gardenF N):= by unfold gardenF; infer_instance
@[fun_prop] lemma hollow_cont {I:Type*}[Fintype I][LinearOrder I] : Continuous (hollow (n:=I)):=Continuous.subtype_mk (continuous_id.smul continuous_const) _
@[fun_prop] lemma board_cont(D:GramM N)(x:Orbit N):Continuous (boardF D x):=by
 have ht(i:Force N):Continuous (fun f=>aster D x f i):= ((hollow_cont (I:=LeanV (Single N))).comp (style_cont i.val.2)).mul continuous_const
 unfold boardF red; apply Continuous.mul (f:=fun _=>exp _) continuous_const; apply continuous_finsetSum; intro i _; split; exact continuous_finsetProd _ (fun j _=>ht j); exact continuous_const
@[fun_prop] lemma optionalCont(ε:ℂ)(S:Support N)(J:Plant N): Continuous (fun y=> (optional ε y J).prod S):= by
 simp_rw [fluffy]; fun_prop
lemma contV (D:GramM N)(x:Orbit N){P:Op (Single N)}(h:IsStarProjection P)(ε:ℂ)(S:Support N)(J:Plant N)(R Y:Phys N): Continuous (values D x P ε S J R Y):=by
 unfold values; simp_rw [tank_eq P _ h]; exact continuous_const.inner ((acts_cont.comp ((optionalCont ε S J).comp continuous_snd)).clm_apply ((acts_cont.comp ((Poly.cookC _).comp ((board_cont D x).comp continuous_fst))).clm_apply continuous_const))
theorem pollinated (D:GramM N)(x:Orbit N){P:Op (Single N)}(h:IsStarProjection P)(ε:ℂ)(e:ε≠0)(p s u:Support N)(d:Disjoint u p)(A B: Quilt N)(v:∀ i,SealH (A i))(g:∀ i∉p,(cbra A u).leaf i=(cbra B sᶜ).leaf i)(R:Phys N) : (∫ f:Fields N,outFuel D x f.1 * outPay ε p f.2 * values D x P ε p (siteJ A (cbra B sᶜ)) R (cbra A u).ket f ∂gardenF N) = inner ℂ (mateK N) (acts ((Madd B).prod s) (acts (tank P (D.board x)) R)):=by
 rw [gardenF,integral_prod]; · simp_rw [mul_assoc (outFuel D x _),integral_const_mul]; unfold outPay values; simp_rw [issue ε e,←act_inner ((siteJ A (cbra B sᶜ)).prod p),issueJ p sᶜ u d A B v g]; unfold outFuel; rw [zscore D x h, ←act_inner ((Madd B).prod s),desired]
 apply cIntegrable; unfold outFuel outPay; have he:=contV D x h ε p (siteJ A (cbra B sᶜ)) R (cbra A u).ket; fun_prop
end YM.CF.BProof.Garden
