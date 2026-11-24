import YM.CF.Leaf.Loft
import YM.CF.Rive.Boil
import YM.CF.Rive.Grid
import YM.CF.Rive.Wally
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
lemma puff_C (G:Copy N)(X:Aura N)(D:Support (Cube.More N))(i:ℂ)(p:Stax.Fray P H δ X D G c) : Stax.Fray P H δ X D (i • G) (‖i‖*c):=by
 obtain ⟨L,Y⟩:=p; obtain ⟨M,c,p,v,t⟩:=L; refine ⟨⟨⟨fun i' j v' h=>congrArg (i • ·) (M.same i' j v' h),fun x=>(M.lit _).smul _,M.keeps.const_smul _,?_⟩,‖i‖ • c,fun k=>mul_nonneg (norm_nonneg _) (p k),fun V h F ht=> ⟨Eventually.of_forall fun j=> (fineShape _).allP,fun k=>((v V h ht).haveP k).σ i⟩,?_⟩,fun x p=> Y x (fun g=>p (by rw [Pi.smul_apply,g,smul_zero]))⟩
 · intro x q; rw [Pi.smul_apply,Pi.smul_apply,M.gaugeX]; apply Subtype.ext; change i • _=sauce false false _ (i • _); rw [sauce,singT,win_c, twist_scalar]; rfl
 unfold joinV; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖i‖,←mul_sum]; exact mul_le_mul_of_nonneg_left t (norm_nonneg _)
variable (S:ι→Bag N)(Q:ι→ Aura N→ℝ)(p:∀ i,Bias δ (S i) P H (Q i))(w:Key ι)(hp:w∈hill ι)
abbrev focusC (Γ:ι→Rinse (Seat N) (Copy N))(w:Key ι)(X:Aura N)(D:Support (Cube.More N))(Y:Aura N)(F:Copy N):= ∑ i:ι,w i • Γ i X D Y F
abbrev θlens:= focusC (fun i=> (p i).payX) w
abbrev κsum(X:Aura N):=∑ i:ι,Q i X
abbrev τlens(x:Orbit N)(X:Aura N): FC (Dwell N):=∑ i:ι,w i • S i X x
variable (hB:3 ≤ P.B)
include hv hB hp p
lemma paceΨ : Pitch P H δ (θlens S Q p w) (κsum Q) (τlens S w):=by
 have hu(i):= (p i).buys hB (zero_le_one.trans hv)
 refine ⟨fun x=>sum_nonneg fun i _=> (p i).weight x,fun X D Y=>?_,fun X D f Y h u z v=>?_ ,fun i Y=> Sector.sumS _ _ (fun j _=> ((p j).valid _ _).scale _),?_⟩
 · exact sum_eq_zero (fun i _=>by simp only [(hu i).start,smul_zero])
 · have ht:= Fray.sumP (δ:=δ) univ _ _ fun i _=>puff_C _ _ _ (w i) ((hu i).plays _ _ f _ h _ z v); refine ⟨ht.merit.big ?_, ht.loaf⟩; unfold κsum; rw [sum_mul]; apply sum_le_sum; intro i _; refine le_trans (mul_le_mul_of_nonneg_right (hill_i.mp hp _) (mul_nonneg ((hu i).dice _) (v.merit.wage (zero_le_one.trans hv)))) ?_; rw [one_mul]
 intro X Y i h z u F _D l; let D:=flags P.threshold i.1∩ X.val; have hx(j):=((hu j).body X Y i h z _ F l); change ((∑ j:ι,w j • (p j).payX X D Y F) i).val=_; rw [Finset.sum_apply]; let V:Copy N:=F; change (Dough (Dwell N)).val (∑ j:ι,w j • _) = Sault.rind (_*_); rw [map_sum]; unfold τlens Sault.rind; rw [sum_mul,map_sum]; apply sum_congr rfl; intro j _; rw [Algebra.smul_mul_assoc, map_smul ((Pastry.cane _).eval)]; exact congrArg (fun k:FC (Dwell N)=>w j • k) (hx j)
omit hp hv hB
variable (σ:ι→Seat N)(pS:∀ i X,σ i∉X.val→ S i X=0)(V:Orbit N)(B':Ids N)
variable (ht:∀ i,∀ X Y:Aura N,X.val⊆Y.val→∀ V, V.1∈ Sour.σX P Y ∅ →∀ A:Ids N,S i X (V.1,A)= S i X V)
include pS ht
lemma veer_K (X Y:Aura N)(F G:Copy N)(t:F (V.1,B')=G V): θlens S Q p w X ∅ Y F (V.1,B')= θlens S Q p w X ∅ Y G V:=by unfold θlens focusC; simp_rw [Finset.sum_apply]; exact sum_congr rfl (fun i _=> congrArg (w i • ·) (opva _ V (p i) (ht i) _ X Y F G t))
lemma hut_Y(X Y:Aura N)(D:Support (Cube.More N))(F:Copy N): Hush σ Y.val (fun w=> θlens S Q p w X D Y F):=by
 intro v _ w _ h; refine sum_congr rfl fun i _=>?_ ; by_cases t:σ i∈Y.val; · exact congrArg (fun v:ℂ=>v • _) (h i t) -- tune
 have hz:(p i).payX X D Y F=0:=by
    by_cases he:Bias.αt Y X D δ; swap; · unfold Bias.payX; rw [dif_neg he]
    funext V; apply Subtype.ext; change _=(0:Cipher N).val; rw [(p i).truth _ _ _ _ he V]; have h:coll_T P X D (S i Y) V=0:=by unfold coll_T; split; rw [pS _ _ t]; rfl; rfl
    rw [h,zero_mul,Sault.rind,map_zero]; rfl
 simp only [hz,smul_zero,smul_zero]
omit pS ht
omit p
lemma r_sm {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y][CompleteSpace Y](G: Key ι→Y)(u:River G)(i:ι): River (fun w:Key ι=> w i • G w):=by
 refine ⟨((continuous_apply i).continuousOn.smul u.shore) -- tune
 ,fun v p j a t=>?_⟩
 have h: DifferentiableAt ℂ (fun w=>update v j w i) a:=by by_cases h:i=j; subst j; simp_rw [Function.update_self]; exact differentiableAt_id; simp_rw [update_of_ne h]; exact differentiableAt_const _
 exact h.smul (u.slope v p j a t)
include p
lemma rent_X (F: Key ι→ Copy N)(h:River (fun i=>F i V))(X Y:Aura N)(D:Support (Cube.More N)):River (fun i:Key ι=> θlens S Q p i X D Y (F i) V):=by
 simp_rw [θlens,focusC,Finset.sum_apply]; apply tick_sum; intro i _; exact r_sm _ (Rive.tariffP _ V (p i) X D F h Y) _
lemma rule_ζ (X Y:Aura N)(F:Key ι→ Copy N)(h:River (fun i=>F i V)):River (fun v=> ζA (θlens S Q p v) X Y (F v) V):=by
 unfold ζA; simp_rw [Pi.sub_apply,Pi.mul_apply]; refine (dub_V (rent_X _ _ _ _ _ h (αK X Y) X ∅) (yorkB _ ?_ )).cong (fun i _=>sub_eq_add_neg ..) -- tune
 apply River.mul_T h; exact rent_X S Q p V _ (zeroR _) _ _ _
lemma rule_κ(X Y Z:Aura N)(F G:Key ι→ Copy N)(he:River (fun i=>F i V))(hv:River (fun i=>G i V)):River (fun v=> κA (θlens S Q p v) X Y Z (F v) (G v) V):=by
 let U:=αK (αK X Y) Z; let K'(v F):=go_K (X:=U) (θlens S Q p v) X F; let ZF(v):=F v*G v
 let pK(f:Key ι→ Copy N)(t:River (fun v=>f v V)):= rent_X S Q p V f t U X ∅
 let x:= pK F he; let y:=pK G hv; let v:=pK ZF (River.mul_T he hv); let t:= pK (fun _=>1) (show River (fun _:Key ι=>(1:Copy N) V) from zeroR _)
 let k:=River.mul_T (River.mul_T hv he) t
 simp only [κA]; simp_rw [Pi.smul_apply,Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; apply Rive.bScale
 refine dub_V ?_ k; exact Rive.river_minus _ _ (Rive.river_minus _ _ v (River.mul_T he y)) (River.mul_T hv x)
end YM.CF.Leaf
