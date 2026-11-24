import YM.CF.Nacre.Chart
import YM.CF.Nacre.Sift
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{m:ℕ}{n:Side}
abbrev InputZ (G:Gauge)(n:Side):= fieldDir G n 1
abbrev AimX(m:ℕ)(G:Gauge)(n:Side)(E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E]:=ContinuousMultilinearMap ℝ (fun _:Fin m=>InputZ G n) E
def Trot(n:Side) := Extra.Iteration.Channel.bondBody n
-- `cur` tree scrub
def fullG (x:Site n)(u:InputZ G n):InputZ G n := fun i=> (collect G u-pure (sap x (collect G u))) ((Trot n).symm i)
lemma sampleX(x:Site n)(u:InputZ G n):collect G (fullG x u)=collect G u-pure (sap x (collect G u)):=by funext i; change (collect G u-Font.pure (sap x (collect G u))) ((Trot n).symm ((Trot n) i))=_; rw [(Trot n).symm_apply_apply]
def put (G:Gauge)(n:Side)(x:Blip n): G.Color→L[ℝ]InputZ G n:=
 (show G.Color→ₗ[ℝ] InputZ G n from { toFun:=fun u=>Pi.single (Trot _ x) u,map_add':=fun a b=> by ext1 i; by_cases p:i=Trot _ x<;> simp [p,Pi.single_apply],map_smul':=fun a b=>by ext1 i; by_cases p:i=Trot _ x<;> simp [p,Pi.single_apply, RingHom.id_apply]}).toContinuousLinearMap
lemma put_sum(X:InputZ G n):X=∑ u: Blip n,put G n u (collect G X u):=by
 funext p; obtain ⟨p,rfl⟩:= (Trot n).surjective p; rw [Finset.sum_apply]; change _=∑ u:Blip n, Pi.single (M:=fun _=> G.Color) (Trot n u) (_ : G.Color) (Trot n p); simp [Pi.single_apply]; rfl
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def timeA (L:AimX m G n E)(f:Fin m→ Blip n): ContinuousMultilinearMap ℝ (fun _: Fin m=>G.Color) E:= L.compContinuousLinearMap fun i=> put G n (f i)
def tiltV(x:Site n)(L:AimX m G n E)(a R:ℝ):ℝ:= ∑ v: Fin m→ Blip n, Real.exp (a*(R+∑ i, (separation x (v i).1:ℝ))) * ‖timeA L v‖
private lemma stitch (T:AimX m G n E)(A:InputZ G n):Tensor.diagonal T A = ∑ u: Fin m→ Blip n,timeA T u (fun i=> collect G A (u i)):=by
 unfold Tensor.diagonal; conv_lhs => rw [put_sum A]
 rw [ContinuousMultilinearMap.map_sum]; rfl
private lemma mapH(x: Site n)(Y:Blip n→Wind n→ℝ)(J:AimX m G n E)(p:∀ (A:InputZ G n),∀ e:Blip n, collect G (fullG x A) e =∑ i,Y e i • heat x (collect G A) i) (A:InputZ G n) :
 Tensor.diagonal J (fullG x A)= ∑ v: Fin m→ Wind n, (∑ F: Fin m→ Blip n,(∏ i,Y (F i) (v i)) • timeA J F) (fun i=> heat x (collect G A) (v i)):=by
 rw [stitch]; simp only [_root_.sum_apply,_root_.smul_apply]; rw [sum_comm (s:= (univ:Finset (Fin m→Wind n)))]; refine sum_congr rfl fun i _=> ?_; simp_rw [p,ContinuousMultilinearMap.map_sum]; refine sum_congr rfl fun j _=> ?_; rw [ContinuousMultilinearMap.map_smul_univ]
def stare(m:ℕ)(x: Site n)(R:ℝ)(p:Fin m → Wind n):= R+∑ i,(dial x (p i):ℝ)
lemma ration (a:ℝ)(p:0<a)(m:ℕ):∃ η K:ℝ,0<η∧0<K∧ ∀ {G:Gauge}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}(x:Site n)(T:AimX m G n E)(R:ℝ),0≤R→∃ W: (Fin m→ Wind n)→ContinuousMultilinearMap ℝ (fun _:Fin m=>G.Color) E,(∑ i,nick η (stare m x R i)*‖W i‖) ≤ K*tiltV x T a R ∧ ∀ A:InputZ G n, Tensor.diagonal T (fullG x A)= ∑ p, W p (fun i=> heat x (collect G A) (p i)) :=by
 let b:=a/4; have hb:0<b:=by unfold b; positivity
 let l:=b/18; have hl:0<l:=by unfold l; positivity
 let B:=400* Iteration.momentPrice 2 b; have hB:0<B:=mul_pos (by norm_num) (Iteration.momentPrice_pos _ hb)
 let H:= taxH (2*l)*Real.exp (2*l*10*m)
 have hH:0<H:=by unfold H taxH; exact mul_pos (Iteration.momentPrice_pos _ (by linarith)) (Real.exp_pos _)
 refine ⟨l,H*B^m,hl,by positivity,?_⟩
 intro G E _ _ n x T R hr
 choose f h v Q using funnel G.Color x
 let F (i:Fin m→Wind n)(d:Fin m→Blip n):=(∏ k,f (d k) (i k)); let W(i:Fin m→ Wind n): ContinuousMultilinearMap ℝ (fun _:Fin m=> G.Color) E:=∑ d: Fin m→ Blip n, F i d • timeA T d; refine ⟨W,?_,mapH x f _ (fun y e=> by rw [sampleX]; exact Q _ _)⟩
 let U(p:Fin m→Wind n)(d:Fin m→ Blip n):=nick l (stare m x R p)*‖F p d • timeA T d‖
 have hm(d:Blip n): ∑ i, |f d i| ≤ B*Real.exp (b*separation x d.1):=by
    apply (h _).trans
    unfold B Font.slope; let z:ℝ:= separation x d.1; have he:0≤z:=Nat.cast_nonneg _
    have hh:=Iteration.spendMoment 2 hb he
    push_cast; change _≤ 400*_ * Real.exp _; rw [mul_assoc]; refine le_trans (b:=400*(1+z)^2) ?_ (by gcongr)
    change 4*(9*(z+1)+1)^2≤ _; nlinarith
 apply le_trans (sum_le_sum (g:=fun i=>∑ d: Fin m→ Blip n,U i d) (fun i (_:i∈(univ:Finset _))=>?_)) ?_
 swap
 · unfold U; rw [← Finset.mul_sum]; refine mul_le_mul_of_nonneg_left (norm_sum_le ..) (nick_pos _ ?_|>.le); unfold stare; positivity
 rw [sum_comm]; unfold tiltV; rw [mul_sum]; refine Finset.sum_le_sum fun d _=>?_
 let Z:= (∑ i:Fin m,(separation x (d i).1:ℝ)); have hz:0≤Z:=Finset.sum_nonneg fun _ _=>Nat.cast_nonneg _
 have he(i:Fin m→Wind n)(h:F i d ≠0): stare m x R i ≤ R+9*Z+10*m:=by
    have ht(j:Fin m): (dial x (i j):ℝ) ≤ 9* (separation x (d j).1 : ℕ) + 10:=by
       have hp:=v (d j) (i j) (fun e=> h (prod_eq_zero (mem_univ j) e)); unfold Font.slope at hp; exact_mod_cast show _ ≤9*separation x (d j).1+10 from (by omega) -- tune
    have hx:=sum_le_sum (fun i (_:i∈univ)=> ht i); simp only [sum_add_distrib,← Finset.mul_sum,sum_const,card_univ, Fintype.card_fin, nsmul_eq_mul] at hx; unfold stare Z; nlinarith only [hx]
 let V:= H*Real.exp (b*(R+Z)); have hv:0<V:=mul_pos hH (Real.exp_pos _)
 have hf : ∑ i, |F i d| ≤ B^m* Real.exp (b*Z):=by
    calc
     _ = ∏ k: Fin m,(∑ i:Wind n,|f (d k) i|):=by unfold F; simp_rw [Finset.abs_prod]; exact (Finset.prod_univ_sum (fun k:Fin m=> (univ:Finset (Wind n))) (fun k i=> |f (d k) i|)).symm
     _ ≤ ∏ k: Fin m, B* Real.exp (b*separation x (d k).1):=Finset.prod_le_prod (fun i _=>sum_nonneg fun j _=>abs_nonneg _) (fun i _=>hm _)
     _ = _:=by rw [Finset.prod_mul_distrib, ←Real.exp_sum, ← Finset.mul_sum,prod_const,card_univ,Fintype.card_fin]
 calc
   _ ≤ V*(∑ i:Fin m→Wind n,|F i d|)* ‖timeA T d‖:=by
     rw [mul_sum,sum_mul]; refine sum_le_sum ?_; intro i _; unfold U; rw [norm_smul,Real.norm_eq_abs,←mul_assoc]; by_cases q:F i d=0; · simp [q]
     apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); apply (nick_inc hl.le (by unfold stare; positivity) (he i q)).trans; refine (dentH (a:=2*l) (by positivity) (by linarith) (by positivity)).trans ?_; unfold V H; rw [mul_assoc (taxH _),← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (Iteration.momentPrice_pos _ (by linarith) |>.le); apply Real.exp_monotone; unfold l; nlinarith
   _ ≤ _:=by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hv.le) (norm_nonneg _)).trans; change _≤ (H*_)* (Real.exp (a*(R+Z))*‖_‖)
    have hx: Real.exp (b*(R+Z))* Real.exp (b*Z)≤ Real.exp (a*(R+Z)):= by rw [←Real.exp_add]; apply Real.exp_monotone; unfold b; nlinarith
    unfold V; calc
      _ = H*B^m*(Real.exp (b*(R+Z))*Real.exp (b*Z))*‖timeA T d‖:=by ring
      _ ≤ _:=by rw [←mul_assoc (H*_) (Real.exp (a*_))]; gcongr
end YM.CF.Nacre
