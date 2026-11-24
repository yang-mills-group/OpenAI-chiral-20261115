import YM.CF.Pec.Denim
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n X m A L B :Side}{j k:ℕ}{ho:Odd L.val} {Y:Pricing j L ho (Thread j)}{e d b a r:ℝ}{P:Grasp Y B e}
structure Vale (f:Cloud n→ℂ):Prop where
 life (g:E)(x:Cloud n):∀ᶠ t in 𝓝 (0:ℝ),f (t • MarkT g x)=f (t • x)
 pier(x:Cloud n)(z:Site (More n)):∀ᶠ t in 𝓝 (0:ℝ), f (race z x t)=f (t • x)
lemma Vale.invariant{f:Cloud n→ℂ}(v:Vale f)(h:cFoot k f)(p:ContDiffAt ℝ k f 0)(x:Cloud n): (∀ z:Site (More n),trim k f (fullG z x)=trim k f x)∧∀ t:E,trim k f (MarkT t x)=trim k f x:=by
 have hp:= (argent p).mp h; constructor; intro z; apply tendsto_nhds_unique (flares (race z x) p ((sport z x).of_le le_top) _ (roundS ..) (tough ..) h); refine (hp x).congr' ?_; filter_upwards [(v.pier x z).filter_mono nhdsWithin_le_nhds] with t ht; rw [ht]
 intro t; apply tendsto_nhds_unique (hp (MarkT t x)); refine (hp x).congr' ?_; filter_upwards [(v.life t x).filter_mono nhdsWithin_le_nhds] with t ht; rw [ht]
lemma Vale.first{f:Cloud n→ℂ}(v:Vale f)(h:f 0=0)(p:ContDiffAt ℝ 1 f 0) : cFoot 2 f:=by
 have ht : cFoot 1 f:= by intro i hi; rw [show i=0 from by omega]; ext1 x; rw [iteratedFDeriv_zero_apply,h]; rfl
 let A:=fderiv ℝ f 0; have hp(x:Cloud n): trim 1 f x= A x:=by simp only [trim,cake,Tensor.diagonal,Nat.factorial]; simp [A]
 have hq (t:E)(x:Cloud n): A (MarkT t x)=A x:=by rw [←hp,←hp]; exact (v.invariant ht (by norm_cast) x).2 t -- normcast
 have hu (i: Body 1 (More n))(x: CoreX): A (Pi.single i x)=0:=by
    let V(i):=LinearMap.single (R:=ℝ) (φ:=fun _:Body 1 (More n)=>CoreX) i
    let X:=A.toLinearMap.comp (V i); have he:X=0:=by apply StressFlux.linear_invariant yet_one X; intro g u; change A (Pi.single i (group.adjoint g u))= _; rw [←show MarkT g (Pi.single i u)= Pi.single i _ from ?_]; exact hq g _; ext1 j; by_cases h:j=i<;>simp [h,Pi.single_apply,MarkT] -- tune
    exact DFunLike.congr_fun he x
 have hx: trim 1 f=0:=by
    funext x; rw [hp]; have hx:x=∑ i,Pi.single i (x i):=by ext1 i; rw [Finset.sum_apply]; simp [Pi.single_apply]
    nth_rw 1 [hx]; rw [map_sum]; simp [hu]
 apply nextF (m:=1) (by exact_mod_cast p); rw [←hx]; exact (argent (by exact_mod_cast p)).mp ht
open MeasureTheory
def dawn (P:HtX k)(g:E):HtX k:= P.compContinuousLinearMap fun _=> (group.adjoint g).toContinuousLinearMap
lemma glaze_A(c:CoreX):Continuous fun g:E=> group.adjoint g c:=by
 simp only [Gauge.adjoint,LinearMap.coe_mk,AddHom.coe_mk, Gauge.conjugate]; apply group.projectColor.continuous_of_finiteDimensional.comp (f:=fun g:E=> _ * _ * _); fun_prop
def deer (P: HtX k):HtX k:=∫ i:E,dawn P i ∂group.probHaar
lemma dawn_U(P:HtX k):Continuous (dawn P):=punctual _ fun v=> P.contDiff (n:=ω) |>.continuous.comp (f:=fun g:E=> (fun i=>group.adjoint g (v i))) (continuous_pi fun i=>glaze_A (v i)) -- tune args
lemma deer_u(P:HtX k)(x:Fin k→CoreX):deer P x=∫ g:E, P (fun i=> group.adjoint g (x i)) ∂group.probHaar:= ((ContinuousMultilinearMap.apply ℝ (fun _:Fin k=> CoreX) ℂ x).integral_comp_comm ((dawn_U P).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
lemma deer_v(P:HtX k)(v: Fin k→CoreX)(g:E):deer P (fun i=>group.adjoint g (v i))=deer P v:=by rw [deer_u,deer_u]; simp_rw [←group.adjoint_mul]; exact integral_mul_right_eq_self (μ:=group.probHaar) (fun x=> P (fun i=>group.adjoint x (v i))) g
lemma deer_h(P:HtX k):‖deer P‖≤ ‖P‖:=by
 have ht(g:E): ‖dawn P g‖≤ ‖P‖:=by apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; apply mul_le_of_le_one_right (norm_nonneg _); refine prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=> ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_); intro x; rw [one_mul]; exact (group.norm_adjoint g _).le
 apply (norm_integral_le_of_norm_le_const (μ:=group.probHaar) (ae_of_all _ ht)).trans_eq; simp
lemma deer_inner(P:HtX 2)(e:CoreX)(h:‖e‖=1)(x y:CoreX):deer P ![x,y]=inner ℝ x y • deer P ![e,e]:=by
 let A:=deer P; let G:= ((continuousMultilinearCurryFin1 ℝ CoreX ℂ).toLinearEquiv.toLinearMap).comp A.curryLeft.toLinearMap; let B:= (show (_→ₗ[ℝ]ℂ)≃ₗ[ℝ](CoreX→L[ℝ]ℂ) from LinearMap.toContinuousLinearMap).symm.toLinearMap.comp G -- tune
 have ht(x y:CoreX):A ![x,y]= B x y:=by
    change _= continuousMultilinearCurryFin1 ℝ CoreX ℂ (A.curryLeft x) y; rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]; congr 1; funext j; fin_cases j<;> simp
 change A _= inner ℝ x y • A _; rw [ht,ht]; refine StressFlux.bilinear_invariant yet_one B ?_ h x y; intro g x y; rw [←ht, ←ht]; exact ((show ![group.adjoint g x,group.adjoint g y]=fun i=>group.adjoint g (![x,y] i) from funext fun i=> by fin_cases i<;> rfl) ▸ deer_v P ![x,y] g) -- direction
private def couples(D:Type) :D× D ≃ (Fin 2→ D) :=⟨fun i=>![i.1,i.2],fun v=>(v 0,v 1),fun i=>rfl,fun v=> funext fun i=>by fin_cases i<;> rfl⟩
lemma clad(p:0<a):∃ b C:ℝ,0<b∧0<C∧∀ {n:Side}{f:Cloud n→ℂ}(x: Orig n), Vale f→ f 0=0→ ContDiffAt ℝ (↑(2:ℕ)) f 0→∀ w, tiltV x (cake 2 f) a 0 ≤ w →∃ T:Dues n,cents x T b≤ C*w∧ trim 2 f=datam x T:=by
 obtain ⟨b,D,hb,hD,U⟩:= ration a p 2; refine ⟨b,D,hb,hD,fun {n f} x v h he w g=>?_⟩
 obtain ⟨P,hq,F⟩:= U x (cake 2 f) 0 (by norm_num)
 haveI : Nontrivial CoreX := yet_one.nontrivial_color; obtain ⟨e,hw⟩:=exists_norm_eq CoreX zero_le_one
 let a:= couples (Ok n); let f':=trim 2 f
 let T:Dues n:=fun i j=> deer (P (a (i,j))) ![e,e]
 have hz:= v.first h (he.of_le (by norm_num))
 have hp(u): f' u=∑ i: Fin 2→Ok n,P i (fun j=>heat x (collect group u) (i j)):=by rw [←F]; exact ((v.invariant hz he u).1 x).symm -- tune
 refine ⟨T, hq.trans ((mul_le_mul_of_nonneg_left g hD.le)) |>.trans' ?_, funext fun y=>?_⟩
 · rw [←Equiv.sum_comp a, Fintype.sum_prod_type]; unfold cents; refine sum_le_sum fun i _=> sum_le_sum fun j _=> ?_; let Z:= P (a (i,j)); have hx:stare 2 x 0 (a (i,j))=contour x i j:=by simp [stare,Fin.sum_univ_two,a,couples]; rfl -- tune
   rw [hx]; apply mul_le_mul_of_nonneg_left _ (nick_pos _ (ct_pos ..) |>.le); unfold T; apply ((deer Z).le_opNorm _).trans; rw [Fin.prod_univ_two]; simpa [Z,hw] using (show ‖deer Z‖* (‖e‖ * ‖e‖)≤‖Z‖ by rw [hw,one_mul,mul_one]; exact deer_h _)
 let L(r: Fin 2→Ok n):= fun i=> heat x (collect group y) (r i)
 have hh : (∑ i: Fin 2→Ok n, deer (P i) (L i))= f' y:=by
    simp_rw [deer_u]; rw [←integral_finsetSum]; have hx(g:E):∑ i:Fin 2→Ok n,P i (fun j=> group.adjoint g (L i j))= f' y:=by
       rw [← (show f' (MarkT g y)= f' y from (v.invariant hz he y).2 g),hp]; unfold L; simp_rw [thump]
    simp [hx]
    intro i _; exact ((P i).contDiff (n:=ω)|>.continuous.comp (continuous_pi fun j=> glaze_A (L i j))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 change f' y=_; rw [←hh,← Equiv.sum_comp a, Fintype.sum_prod_type]; unfold datam; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; let X(i):=heat x (collect group y) i
 rw [show L (a (i,j))= ![X i,X j] from funext fun i=>by fin_cases i<;>rfl]; exact deer_inner _ _ hw _ _
end YM.CF.Pec
