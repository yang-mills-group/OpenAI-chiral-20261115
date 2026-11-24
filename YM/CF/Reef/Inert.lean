import YM.CF.Reef.Opus
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.CF.Reef
open Function Filter NormedSpace Lattice Lat Rush Fock Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Nacre Cube Thera Laic Matrix Finset
open scoped Topology InnerProductSpace Matrix MatrixOrder Kronecker ContDiff BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{k:ℕ}{b a:ℝ}{F:Toy k N}
def wages(F:Toy k N):Toy k N:=fun x y i=> (glare x.1.2*glare y.1.2) • (Complex.conjCLE.toContinuousLinearMap.compContinuousMultilinearMap ((F (twinE N x) (twinE N y) i).compContinuousLinearMap fun _=> frolic.toContinuousLinearMap))
lemma form_w(F:Toy k N)(x y:HopK N)(i:Font.Trip k N)(v) : Nacre.halo (wages F) x y i v = (glare x.2*glare y.2) • cc (Nacre.halo F (twinHop N x) (twinHop N y) i (frolic ∘ v)):=by rfl
lemma swanK(F:Toy k N)(x y:HopK N)(i:Font.Trip k N)(U:Bkg (More N)): mold (wages F) x y i U=(glare x.2*glare y.2) • cc (mold F (twinHop N x) (twinHop N y) i (echo U)):=by
 unfold mold walkB; have he(p): silt (terse (twinHop N x)) p (echo U)=frolic (silt (terse x) p U):=by unfold silt; rw [echo_t,swing]; rfl
 rw [form_w, cc_mul, echo_t,Matrix.smul_mul]; simp_rw [he]; rw [show ∀ x:E, (matter (qG x)).val= cc (matter x).val from matterX true,cc_cc]; rfl
lemma glitz(F:Toy k N)(U:Bkg (More N)): cavil (wages F) U=rally N (cavil F (echo U)):=by ext ⟨i,x⟩ ⟨j,y⟩; rw [riot_p]; simp only [cavil,Matrix.of_apply,swanK,Matrix.sum_apply]; rw [star_sum, Finset.smul_sum]; rfl -- tune
lemma riches(F:Toy k N)(U:Bkg (More N)): colorX (wages F) U=rally N (colorX F (echo U)):=by
 have ht(i): Yg (incX i) (echo U)=echo (Yg (incX i) U):=echo_p U _ _; unfold colorX sumU; rw [map_smul, map_sum]; congr 1; apply sum_congr rfl; intro i h; unfold foil; rw [glitz,rally_m, ht]
lemma arch_p(h:Prints F) : Prints (wages F):=by
 have he(i:Single N)(t): twinE N (ramH t i)=ramH t (twinE N i):=rfl
 intro t i j r; ext1 x; unfold wages; rw [he,he,h]; change (glare i.1.2*glare j.1.2) • star ((Rush.wind i.1.1 t*Rush.wind j.1.1 t) * _) = (Rush.wind i.1.1 t*Rush.wind j.1.1 t) • (_:ℝ) • star _; rw [star_mul',star_mul',show star (Rush.wind i.1.1 t)=_ from fee_real _,show star (Rush.wind j.1.1 t)=_ from fee_real _] -- tune
 exact smul_comm (glare i.1.2*glare j.1.2) (Rush.wind i.1.1 t*Rush.wind j.1.1 t) _
lemma wages_p(h:handy F): handy (wages F):=by
 intro i j r C u; rw [form_w, form_w]; unfold Function.comp; dsimp only; simp_rw [dip]; rw [h,map_smul,twist_formula,twist_formula,show (matter (qG _)).val=_ from matterX true u, cc_mul,cc_mul,cc_star]; simp [windX]
lemma guard_h(h:CardK N k F b a):CardK N k (wages F) b a:=by
 refine ⟨arch_p h.1, wages_p h.2.1,fun i=> le_trans ?_ (h.2.2 (twinE N i))⟩
 unfold balance; conv_rhs=> rw [←Equiv.sum_comp (twinE N)]
 refine sum_le_sum fun j _=> sum_le_sum ?_
 have he(i): ‖glare i‖=1:=by unfold glare; split<;>simp
 intro l _; rw [show notx k (twinE N i) (twinE N j) l=notx k i j l from rfl]; apply mul_le_mul_of_nonneg_left _ (nick_pos _ (notx_zero ..)|>.le)
 unfold wages; rw [norm_smul,norm_mul,he,he,one_mul,one_mul]
 apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..).trans; apply le_trans (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun (x:ℂ)=>by change ‖star x‖≤_; simp)) (norm_nonneg _)) _ -- tune
 rw [one_mul]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
 have ht: ∀ t : Fin k, ‖frolic.toContinuousLinearMap‖ ≤ 1:= fun _=>ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by simp)
 exact mul_le_of_le_one_right (norm_nonneg _) (prod_le_one (fun _ _=>norm_nonneg _) (fun j _=>ht j)) -- tune
private lemma roll_p (F:Toy k N)(z:ℝ)(v:Bkg (More N)):colorX (z • F) v=z • colorX F v:=by
 unfold colorX sumU; rw [smul_comm]; congr 1; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; unfold foil; rw [←map_smul]; congr 1; ext1 k j; change (∑ l,mold _ _ _ l _) _ _= _; have he(i u l x): mold (z • F) i u l x=z • mold F i u l x:=by unfold mold; rw [← Matrix.smul_mul]; rfl
 simp_rw [he]; rw [← Finset.smul_sum]; rfl
abbrev dolphin (F:Toy k N):= (2:ℝ)⁻¹ • (F+wages F)
def Neat(F:Toy k N):Prop:= ∀ x:Bkg (More N),colorX F (echo x) = rally N (colorX F x)
lemma ferocious(F:Toy k N)(p:CardK N k F b a):Neat (dolphin F) ∧ CardK N k (dolphin F) b a ∧ ∀ x,colorX (dolphin F) x= (2:ℝ)⁻¹ • (colorX F x+rally N (colorX F (echo x))):=by
 let T:=wages F; let W:= F+T; let z:ℝ:=(2:ℝ)⁻¹; have h:= guard_h p
 obtain ⟨hp,hq,hv,he⟩:= carK F T p.1 h.1 p.2.1 h.2.1
 have ht(x):colorX (dolphin F) x= z • (colorX F x+rally N (colorX F (echo x))):=by rw [dolphin,roll_p, show F+wages F=W from rfl,show colorX W= _ from hv, Pi.add_apply,show colorX T x= _ from riches F x]
 refine ⟨fun i=>?_,⟨?_,?_,fun i=>?_⟩,ht⟩
 · rw [ht,ht,map_smul,map_add,relay_n,echo2,add_comm]
 · intro a i j k; unfold dolphin; simp_rw [Pi.smul_apply,show (F+wages F) _ _ _= _ from hp a i j k]; rw [smul_comm]
 · intro i u r C g; change z • Nacre.halo W i u r _= twist _ (z • Nacre.halo W _ _ _ _); rw [hq i u r C,map_smul]
 unfold dolphin balance; simp only [Pi.smul_apply,norm_smul, Real.norm_of_nonneg (by positivity :0≤(2:ℝ)⁻¹), ← mul_assoc]; let H:= (car_c p h).2.2 i; unfold balance at H; -- tune mul sum
 suffices (∑ y,∑ u,nick a (notx k i y u)* (2:ℝ)⁻¹ * (‖W i y u‖))= z*balance a W i by
    rw [this]; unfold z; change (2:ℝ)⁻¹ * balance a (F+wages F) i≤_; have hv:balance a (F+wages F) i ≤ b+b:=H; linarith
 simp_rw [balance, mul_sum]; refine sum_congr rfl fun _ _=>sum_congr rfl fun _ _=> ?_; ring
end YM.CF.Reef
