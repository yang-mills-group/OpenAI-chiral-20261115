import YM.SU5.FiniteGaugeData.Stent.Velcro
import YM.CF.Cascade.Linen
import YM.Next.FLUCTUATIONS.Charts
import YM.Next.RANK.Ray
import YM.CF.Jet.Operetta
/-! # Group chart. mark cost yields lens from determinant.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option linter.flexible false
noncomputable section
namespace YM.CF
namespace Indigo
open SU Filter Function NormedSpace Thera Fock RG Finset Metric MeasureTheory Asymptotics
open Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight.Succulent
open scoped Matrix Topology InnerProductSpace MatrixOrder BigOperators ContDiff ComplexOrder Kronecker
open Cascade
local notation "D"=> Op SU.Slot
local notation "V"=> SU.group.Color
section
open scoped Matrix.Norms.Frobenius
lemma pep_e (k:ℕ)(i j:SU.F): ContDiff ℝ (↑k:WithTop ℕ∞) (fun x:V=> SU.fund (SU.group.lieExp x) i j):=by
 let z: SU.group.Mat→ₗ[ℝ]ℂ:=⟨⟨fun x=>x i j,fun _ _=>rfl⟩,fun _ _=> rfl⟩; exact z.toContinuousLinearMap.contDiff.comp (SU.group.exp_jet.of_le le_top) -- ω notation top? WithTop Nat∞ top
lemma pep_a : DifferentiableAt ℝ (fun x: V=> SU.group.curvature (SU.group.lieExp x)) 0 := (Next.Fluctuations.curvature_diff_mat (G:=SU.group) (SU.group.lieExp) 0 SU.group.exp_jet.contDiffAt).differentiableAt (by simp)
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- jet calculus.L.O.
namespace AntiS
variable {X X' :Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup X'][NormedSpace ℝ X']{f f':X→X'}{x:X'}
lemma beas (g:DifferentiableAt ℝ f 0)(p:forall x:X,HasDerivAt (fun i:ℝ=>f (i • x)) (f' x) 0) (t:X): (fderiv ℝ f 0) t=f' t := (Push.side _ g t).unique (p t)
lemma att (g:DifferentiableAt ℝ f 0)(p:forall x:X,HasDerivAt (fun i:ℝ=>f (i • x)) (f' x) 0)(a:f 0=x) : (fun v=> (f v-x)-f' v) =o[𝓝 0] (fun v=> ‖v‖):=by
 have e:(fun v=> f v-f 0-(fderiv ℝ f 0) (v-0)) =o[𝓝 (0:X)] fun i=> i-0:= g.hasFDerivAt.isLittleO; exact e.norm_right.congr (fun _=>by rw [sub_zero, a, beas g p]) (fun _=>by rw [sub_zero]) -- tune
lemma big (g:DifferentiableAt ℝ f 0)(a:f 0=x): (fun v=> f v-x) =O[𝓝 0] fun v=>‖v‖:=g.isBigO_sub.norm_right.congr (fun _=>by rw [a]) (fun _=>by rw [sub_zero])
lemma bigp (g:DifferentiableAt ℝ f 0)(a:f 0=0): f =O[𝓝 0] fun v=>‖v‖ := (big g a).congr_left fun _=>sub_zero _
end AntiS
lemma hst (x:V) : (green x^2).trace=-(60*↑(‖x‖^2:ℝ):ℂ):=by
 let Z:=SU.group.colorMat x; have hzZ:star Z= -Z:=SU.group.colorMat_skew x; have ht: Z.trace=0:=(league.mp (SU.group.colorMat_mem x)).2; rw [green,(SU.local_polynomial Z ⟨hzZ,ht⟩).2.1]; let M:= (Z^2).trace; have he:M= -5* ((‖x‖^2:ℝ):ℂ):=by
    unfold M; rw [sq]; apply Complex.ext; have ht:= SU.group.trace_color x x; rw [real_inner_self_eq_norm_sq] at ht; change - (Z*Z).trace.re=(↑(5:ℕ):ℝ)*_ at ht; push_cast at ht; norm_num -decide [←Complex.ofReal_pow]; linarith -- diag im
    have hx:(Z*Z).trace.im=0:=SU.group.trace_color_real x x; norm_num [hx,← Complex.ofReal_pow]
 change (12:ℂ)* M= _; rw [he]; push_cast; ring
abbrev scale_G :ℝ:= massP*massL
lemma sg0 : 0< scale_G:= mul_pos leaning.1 leaning.2.1
abbrev colorG :ℝ:= scale_G*60
lemma cg0: 0 < colorG:= mul_pos sg0 (by norm_num)
abbrev growX(U:E):= (matter U).val-1
lemma identity_C (U:E): CashNotch U=(1-scale_G • (growX U*star (growX U))).det:=by
 let X₀:= (matter U).val; let a:=massP; let b:=massL; have hp: X₀*star X₀=1:=(matter U).property.2; have ht: a+b=1:=leaning.2.2; unfold CashNotch; rw [← Matrix.det_conjTranspose,←Matrix.star_eq_conjTranspose,← Matrix.det_mul]; apply congrArg Matrix.det; change (a • X₀+b • 1)*star (a • X₀+b • 1)=1- (a*b) • ((X₀-1)*star (X₀-1)); rw [star_add,star_smul,star_smul,star_trivial a,star_trivial b,star_sub, star_one]; simp only [add_mul,mul_add, sub_mul,mul_sub, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,hp,mul_one,one_mul,smul_add,smul_sub, smul_smul] -- tune expansion.
 -- module.Normalize. Try solve via replacing b=1-a now.
 rw [show b=1-a by linarith]; module -- works?
-- L2 part contour derivative
abbrev diggon (x:V):D:= (matter (SU.group.lieExp x)).val
namespace AntiS
lemma dW : DifferentiableAt ℝ diggon 0:= by exact (((Jet.trie (k:=1)).comp (Jet.matt (k:=1) (pep_e 1))).differentiable (by norm_num) (0:V)) -- notation dW eq
lemma part_g : (fun x:V=> growX (SU.group.lieExp x)-green x) =o[𝓝 0] (fun v=>‖v‖):= att dW (fun x=>greenD x) (by simp only [show SU.group.lieExp 0=1 by simp,map_one]; rfl)
lemma stock_g : (fun x=> growX (SU.group.lieExp x))=O[𝓝 (0:V)] fun v=> ‖v‖:= big dW (by simp only [show SU.group.lieExp 0=1 by simp,map_one]; rfl)
lemma spur_g : green=O[𝓝 (0:V)] fun v=> ‖v‖:= (stock_g.sub part_g.isBigO).congr_left fun _ => sub_sub_self ..  -- tune bigO symmetry? replace
local notation "νs"=> SU.group.lieExp
local notation "φ"=> 𝓝 (0:V)
abbrev motto (x:V):= growX (SU.group.lieExp x)
private lemma star_m : (fun x=> star (motto x))=O[φ] fun x=>‖x‖:= (isBigO_of_le (φ) fun x:V=> (norm_star (motto x)).le).trans stock_g
abbrev salary (M:D) := ( -scale_G ) • (M * star M)
abbrev spawn(x:V):= salary (motto x)
abbrev priceB(x:V):= salary (green x)
lemma pin_m : spawn=O[φ] fun x=> ‖x‖^2:= ((stock_g.mul star_m).congr_right (fun _=> (sq _).symm)).const_smul_left (-scale_G)
lemma staple_m : (fun x=>spawn x-priceB x)=o[φ] (fun x=> ‖x‖^2):=by
 have hx: (fun x:V=> star (motto x)- star (green x)) =o[φ] (fun x=>‖x‖):= (isBigO_of_le (φ) fun x => (show ‖star (motto x)-star (green x)‖ ≤‖ motto x-green x‖ from (by rw [←star_sub,norm_star]))).trans_isLittleO part_g
 have hp: (fun x:V=> (motto x-green x)*star (motto x)+green x*(star (motto x)-star (green x)))=o[φ] (fun x=>‖x‖*‖x‖):= (part_g.mul_isBigO star_m).add (spur_g.mul_isLittleO hx); refine ((hp.congr_right fun _=> (sq _).symm).const_smul_left (-scale_G)).congr_left ?_; intro x; simp only [Pi.smul_apply]; unfold priceB spawn salary; rw [←smul_sub]; congr 1; noncomm_ring
local notation "ω₁"=> (1:D)
lemma greenTrace(x:V):(priceB x).trace= - (↑(colorG*‖x‖^2):ℂ):=by
 unfold priceB salary; rw [greenN,mul_neg,Matrix.trace_smul,Matrix.trace_neg,←sq, hst,Complex.real_smul]; unfold colorG; push_cast; ring
abbrev trival (m:D):= m.trace
abbrev bravoB(x:D):=(1+x).det
lemma jackpot : (fun x:D=> (1+x).det-1-x.trace) =o[𝓝 0] (fun i => ‖i‖):=by
 have ht(y:D):HasDerivAt (fun t:ℝ=> bravoB (t • y)) y.trace 0:= det_one_deriv (f:=fun t:ℝ=> 1+t • y) (by simp) (by simpa using! (((hasDerivAt_id' (0:ℝ)).smul_const y).const_add 1)) -- tune `.hasDeriv` parentheses
 have hv: DifferentiableAt ℝ bravoB 0:= (((Jet.det_k (k:=1) (fun i:D=> ω₁+i) (fun i j=> (Jet.elem (k:=1) i j).comp (contDiff_const.add contDiff_id))).differentiable (by simp)) (0:D)); exact att hv ht (by rw [add_zero,Matrix.det_one])
lemma pinchT:Tendsto spawn (𝓝 (0:V)) (𝓝 0):=by
 change Tendsto spawn (φ) (𝓝 (0:D)); exact pin_m.trans_tendsto (by simpa [ContinuousAt] using! ((continuous_norm.comp (continuous_id (X:=V))).pow 2).continuousAt (x:=(0:V))) -- check name
-- main stock
lemma vibrant : (fun x:V=> CashNotch (SU.group.lieExp x)-1+ (↑(colorG*‖x‖^2):ℂ)) =o[φ] (fun x=>‖x‖^2):=by
 have hku(x:V):CashNotch (νs x)= (1+spawn x).det:=by unfold spawn motto salary; rw [identity_C, neg_smul, ←sub_eq_add_neg]
 let T:D→ₗ[ℝ]ℂ:= Matrix.traceLinearMap SU.Slot ℝ ℂ -- check
 let L:= T.toContinuousLinearMap; let t₁:= ((jackpot.comp_tendsto pinchT).trans_isBigO pin_m.norm_left); have he:(fun x=> (spawn x).trace-(priceB x).trace)=o[φ] fun x=>‖x‖^2:= ((IsBigO.of_bound ‖L‖ <| Eventually.of_forall (p:=fun x:V=> ‖(spawn x).trace-(priceB x).trace‖ ≤ _ ) fun x=>by rw [← Matrix.trace_sub]; exact (L.le_opNorm (spawn x-priceB x))).trans_isLittleO staple_m)
 exact (t₁.add he).congr_left (fun x=>by simp only [Function.comp_apply,hku]; rw [greenTrace]; ring)
-- curvature in V part
abbrev cruxS (x:V):= SU.group.curvature (SU.group.lieExp x)
lemma goodP : (fun x => cruxS x-x) =o[φ] fun x=> ‖x‖:= (att pep_a SU.group.leading_curvature (show cruxS 0=0 by simp [cruxS])).congr_left fun x=>by simp only [sub_zero]
lemma costP : cruxS=O[φ] fun x=> ‖x‖:= bigp pep_a (show cruxS 0=0 by simp [cruxS])
lemma crystallized : (fun x:V=> CashNotch (SU.group.lieExp x)-1+(↑(colorG*‖cruxS x‖^2):ℂ)) =o[φ] (fun x=> ‖x‖^2):=by
 have he : (fun x:V => ‖cruxS x‖-‖x‖) =o[φ] fun x=> ‖x‖:= (isBigO_of_le (φ) fun x=> (abs_norm_sub_norm_le (cruxS x) x)).trans_isLittleO goodP; have hx:(fun x:V=> colorG*(‖cruxS x‖^2-‖x‖^2))=o[φ] fun x=> ‖x‖^2:=(( (he.mul_isBigO (costP.norm_left.add (isBigO_refl ..)))).congr (fun _=>by ring) (fun _=> (sq _).symm)).const_mul_left colorG
 have hp:(fun x:V=> (↑(colorG*(‖cruxS x‖^2- ‖x‖^2)):ℂ))=o[φ] fun x=> ‖x‖^2:= (isBigO_of_le (φ) fun x=> (Complex.norm_real (colorG*(‖cruxS x‖^2- ‖x‖^2))).le).trans_isLittleO hx; exact (vibrant.add hp).congr_left fun x=>by push_cast; ring
#print axioms crystallized
end AntiS
end Indigo
end YM.CF
