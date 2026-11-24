import YM.SU5.FiniteGaugeData.ArchiveK.Freight
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
attribute [local instance] μFin
open MeasureTheory.Measure
-- ℙ op.Eq lemma Rain fits. norm & cost. choose η.Aux measure.Not period-s.NB.
variable {A:Momentum→Op SpinIdx}{c C e:ℝ}{a:Axis}{x:E4} {b:ℕ}
#synth CompleteSpace (Op SpinIdx)
#synth IsScalarTower ℝ ℂ (Op SpinIdx)
#check ContinuousLinearMap.mul
#check LinearMap.mulRight
section mat
local notation "Ω" => Op SpinIdx
abbrev drizzle (i : Axis) : Ω:= -(Complex.I • gammaOp i)
local notation "Q"=> drizzle
open ContinuousLinearMap
def pactL (i:Ω) : ℂ →L[ℂ] Ω:= ((ContinuousLinearMap.id ℂ ℂ).smulRight i) -- tune Ω char 
@[simp] lemma xyone (u:Ω)(v:ℂ): pactL u v=v • u:=rfl
lemma rain_shape(x:E4): rain x= ∑ i:Axis,slurp x i • (drizzle i):=by unfold rain zen; simp_rw [←Finset.sum_neg_distrib]; unfold drizzle; simp_rw [smul_neg]
lemma rain_Int : Integrable rain μF:= by
 let X(i:Axis):=fun x:E4=> slurp x i • drizzle i; rw [show rain=fun x=>∑ i:Axis, X i x from funext rain_shape]; apply integrable_finsetSum _ (fun i _=> ?_); exact (((pactL (drizzle i)).restrictScalars ℝ).integrable_comp (slurp_I i))
def spiral(x:E4) : Ω:= ∑ i:Axis,((((gain⁻¹:ℝ):ℂ)*sax i x) • drizzle i)
lemma starQuote (x:Cover): scout rain x= spiral (emitX x):=by
 let X(i:Axis):=fun x:E4=> slurp x i • drizzle i; rw [show rain=fun x=>∑ i:Axis, X i x from funext rain_shape, scout_sum _ X (fun i _=>(((pactL (drizzle i)).restrictScalars ℝ).integrable_comp (slurp_I i)))]; unfold spiral; apply Finset.sum_congr rfl; intro i _; let A:= (pactL (drizzle i)); change scout (A ∘ fun x:E4=>slurp x i) x= A (((gain⁻¹:ℝ):ℂ)*sax i (emitX x)); rw [scout_we (f:=fun x:E4=> slurp x i) A (slurp_I i) x,scout_pa x i]; -- tune defeq
lemma spiral_other(x:E4) : spiral (-x)= -spiral x:=by unfold spiral; simp_rw [sax_neg, mul_neg, neg_smul, Finset.sum_neg_distrib]
-- anti-spin: Aop deck grading
abbrev keel:= 1-Aop
lemma zig (x:E4): Aop*spiral x=spiral x * keel:= by
 unfold spiral; let f:=fun i:Axis=> (sax i x); let p(y:E4)(i:Axis):= ((gain⁻¹:ℝ):ℂ)*sax i y; have he: spiral x= -zen (p x):= by unfold spiral zen drizzle; simp_rw [smul_neg, Finset.sum_neg_distrib]; rfl
 -- rewrite using he. norm zero spectral comparer. drift.
 change Aop*spiral x=spiral x * keel; rw [he,mul_neg,neg_mul,zenA]
lemma zig_z (x:E4): keel*spiral x=spiral x*Aop:=by unfold keel; rw [sub_mul,zig,keel,mul_sub,one_mul,mul_one]; abel
lemma keel_song : keel*keel=keel:=by unfold keel; rw [sub_mul,mul_sub Aop,one_mul,mul_one,AOne,sub_self,sub_zero]
lemma keel_snow : Aop*keel=0∧keel*Aop=0:=by unfold keel; rw [mul_sub Aop, sub_mul,one_mul,mul_one,AOne,sub_self]; simp
def voteS (x:E4) : Ω:= (1+rain x)*keel
abbrev fpS(x:Cover):Ω:= (if x=0 then keel else 0)+ spiral (emitX x)*keel
abbrev mulLs (i:Ω):Ω→L[ℂ]Ω:= (LinearMap.mul ℂ Ω i).toContinuousLinearMap
abbrev mulRs(i:Ω):Ω→L[ℂ]Ω:= (LinearMap.mulRight ℂ i).toContinuousLinearMap
lemma vote_I : Integrable voteS μF:= ((mulRs keel).restrictScalars ℝ).integrable_comp ((integrable_const 1).add rain_Int)
lemma vote_Q (x:Cover): scout voteS x=fpS x:=by
 let A:=mulRs keel; change scout (A ∘ fun y:E4=>1+rain y) x=_; rw [scout_we (f:=fun x:E4=>1+rain x) A ((integrable_const _).add rain_Int) x]; rw [scout_add (integrable_const _) rain_Int,pact, starQuote]; unfold fpS; change ( (if x=0 then _ else _) + spiral (emitX x))*keel= _; split_ifs <;> simp [add_mul]
-- eventually under shot. quant.E integral via pointwise convergence: vote∞ as symbol; kill.
#check Complex.continuous_exp
set_option maxHeartbeats 800000 in
lemma receives {X:Type*} {f:Filter X}{M:X→Tulip.Male}[f.NeBot](t:Tendsto (fun i=>(M i).val.val) f atTop)(e:x∈stair)(h:∀ i:Cover,pass (brushQ x+reciprocal i)≠0)(p:brushQ x≠0): Tendsto (fun i=>bar 4 (M i).val (brushQ x)* voteS x) f (𝓝 0):=by
 let Z:= brushQ x; let v(i):=mixL 4 (M i).val Z; let V:= slurp x; have hu:= stair_body e; have he:Tendsto v f (𝓝 V):= tendsto_pi_nhds.mpr (fun i=>harmony (fun k:X=>(M k).property) t (F:=fun _=>Z) tendsto_const_nhds h i (Eventually.of_forall fun _=>hu)); -- per-coordinate A.e? norm
 let C:=zen V; let W:= graphs_ne (v:=V); have ht:physical V:=by
    unfold physical; apply tendsto_nhds_unique _ he; change Tendsto v _ _; let H:= he.star; exact H.congr' (by filter_upwards with i; exact phys_mix 4 _ (M i).property _ hu.1)
 let s (z:Momentum):=(1+prodM z z)⁻¹ • (((1:Ω)-zen z)*Aop*(1+zen z)); have hb:s V*voteS x=0:=by
    let θ:=prodM V V; have hh:(1+C)*(1-C)=(1+θ) • (1:Ω):=by rw [add_mul,one_mul,mul_sub,mul_one, show C*C= -θ • (1:Ω) from zenSq V]; module
    unfold s voteS; rw [Matrix.smul_mul]; change (1+θ)⁻¹ • (((1-C)*Aop*(1+C))*((1+-C)* keel))=0; rw [← sub_eq_add_neg,←mul_assoc,mul_assoc ((1-C)*Aop),hh,Matrix.mul_smul,mul_one,Matrix.smul_mul,mul_assoc,keel_snow.1,mul_zero,smul_zero,smul_zero]
 have hV : Continuous zen := by unfold zen; fun_prop
 have hg: ContinuousAt s V:= by unfold s; refine ((show ContinuousAt (fun p=>1+prodM p p) V from (show Continuous (fun p: Momentum=>1+prodM p p) from by unfold prodM; fun_prop).continuousAt).inv₀ (W ht)).smul ?_; exact (((continuous_const.sub hV).mul continuous_const).mul (continuous_const.add hV)).continuousAt -- tune op. 
 rw [←hb]; refine ((hg.tendsto.comp he).mul_const (voteS x)).congr' ?_; filter_upwards with i; let A:= (M i).val; have hq:=base_subset_realCube zone_pos hu
 rw [(bar_full 4 A hq p (graphs_ne (phys_mix _ _ (M i).property _ hu.1))).1,shell_inv _ _ hq p]; rfl
end mat
end YM.CF.Window.ArchiveK
