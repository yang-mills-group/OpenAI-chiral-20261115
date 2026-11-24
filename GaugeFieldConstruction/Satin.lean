import GaugeFieldConstruction.Tremor
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {c f: Side}{G:Ratio c f}{M:Male}{A:Site f}{Q: Op (Single f)}{o:Skye.Seat f}{h:ℝ}{k n:ℕ}{b:Bool}
abbrev quote_B (M:Male) (Q:Op (Single f))(o:Skye.Seat f) (h:ℝ) (r:ℕ):=KappaF r (winJ o M h Q)
def coincid (o:Skye.Seat f):Views→L[ℝ]ℝ:= -(kNote f o|>.comp (ContinuousLinearMap.fst ℝ Plane Plane))+(kNote f o|>.comp (ContinuousLinearMap.snd ℝ Plane Plane))
def HyT (o:Skye.Seat f)(Q: Op (Single f))(x y:Single f):ℂ:= Caller o x.1.1 * Caller o y.1.1 * Q x y
abbrev kview (b:Bool)(v:Views):= if b then v.2 else v.1
-- Pinched strong chart on U
abbrev SentK(o:Skye.Seat f)(Q:Op (Single f)):=∀ i j,Q i j≠0 →10*separation (node i.1.1) o <(More f).val∧ 10*separation (node j.1.1) o < (More f).val
def ηlux (o:Skye.Seat f)(x: Single f)(v:Plane):= PayS (rom (spot o x.1.1)) v
def candle (M:Male)(o: Skye.Seat f)(b:Bool)(v:Views)(i:Single f)(x:Kt):ℂ:= ηlux o i (kview b v)* fellP M b v (portB i) x
abbrev Fn (n:Side):= Single n → ℂ
def PJ_act (Q:Op (Single f))(o:Skye.Seat f)(L K:Fn f):ℂ:= ∑ i: Single f×Single f, star (L i.1) *HyT o Q i.1 i.2 * K i.2
lemma fact_lights (v:Views)(p:SentK o Q)(u:100 < f.val)(x y:Single f): PayS (κviews o x.1.1 y.1.1) v*hill_Z o Q h x y= PayS (coincid o) v * (h^2:ℂ) * star (ηlux o x v.1)*HyT o Q x y * ηlux o y v.2 :=by
 by_cases h:Q x y=0; · simp only [hill_Z,HyT,h,mul_zero,zero_mul]
 let P:= p x y h; unfold ηlux; unfold PayS; rw [Complex.star_def, ←Complex.exp_conj] -- tune
 unfold κviews; rw [point_phase x.1.1 P.1 u, point_phase y.1.1 P.2 u]; let K:= kNote f o; let X:=rom (spot o x.1.1); let Y:=rom (spot o y.1.1); let L:= (coincid o) v;
 have he: star (Complex.I*↑(X v.1))= -(Complex.I*↑(X v.1)):=by simp [star_mul,mul_comm] -- tune
 change Complex.exp (Complex.I*↑(- ( (K+X) v.1)+(K+Y) v.2)) * hill_Z _ _ _ x y= Complex.exp (Complex.I*↑L)*_* Complex.exp _ *_*_
 rw [show -( (K+X) v.1)+(K+Y) v.2=L-X v.1+Y v.2 from ?_]; swap; · change -(K v.1+X v.1)+(K v.2+ Y v.2)= (-K v.1+K v.2)-X v.1+Y v.2; ring
 push_cast; rw [show Complex.I*(L-X v.1+Y v.2)= Complex.I*↑L+star (Complex.I*(X v.1:ℂ))+Complex.I*(Y v.2:ℂ) from (by rw [he]; ring),Complex.exp_add,Complex.exp_add]; unfold X Y hill_Z HyT; simp only [Complex.star_def]; ring
private lemma march_e (b:Bool):∀ᶠ v in 𝓝 (0:Views), star (fellP M b v)= fellP M b v:=by
 cases b
 · filter_upwards [(show Tendsto (ContinuousLinearMap.fst ℝ Plane Plane) (𝓝 0) (𝓝 0) from continuousAt_fst).eventually (palP M false)] with i p; exact p.2
 filter_upwards [(show Tendsto (ContinuousLinearMap.snd ℝ Plane Plane) (𝓝 0) (𝓝 0) from continuousAt_snd).eventually (palP M true)] with i p; exact p.2
lemma fact_Φ (Q:Op (Single f))(o:Skye.Seat f)(h:ℝ)(M:Male)(p:SentK o Q)(u:100 < f.val) (a b:Kt): (fun x=> FullY M Q o h x a b) =ᶠ[𝓝 0] (fun x=> PayS (coincid o) x * (h^2:ℂ)* PJ_act Q o (fun i=>candle M o false x i a) (fun i=>candle M o true x i b)):=by
 filter_upwards [march_e (M:=M) false] with x hx
 let K:= fellP M false x; let T:= fellP M true x
 let U(i:Single f ×Single f):= PayS (κviews o i.1.1.1 i.2.1.1) x * hill_Z o Q h i.1 i.2
 unfold FullY streamF PJ_act; rw [Matrix.mul_sum, Matrix.sum_mul,Matrix.sum_apply,mul_sum]; apply sum_congr rfl; intro i _; change (K * flare_one (portB i.1) (portB i.2) (U i)*T) a b=_; let j:=portB i.1; let k:=portB i.2;
 have he(u:ℂ): (K* flare_one j k u * T) a b= K a j*u*T k b:=by
    change (K * Matrix.single j k u *T) a b= _; rw [Matrix.mul_apply, sum_eq_single k]
    · rw [Matrix.mul_apply,sum_eq_single j]
      · rw [Matrix.single_apply_same]
      · intro i _ h; rw [Matrix.single_apply]; split; rename_i g; · tauto
        rw [mul_zero]
      simp
    · intro i _ h; rw [Matrix.mul_apply]; simp [Matrix.single_apply, ite_and,h,Ne.symm h] -- tune
    simp -- tune
 rw [he,show K a j= star (K j a) from Eq.symm (congrFun (congrFun hx a) j), show U i=_ from fact_lights (h:=h) x p u i.1 i.2]; unfold candle; change star (K j a)*(_ :ℂ)* T k b= (PayS (coincid o) x* (h^2:ℂ))*(star (ηlux o i.1 x.1 * K j a)* _ *(ηlux o i.2 x.2*T k b)); rw [star_mul]; ring -- tune
-- TierS equality up to d reciprocal
private abbrev Kev (a b d:ℂ)(r:ℕ): Prop:=(1 ≤r→a=0)∧ (2 ≤r → b=0)∧ (3 ≤r →d=0)
private def PAL_it(x y:Kt): Pal→L[ℝ] ℂ:= LinearMap.toContinuousLinearMap ⟨⟨(fun i=>i x y),fun i j=>rfl⟩,fun i j=>rfl⟩
lemma Account_F (Q:Op (Single f))(o:Skye.Seat f)(h:ℝ)(M:Male){r:ℕ}(s:quote_B M Q o h r)(p:SentK o Q)(u:100 < f.val)(d:h≠0) (i j:Kt)(y:Views) {a a' b':ℂ}(g:TierS (fun t:ℝ=> PJ_act Q o (fun i'=> candle M o false (t • y) i' i) (fun j'=> candle M o true (t • y) j' j)) a a' b'): Kev a a' b' r:=by
 let A:=coincid o
 have ht:Tendsto (fun t:ℝ=> t • y) (𝓝 0) (𝓝 0):=(show Continuous (fun t:ℝ=> t • y) from by fun_prop).tendsto' _ _ (zero_smul ..)
 let V:= Strap M Q o h
 let z:= (h^2:ℂ); let B:= (bookP A z); have v :z≠0:= pow_ne_zero _ (Complex.ofReal_ne_zero.mpr d)
 have hg:= ((factor_sale A z).turn y).mul g
 have he:= ((AptK.turn (P:=V) flow_A y).map (PAL_it i j)).unique hg (ht.eventually (fact_Φ Q o h M p u i j)); let a₁:=a';
 have hu:KappaF r V:= (cottonZ r).mp s
 obtain ⟨u0,u1,u2⟩:=he
 rw [fund0] at u0 u1 u2
 have ha(q:1≤r): a=0:=by
    rw [hu.u q,map_zero] at u0; exact (mul_eq_zero.mp u0.symm).resolve_left v
 have hb(q:2≤r):a'=0:=by
    rw [hu.v q, ContinuousLinearMap.zero_apply,map_zero] at u1; rw [ha (by omega),mul_zero,zero_add] at u1; exact (mul_eq_zero.mp u1.symm).resolve_left v
 refine ⟨ha,hb,fun t=>?_⟩; rw [ha (by omega), hb (by omega),mul_zero,zero_add,mul_zero, zero_add,add_zero] at u2; rw [hu.q t,Submodule.coe_zero,ContinuousLinearMap.zero_apply,ContinuousLinearMap.zero_apply,map_zero] at u2; exact (mul_eq_zero.mp u2.symm).resolve_left v
end Boom
end YM.CF.TableF
end
