import GaugeFieldConstruction.Corvex
/-!
# Infinite ray-test packing
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
variable {c f:Side} {V S:DiamP→ℂ} {M M':Male}{G:Ratio c f}{o:Skye.Seat f}{b:Bool}{U σ r:ℝ}{Y:Op (Single f)}
private abbrev armYLeft (A:Mill→ℂ)(M:Male)(G:Ratio c f)(o:Skye.Seat f)(b:Bool)(p:Plane)(s:Kt)(x:Mill):ℂ:= PayS (measureG G o x.1) p * A x * InputC M b (angle p) x.2 s
-- legacy angle ambiguity
abbrev MoonY (A:Mill→ℂ)(M:Male)(G:Ratio c f)(o:Skye.Seat f)(b:Bool)(p:Plane)(s:Kt):= ∑' x:Mill, armYLeft A M G o b p s x
lemma Post_orb (x:DiamP)(v:Views): PayS (pairF G o x) v=star (PayS (measureG G o x.1.1) v.1)* PayS (measureG G o x.2.1) v.2:=by
 unfold PayS; rw [Complex.star_def, ←Complex.exp_conj, ← Complex.exp_add]; apply congrArg Complex.exp; let M:=measureG G o;
 change Complex.I*↑(-(M x.1.1 v.1) +M x.2.1 v.2)=_; push_cast; simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]; unfold M measureG; ring
lemma armSum (g:Mill→ℂ)(p:Summable fun x=>‖g x‖)(v:Plane)(i:Kt):Summable (fun x=>‖armYLeft g M G o b v i x‖):=by
 let B:= InputC M b (angle v); let C:= ∑ j:Kt,‖B j i‖; apply Summable.of_nonneg_of_le _ _ (p.mul_right C); · exact fun _=> norm_nonneg _
 intro x; rw [armYLeft,norm_mul,norm_mul,pay_money,one_mul]; exact mul_le_mul_of_nonneg_left (single_le_sum (f:=fun j:Kt=>‖B j i‖) (fun _ _=>norm_nonneg _) (mem_univ _)) (norm_nonneg _)
lemma into_wave (G:Ratio c f)(o:Skye.Seat f) (hX:Summable fun x=>‖V x‖) (h:ℝ)(i j:Kt): (fun v=>δInfty (RawInfinity G o V h) M v i j)=ᶠ[𝓝 0] fun v=> ∑' x:DiamP,(h^2:ℂ)*(V x*PayS (pairF G o x) v) * star (InputC M false (angle v.1) x.1.2 i) * InputC M true (angle v.2) x.2.2 j:=by
 let P(v:Views) := pairF G o -- tune
 filter_upwards [(show Tendsto (ContinuousLinearMap.fst ℝ Plane Plane) (𝓝 0) (𝓝 0) from continuousAt_fst).eventually (palP M false)] with v e
 let A:= RawInfinity G o V h v; let X:= InputC M false (angle v.1); let Y:= InputC M true (angle v.2); have hp: InputC M false (angle v.1)=fellP M false v*baseF false:= rfl -- if norm
 let L:=baseF false * fellP M false v; have he: δInfty (RawInfinity G o V h) M v=L*A*Y:=by unfold δInfty; change _=L*A*Y; unfold L; rw [mul_assoc, mul_assoc]; try rfl -- tune
 have hv(x:Kt):L i x= star (X x i):=by
    have hh: star X=L:=by unfold X; rw [hp,star_mul,show star (baseF false)=_ from (bladeSeal false).2, show star (fellP M false v)=_ from (show IsSelfAdjoint (fellP M false v) from e.2)]
    exact (show star (X x i)=L i x from congrFun (congrFun hh i) x).symm
 rw [he, mul_assoc, Matrix.mul_apply]; simp_rw [show ∀ a,(A*Y) a j =∑ b:Kt,A a b*Y b j from fun _=>Matrix.mul_apply ..] -- fix
 let F(a b:Kt)(x:DiamP) := L i a * (PayS (pairF G o x) v* gated a b h V x *Y b j)
 have hs(a b:Kt):Summable (F a b):=by
    let A':= fun x=>PayS (pairF G o x) v* gated a b h V x; have ht := Summable.of_norm_bounded (f:=A') (hX.mul_left (h^2)) fun x=> by unfold A'; rw [norm_mul,pay_money,one_mul]; exact γG a b x
    exact (ht.mul_right _).mul_left _
 simp_rw [mul_sum]; let Z(a b):= A a b
 change (∑ a:Kt,∑ b:Kt,L i a*(A a b* Y b j))=_; have hh(a b): L i a*(A a b*Y b j)=∑' x,F a b x:=by unfold F A RawInfinity; rw [tsum_mul_left,tsum_mul_right,Matrix.of_apply]
 simp_rw [hh]; rw [show (∑ a:Kt,∑ b:Kt,∑' x,F a b x)=∑' x,∑ a:Kt,∑ b:Kt,F a b x from ?_]; refine tsum_congr fun x=> ?_
 · unfold F; rw [sum_eq_single x.1.2]; rw [sum_eq_single x.2.2]; rw [gated,if_pos rfl,hv]; unfold X Y; ring -- tune
   intro b _ h; have hp:(x.1.2,b)≠ (x.1.2,x.2.2):=fun e=>h ((Prod.mk.inj e).2); simp only [gated,if_neg hp,mul_zero,zero_mul]; -- tune
   simp
   intro a _ e; exact sum_eq_zero fun b _=>by simp only [gated,if_neg (show (a,b)≠(x.1.2,x.2.2) from fun g=>e (Prod.mk.inj g).1),mul_zero,zero_mul]
   simp
 simp_rw [← Summable.tsum_finsetSum (fun i _=>hs _ i)] -- tune
 exact (Summable.tsum_finsetSum (fun i (_:i∈ (univ:Finset Kt))=> summable_sum (s:=univ) fun j _=>hs i j)).symm
noncomputable def LAM (M M':Male)(G:Ratio c f)(o:Skye.Seat f)(p: Plane)(b:Bool)(i: Single f)(x:Kt) := MoonY (Θfull M G o b i) M' G o b p x

lemma fund_par (Q:Op (Single f))(h:ℝ)(s:ℕ){V' Y' B:Bool→ℝ}(p:Silks V' Y' B s)(e:Odd G.count.val)(i j:Kt): (fun v=>δInfty (RawInfinity G o (CoverPull M G o Q) h) M' v i j) =ᶠ[𝓝 0] (fun v=> (h^2:ℂ)* PJ_act Q o (fun t=> LAM M M' G o v.1 false t i) (fun t=> LAM M M' G o v.2 true t j)):=by -- tune
 let A:=Θfull M G o; have hz(b) x : Summable fun y=>‖A b x y‖:=by
    have hp := (SB_paws (p.kw G e M b) (p.light _) (p.minor _) (AnchorN o) (μPose o x) (portB x) 0).2.1; simp_rw [wl0,one_mul] at hp; exact hp
 have hb(x:SM f): Summable fun i=>‖PeekE M G o x i‖:= (E_exist (G:=G) (A:=AnchorN o) _ _ (hz ..) (hz ..) (Classical.arbitrary _) (Classical.arbitrary _)).1
 let U(i:SM f)(v:DiamP):= PeekE M G o i v; let V(i:SM f):= HyT o Q i.1 i.2
 have he:Summable fun x=>‖CoverPull M G o Q x‖:=by
    have hh(i:SM f): Summable (fun y=>V i*U i y):=(hb i).of_norm.mul_left _; simp_rw [CoverPair]; exact (summable_sum (s:=univ) (fun i _=> hh i)).norm
 filter_upwards [into_wave G o he h (M:=M') i j] with v hv
 rw [hv];
 let w(i':SM f) :=armYLeft (A false i'.1) M' G o false v.1 i; let k(i':SM f) :=armYLeft (A true i'.2) M' G o true v.2 j; let H:ℂ:=h^2
 let E(i':SM f)(x:DiamP):=star (w i' x.1) * k i' x.2; let Z(i':SM f)(x):=H*V i'* E i' x
 have hh(x): H*(CoverPull M G o Q x * PayS (pairF G o x) v)*star (InputC M' false (angle v.1) x.1.2 i)*InputC M' true (angle v.2) x.2.2 j=∑ i:SM f,Z i x :=by
    rw [CoverPair, sum_mul,mul_sum,sum_mul,sum_mul]; apply sum_congr rfl; intro t _; unfold Z V E w k armYLeft; rw [Post_orb]; unfold PeekE ThetaS; simp only [star_mul]; unfold A; ring
 unfold H at hh; simp_rw [hh] -- tune after change
 have hy(u: SM f): Summable (E u) :=by
    have hp:= (E_exist (G:=G) (A:=AnchorN o) (w u) (k u) (armSum _ (hz ..) ..) (armSum _ (hz ..) ..) (Classical.arbitrary _) (Classical.arbitrary _)).1; exact hp.of_norm
 rw [Summable.tsum_finsetSum (f:=Z) (fun i _=>(hy i).mul_left _)]; unfold PJ_act; rw [mul_sum]; apply sum_congr rfl; intro i _; unfold Z; rw [tsum_mul_left,(hy i).tsum_prod]; unfold E; -- don't unfold w k
 simp_rw [tsum_mul_left,tsum_mul_right, ← tsum_star]; unfold w k LAM MoonY A V H; ring
end Boom
end YM.CF.TableF
end
