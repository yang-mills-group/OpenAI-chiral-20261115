import GaugeFieldConstruction.Culp
/-!
# pay primary mixing exact on Orbit. units at aperture origins; frames OK even o not a Matter cell
-/
set_option autoImplicit false
set_option maxHeartbeats 60000
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
variable {f c:Side} (o:Skye.Seat f)(M:Male) (M': Male)(G: Ratio c f)
local notation "Λ"=> G.count
local notation "ρ"=> αN G.count
local notation "A'"=> AnchorN o
private lemma pintA (p:Plane): aliasAt (angle p) (0: Site Λ)= angle (ρ • p):=by ext i; rw [alias_zero_eq]; unfold narrow Lenten.angle; first|simp [αN]| (simp [Fir.narrow,αN]; ring) -- tune
abbrev Blend (G: Ratio c f)(M M': Male)(b:Bool)(v: Views):Pal:= blockX M b G.count 0 (angle (kview b v))*InputC M' b (angle (kview b v))
abbrev phaseO (G:Ratio c f)(o:Skye.Seat f)(p:Plane):ℂ:=fanTax G o p * PayS (rom (lift (PatchLoc G (AnchorN o)))) (αN G.count • p)
abbrev ζOut (G:Ratio c f)(o:Skye.Seat f)(v:Views):ℂ:= star (phaseO G o v.1)*phaseO G o v.2 * (PayS (coincid o) (αN G.count • v))⁻¹ * (Next.Free.toll G.count 2)^2
lemma ntQ (b:Bool)(v:Views):kview b (ρ • v)=ρ • kview b v:=by cases b <;> rfl
lemma ℓcompose (x:Single f)(v:Views)(j:Kt)(b:Bool): let p:=kview b v; fanTax G o p* (AliTax b M G o x 0 p * smear_P Λ b p 0 M M' (portB x) j)= phaseO G o p * Next.Free.toll Λ 2 * ∑ l:Kt, candle M o b (ρ • v) x l* Blend G M M' b v l j:=by
 intro p; let q:= PatchLoc G A'; let X:=μPose o x
 let Y:= αN Λ • p
 have he: AliTax b M G o x 0 p=ηlux o x Y * PayS (rom (lift q)) Y *Next.Free.toll Λ 2:=by rw [AliTax,pintA, dockLoc,mode_shift,←rom_e,←rom_e]; rfl
 let A:=fellP M b (ρ • v); let B:=Blend G M M' b v
 have hg: bootstrap M b (angle (ρ • p))= A:=by cases b<;> rfl
 rw [he,show smear_P Λ b p 0 M M'=A*B from (by unfold smear_P; rw [pintA,hg])]; unfold candle; simp_rw [ntQ G _,mul_assoc,← Finset.mul_sum]; rw [Matrix.mul_apply]; unfold Y A B q p; ring -- tune
set_option maxHeartbeats 120000 in
lemma Φ_sc (i j:Kt)(h:ℝ)(V:Op (Single f))(v:Views) (l:ℝ):
 let r(l:ℝ):=l • v; let w(l):=ρ • r l; let S(l):=r l; let A(l):=Blend G M M' false (r l); let Y'(l):=Blend G M M' true (r l)
 let D(l):=FullY M V o h (w l)
 let L(b p x i):=LAM M M' G o p b x i; let F(b l x i):= ∑ a:Kt,candle M o b (w l) x a * Blend G M M' b (r l) a i
 let T:= Next.Free.toll G.count 2; let fz(b l):= phaseO G o (kview b (r l))* T
 let H:ℂ:=(h^2:ℂ); let V'(l):=PayS (coincid o) (w l);
 let K(b)(i:Kt)(l:ℝ) := fun x=> fz b l * F b l x i
 (∀ a b:Kt,D l a b= V' l * H* PJ_act V o (fun i=>candle M o false (w l) i a) (fun i=>candle M o true (w l) i b)) → H*PJ_act V o (K false i l) (K true j l)= ζOut G o (r l)* (star (A l)*D l*Y' l) i j:=by
 intro r w S A Y' D L F T fz H V' K ht
 let R(v y:Fn f):= PJ_act V o v y
 let a(b i):=fun x=>candle M o b (w l) x i
 have hk' (b) (i:Kt): K b i l=fz b l • (∑ j:Kt,Blend G M M' b (r l) j i • a b j):=by
    funext x; unfold K F; rw [Pi.smul_apply,Finset.sum_apply]; apply congrArg (fz b l * ·); exact sum_congr rfl (fun j _=>mul_comm ..)
 have hJ {E:Type}(p: Finset E)(Q:E→Fn f)(u:Fn f): R (∑ i∈p,Q i) u=∑ i∈p,R (Q i) u:=by induction p using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact zero_PJl _| insert a p h ih=> rw [sum_insert h,sum_insert h,← ih]; exact PJ_addL ..
 have hU {E:Type}(p: Finset E)(Q:E→Fn f)(u:Fn f): R u (∑ i∈p,Q i)=∑ i∈p,R u (Q i):=by induction p using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact zero_PJr _| insert a p h ih=> rw [sum_insert h,sum_insert h, ←ih]; exact PJ_addR ..
 change H* PJ_act V o (K false i l) (K true j l)= ζOut G o (r l)* (star (A l)*D l*Y' l) i j; rw [hk',hk',PJ_wL, PJ_wR,mul_assoc (star (A l))]
 unfold R at *; simp_rw [hJ,hU,PJ_wL,PJ_wR]; -- sum ordering
 rw [Matrix.mul_apply]; simp_rw [show ∀ k,(D l*Y' l) k j= _ from fun k=> Matrix.mul_apply, mul_sum]; -- tune notation
 apply sum_congr rfl; intro b _; apply sum_congr rfl; intro c _; rw [Matrix.star_apply, ht]
 have hp:star T=T:=by unfold T Next.Free.toll; simp
 have hz: V' l ≠0:=by unfold V' PayS; exact Complex.exp_ne_zero _ -- tune
 let FL:=phaseO G o (r l).1; let FX:=phaseO G o (r l).2; let z:=V' l; let p:= PJ_act V o (a false b) (a true c)
 change H*(star (FL*T)*(FX*T*(star (A l b i)*(Y' l c j *p)))) = star FL*FX*z⁻¹*T^2 * (star (A l b i) * ((z*H*p) * Y' l c j))
 rw [star_mul,hp]; change z≠0 at hz; field_simp
lemma ζop (x:ℂ)(s:ℕ)(σ Y B:Bool→ℝ)(u:Silks σ Y B s)(t:Odd G.count.val)(i j:Kt)(h:ℝ)(V:Op (Single f))(v:Views) (q:SentK o V)(p:100<f.val): TierPair (fun l:ℝ=> δInfty (RawInfinity G o (CoverPull M G o V) h) M' (l • v) i j) (fun l:ℝ=> ζOut G o (l • v) * (star (Blend G M M' false (l • v)) * FullY M V o h (ρ • (l • v)) * Blend G M M' true (l • v)) i j):=by
 let r(l:ℝ):=l • v; let w(l):=ρ • r l; let S(l):=r l; let A(l):=Blend G M M' false (r l); let Y'(l):=Blend G M M' true (r l)
 let D(l):=FullY M V o h (w l)
 let L(b p x i):=LAM M M' G o p b x i; let F(b l x i):= ∑ a:Kt,candle M o b (w l) x a * Blend G M M' b (r l) a i
 let T:= Next.Free.toll G.count 2; let fz(b l):= phaseO G o (kview b (r l))* T
 have hP(b x i): TierPair (fun l=>L b (kview b (r l)) x i) (fun l=>fz b l *F b l x i):=by
    have hy(p:ℝ):kview b (r p)=p • kview b v:=by cases b<;>rfl
    simp_rw [hy]; apply TierPair.symm; apply Transe (TierPair.symm (Lam_Pr (o:=o) (G:=G) (M':=M') b (u.kw G t M b) (u.light b) (u.minor b) t x (kview b v) i)) -- tune kview scalar def case
    apply Eventually.of_forall; intro z; have hg:kview b (r z)= z • kview b v:=by cases b<;> rfl
    have he:=ℓcompose o M M' G x (r z) i b; dsimp only at he; rw [hg] at he; unfold fz; dsimp only; rw [hg]; exact he
 have he:Tendsto (fun s:ℝ=> s • v) (𝓝 0) (𝓝 0):= (show Continuous (fun s:ℝ=> s • v) from by fun_prop).tendsto' 0 0 (zero_smul ..)
 let H:ℂ:= (h^2:ℂ);
 refine Transe (f:=fun l=>H*PJ_act V o (fun x=>L false (kview false (r l)) x i) (fun x=>L true (kview true (r l)) x j)) ?_ (he.eventually (fund_par (o:=o) V h s u t i j).symm)
 let K(b)(i:Kt)(l:ℝ) := fun x=> fz b l * F b l x i; let E(l):=H*PJ_act V o (K false i l) (K true j l); let p' : TierPair (fun l=>H*PJ_act V o (fun x=>L false (kview false (r l)) x i) (fun x=>L true (kview true (r l)) x j)) E:=by
    let Vq(x:SM _):= HyT o V x.1 x.2; let hh:= peelT (X:=SM _) univ _ _ (fun x _=> mul_T (mul_T (star_T (hP false x.1 i)) (Tpair (f:=fun _=>Vq x) contDiffAt_const)) (hP true x.2 j)); exact mul_T (Tpair (f:=fun _ : ℝ=>H) contDiffAt_const) hh
 let V'(l):=PayS (coincid o) (w l); have hS:Tendsto w (𝓝 0) (𝓝 0):= by unfold w; have hz: ContinuousAt (fun t:Views=> ρ • t) 0:=(by fun_prop); exact Tendsto.comp (by simpa only [smul_zero] using hz.tendsto) he -- tune
 have hf:∀ᶠ l in 𝓝 0,∀ a b:Kt,D l a b= V' l* H* PJ_act V o (fun i=>candle M o false (w l) i a) (fun i=>candle M o true (w l) i b):=eventually_all.mpr fun a=>eventually_all.mpr fun b=>hS.eventually (fact_Φ V o h M q p a b)
 apply TierPair.symm; refine Transe p'.symm ?_; filter_upwards [hf] with l ht;
 exact Φ_sc o M M' G i j h V v l ht
end Boom
end YM.CF.TableF
end
