import GaugeFieldConstruction.Satin
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
variable {f:Side} {M:Male}{b:Bool}{o:Skye.Seat f}
-- seed with matrix index single & power
abbrev Platter := Kt → Cover → ℂ
def κFlow (M:Male)(b:Bool)(F:Platter)(x:Cover)(i:Kt):ℂ:= ∑' z: Lane,Paw 4 M b z.2 i z.1 * F z.1 (x+z.2)
def δbook (k:ℕ)(i:Plane)(x:Cover):ℂ:= (Complex.I*↑(rom x i))^k
def LψSeed (k:ℕ)(i:Plane)(a:Kt):Platter:=fun j x=> if a=j then δbook k i x else 0
def Lψε (k:ℕ)(M:Male)(b:Bool)(i:Plane)(a:Kt)(x:Cover)(j:Kt):= κFlow M b (LψSeed k i a) x j
lemma Ω_summable (k:ℕ)(v: Cover→ℂ)(C:ℝ)(h: chime (fun x:Cover=>Ladder x^k) v C) (a:Kt)(t: Plane)(x:Cover) : Summable (fun i:Cover=> ‖v i * δbook k t (x+i)‖):=by
 let P:= (Ladder x*‖t‖)^k; have he:Ladder x ≥ 0:= zero_le_one.trans (ladE _); refine Summable.of_nonneg_of_le (fun _=>norm_nonneg _)  (fun i=> ?_) (h.2.1.mul_left P); -- tune named
 rw [norm_mul]; unfold δbook; rw [norm_pow,norm_mul, Complex.norm_I,one_mul,Complex.norm_real]; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (rom _ _)) (b:= (Ladder x*‖t‖)*Ladder i) ?_ k) (norm_nonneg _)).trans_eq
 · unfold P; rw [mul_pow]; ring -- tune ring!
 · let X:=x+i; have ht:‖rom X‖≤ Ladder x* Ladder i:=(radius_Z X).trans ((le_add_of_nonneg_left zero_le_one).trans (wl_up ..)); exact ((rom _).le_opNorm _).trans ((mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_eq (mul_right_comm ..))
lemma Ω_root(k:ℕ)(M:Male)(b:Bool)(i:Plane)(a:Kt)(x:Cover)(j:Kt):Lψε k M b i a x j= ∑' z:Cover, Paw 4 M b z j a *δbook k i (x+z):=by
 let F(t: Kt)(y:Cover):=Paw 4 M b y j t*LψSeed k i a t (x+y); have hf(t):Summable (F t):=by
    unfold F LψSeed; by_cases h:a=t; · subst t; simp only [if_true]; exact (Ω_summable k _ _ (PC_pay (M:=M) (n:=k) b j a) a i x).of_norm
    simp_rw [if_neg h,mul_zero]; exact summable_zero
 let Q(p:Lane):=uncurry F p
 have hw:Summable Q:=Summable.of_norm (f:=Q) ((summable_prod_of_nonneg (fun i:Lane=> norm_nonneg (Q i))).2 ⟨fun i=> (hf i).norm,(hasSum_fintype _).summable⟩)
 change tsum Q= _; rw [hw.tsum_prod,tsum_fintype, sum_eq_single a]
 · simp only [Q,uncurry,F, LψSeed, if_true]
 · intro i g h; simp [Q,uncurry,F,LψSeed,Ne.symm h]
 simp
lemma rom_sum (x y:Cover):rom (x+y)=rom x + rom y:=by
 apply ContinuousLinearMap.ext; intro i; rw [rom_p,ContinuousLinearMap.add_apply,rom_p,rom_p]; simp only [Pi.add_apply,Int.cast_add,add_mul, Finset.sum_add_distrib]
variable (i:Plane)(k:Kt)(j:Kt)(x:Cover)(b M)
set_option maxHeartbeats 55000 in
lemma hectic (K:Cover→ℂ) (H:Summable fun i=> Ladder i^2*‖K i‖):TierS (fun t:ℝ=> ∑' z,PayS (rom (x+z)) (t • i)*K z) (∑' z,K z*δbook 0 i (x+z)) (∑' z,K z*δbook 1 i (x+z)) (∑' z,K z*δbook 2 i (x+z)):=by
 let V(z:Cover):= rom (x+z); let a(z:Cover):= Ladder x * Ladder z; let f(p: Plane):=∑' z, PayS (V z) p * K z; have he(z):‖V z‖≤ a z:= (radius_Z _).trans ((le_add_of_nonneg_left zero_le_one).trans (wl_up ..)); have h1(i):1 ≤ a i:= one_le_mul_of_one_le_of_one_le (ladE _) (ladE _)

 have ha : Summable fun i=> a i^2*‖K i‖:=by simp_rw [a,mul_pow, mul_assoc]; exact H.mul_left _
 obtain ⟨Y,e,g,y0,y1,y2⟩:= mainStream K V a he h1 ha
 let J(z:Cover)(s:ℝ):=PayS (V z) (s • i)*K z; let L(z:Cover):= Complex.I*↑(V z i); let B(r:ℕ)(z:Cover)(s:ℝ):=J z s*L z^r
 have hb(r z s): HasDerivAt (B r z) (B (r+1) z s) s:=by
    unfold B J; apply ((((PayS_diff (V z) i s).mul_const (K z)).mul_const (L z^r))).congr_deriv; unfold L; ring
 let H'(i':Cover):= a i'^2*‖K i'‖
 have hx(r:ℕ)(s:ℝ)(g:r ≤2)(z:Cover): ‖B r z s‖ ≤ H' z * ‖i‖^r:=by
    unfold B; rw [norm_mul,norm_pow]; have hp: ‖L z‖≤ a z*‖i‖:=by unfold L; rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]; exact ((V z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (he z) (norm_nonneg _))
    have hv:‖J z s‖=‖K z‖:=by unfold J; rw [norm_mul,pay_money,one_mul]
    rw [hv]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp r) (norm_nonneg _)); rw [mul_pow, ← mul_assoc, mul_comm ‖K z‖]; apply mul_le_mul_of_nonneg_right _ (by positivity); exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (h1 z) g) (norm_nonneg _)
 let R(k)(i):= ∑' z,B k z i
 have hg(r:ℕ)(v:r<2): ∀ i:ℝ, HasDerivAt (R r) (R (r+1) i) i := fun t=> hasDerivAt_tsum (g:= B r) (show Summable (fun z=> H' z *‖i‖^(r+1)) from ha.mul_right _) (hb r) (fun z s=> hx (r+1) s v z) (Summable.of_norm_bounded (ha.mul_right _) (hx r 0 v.le)) t
 have hV(r): R r 0=∑' z,K z*δbook r i (x+z):=by apply tsum_congr; intro z; unfold B J; rw [zero_smul,pay_zero,one_mul]; rfl
 have hp(s:ℝ):R 0 s= f (s • i):= by unfold R B; simp_rw [pow_zero,mul_one]; rfl
 have hR:ContDiffAt ℝ (2:WithTop ℕ∞) (R 0) 0:=(e.turn i).cost.congr_of_eventuallyEq (f:=fun t:ℝ=>f (t • i)) (Eventually.of_forall hp)
 refine TierS.equal (f:=R 0) ⟨hR,hV 0,(hg 0 (by decide) 0).deriv.trans (hV 1),?_⟩ (Eventually.of_forall hp); rw [show deriv (R 0)=R 1 from funext (fun x=>(hg 0 (by decide) x).deriv)]; exact (hg 1 (by decide) 0).deriv.trans (hV 2)
set_option maxHeartbeats 90000 in
lemma αLed : TierS (fun t:ℝ=> PayS (rom x) (t • i)*binor M b (t • i) j k) (Lψε 0 M b i k x j) (Lψε 1 M b i k x j) (Lψε 2 M b i k x j):=by
 let K:=fun z:Cover=> Paw 4 M b z j k; let V(z:Cover):=rom (x+z); let f(p:Plane):= ∑' z,PayS (V z) p*K z
 have hh(z): PayS (V z) =fun i=> PayS (rom x) i*PayS (rom z) i:= by funext i; unfold PayS V; rw [rom_sum,ContinuousLinearMap.add_apply,Complex.ofReal_add,mul_add,Complex.exp_add]
 have h_eq: f=ᶠ[𝓝 0] fun t=> PayS (rom x) t *binor M b t j k:=by
    filter_upwards [buoy_l] with u h
    unfold f; simp_rw [hh, mul_assoc, rom_e,tsum_mul_left]; exact congrArg _ (hel_pawn 4 (by decide) M b|>.readK _ h j k)
 rw [Ω_root,Ω_root,Ω_root]; exact (hectic i x K (PC_pay (M:=M) (n:=2) b j k).2.1).equal ((show Tendsto (fun s:ℝ=> s • i) (𝓝 0) (𝓝 0) from (show Continuous (fun s:ℝ=> s • i) from by fun_prop).tendsto' 0 0 (zero_smul ..)).eventually h_eq)
omit i k j
lemma αcharge (n:Single f)(p:Views)(o:Skye.Seat f)(k:Kt): let S(q:ℕ):= Lψε q M b (kview b p) k (spot o n.1.1) (portB n)
 TierS (fun t:ℝ=> candle M o b (t • p) n k) (S 0) (S 1) (S 2):=by cases b; exact αLed ..; exact αLed ..
end Boom
end YM.CF.TableF
end
