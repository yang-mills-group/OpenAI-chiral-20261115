import GaugeFieldConstruction.Arty
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
variable {c f: Side}{M M':Male}{G:Ratio c f}{o:Skye.Seat f}{Q:Op (Single f)}{h:ℝ}{Z:PalOne}{k n:ℕ}
local notation "ρ"=> αN G.count
local notation "L₀"=>G.count
-- term at rankJ. enough via FullY not tr depending Ω.
lemma z_v :ζOut G o 0= (Next.Free.toll L₀ 2)^2:=by unfold ζOut phaseO fanTax; simp [PayS]
private abbrev radical(F:Plane→L[ℝ]ℝ)(v:Plane):=fun t:ℝ=> PayS F (t • v)
lemma steamM (v:Views): ContDiffAt ℝ 2 (fun s:ℝ=>ζOut G o (s • v)) 0:=by
 let L:= PatchLoc G (AnchorN o); let K:=pointF (downT G o) (deckLoc G (AnchorN o));
 have hP {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (F:E→L[ℝ]ℝ)(i:E):ContDiffAt ℝ 2 (fun t:ℝ=> PayS F (t • i)) 0:=by simpa only [mul_one] using! ((factor_sale F 1).turn i).cost
 let A(i:Plane)(t:ℝ):= PayS (rom (lift L)) (ρ • t • i); have hp(i):ContDiffAt ℝ 2 (A i) 0:=by unfold A; simp_rw [smul_comm ρ]; exact hP _ _
 let X(i:Plane)(t:ℝ):= radical K i t*A i t; let e(i):ContDiffAt ℝ 2 (X i) 0:=(hP K i).mul (hp i)
 let Y(t:ℝ):= PayS (coincid o) (ρ • t • v); have he:ContDiffAt ℝ 2 Y 0:=by unfold Y; simp_rw [smul_comm ρ]; exact hP _ _
 change ContDiffAt ℝ 2 (fun t:ℝ=> star (X v.1 t)*X v.2 t*(Y t)⁻¹ * _) 0; exact ((((starL' ℝ:ℂ ≃L[ℝ]ℂ).contDiff.contDiffAt.comp 0 (e v.1)).mul (e v.2)).mul (he.inv (Complex.exp_ne_zero _))).mul contDiffAt_const -- tune
include M
lemma Blend_zero (b:Bool)(e: Odd G.count.val): Blend G M M' b 0=(Real.sqrt G.count.val:ℂ) • baseF b:=by
 let s:= (Real.sqrt G.count.val:ℂ); let Z:=baseF b
 unfold Blend; rw [show kview b (0:Views)=0 from (by unfold kview; split <;> rfl)]
 have hx:blockX M b L₀ 0 (angle (0:Plane))= s • Z :=by
    unfold blockX; rw [ang₀,(Hove.arm_u _ _ (by decide) _ _ e M.property).1]; -- order binder tune
    ext a v; change ( (s • (binV b:Op SpinIdx)) ⊗ₖ (1:Op SU.Slot)) a v= _; rw [Matrix.kronecker_apply]; rw [show Z=_ from binA b|>.symm]; obtain ⟨a,i⟩:=a; obtain ⟨v,j⟩:=v; rw [Matrix.smul_apply,Matrix.smul_apply,Matrix.kronecker_apply]; exact mul_assoc ..
 rw [hx,InputC,show bootstrap M' b (angle 0)=Z from binBase ..,(bladeSeal b).1.eq, Matrix.smul_mul,(bladeSeal b).1.eq] -- tune let un
lemma st_blend (b:Bool)(e:Odd G.count.val)(v: Views) (x y:Kt): ContDiffAt ℝ 2 (fun s:ℝ=> Blend G M M' b (s • v) x y) 0:=by
 let u:=kview b v; unfold Blend; simp_rw [show ∀ s:ℝ, ((blockX M b G.count 0 (angle (kview b (s • v)))) * InputC M' b (angle (kview b (s • v)))) x y=_ from fun s=> Matrix.mul_apply] -- tune
 apply ContDiffAt.sum; intro i _; let V(s:ℝ):=s • u; have ht(s:ℝ): kview b (s • v)= V s:=by cases b <;> rfl
 have hz(a b'):ContDiffAt ℝ 2 (fun x:ℝ=> blockX M b L₀ 0 (angle (V x)) a b') 0:= ((arm_K G.count M.val e M.property b (kview b v) 0 a.1 b'.1).of_le le_top).mul (contDiffAt_const (c:=(1:Op SU.Slot) a.2 b'.2)) -- tune alias M
 simp_rw [ht]; exact (hz x i).mul (sm_K b _ _ _)
omit M
-- matrix Taylor with hats; when lower vanish, prove k-<=2 derivative leading at line. general function not Pal Id.
section
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma H_cont (F:Views→ Pal)(V:PalOne)(v:AptK F V)(y:Views): ContDiffAt ℝ (2:WithTop ℕ∞) (fun t:ℝ=> F (t • y)) 0:= (v.turn y).cost
lemma P_trK(x:ℝ→Pal)(e: ContDiffAt ℝ 2 x 0) (y:Kt)(z:Kt):ContDiffAt ℝ 2 (fun i=> x i y z) 0:=by exact (LinearMap.toContinuousLinearMap (show Pal→ₗ[ℝ]ℂ from ⟨⟨(fun i=>i y z),fun _ _=>rfl⟩,fun _ _=>rfl⟩)|>.contDiff).contDiffAt.comp 0 e
end
private def part (P:PalOne)(r:ℕ)(v:Views):Pal:= match r with
| 0=>P.1 | 1=>P.2.1 v | _+2=> P.2.2.val v v
abbrev PartT(P:PalOne)(r:ℕ)(v:Views) := part P r v
private lemma sliceTP (P:Views→Pal)(V:PalOne)(e:AptK P V)(v:Views)(m:ℕ)(h:m≤2) (i j:Kt): iteratedDeriv m (fun s:ℝ=> P (s • v) i j) 0= part V m v i j:=by
 let F:Pal →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap (show Pal→ₗ[ℝ]ℂ from ⟨⟨(fun a=>a i j),fun _ _=>rfl⟩,fun _ _=>rfl⟩)
 have hp:=(e.turn v).map F
 interval_cases m
 · exact (show _ from hp.post) -- tune simpa
 · simpa only [iteratedDeriv_one] using! hp.fone
 simp only [iteratedDeriv_succ,iteratedDeriv_zero]; exact hp.gOne
lemma part_z (V:PalOne)(q:KappaF k V)(p:n ≤2)(t:n <k) (v:Views): part V n v=0:=by -- tune binder n
 interval_cases n; exact q.u t; unfold part; rw [q.v t]; rfl; unfold part; rw [q.q t]; rfl
lemma κ_trans {f g:ℝ→ℂ} (p:TierPair f g)(m:ℕ)(v:m≤2):iteratedDeriv m f 0=iteratedDeriv m g 0:=by obtain ⟨x,y,z,e,w⟩:=p; interval_cases m; exact (show _ from e.post.trans w.post.symm); rw [iteratedDeriv_one,iteratedDeriv_one]; exact e.fone.trans w.fone.symm; simp only [iteratedDeriv_succ,iteratedDeriv_zero]; exact e.gOne.trans w.gOne.symm
-- preserve lower zeros general
lemma jitney {a b: ℝ→ℂ}(h:ContDiffAt ℝ 2 a 0)(p:ContDiffAt ℝ 2 b 0)(z: ∀ i<k,iteratedDeriv i b 0=0) (u:k ≤ 2): iteratedDeriv k (fun x=> a x*b x) 0= a 0* iteratedDeriv k b 0:=by
 rw [iteratedDeriv_fun_mul (h.of_le _) (p.of_le _)]; rotate_left; · exact_mod_cast u
 · exact_mod_cast u
 rw [sum_eq_single 0]; simp; intro i u h
 have he:=mem_range.mp u; have hp:k-i < k:=by omega -- need i≤k
 rw [z _ hp]; simp
 simp
lemma jitR {a b:ℝ→ℂ}(h:ContDiffAt ℝ 2 a 0)(p:ContDiffAt ℝ 2 b 0)(z:∀ i<k,iteratedDeriv i b 0=0) (u:k ≤2) :iteratedDeriv k (fun x=> b x*a x) 0= iteratedDeriv k b 0 * a 0:=by simp_rw [mul_comm (b _)]; rw [jitney h p z u,mul_comm]
include M
lemma δFactor (e:Odd G.count.val) (v:Views)(x y:Kt)(t:k≤2)(F: ℝ→Pal)(L: Pal)(p: ∀ i j:Kt,ContDiffAt ℝ 2 (fun k=>F k i j) 0)(w:∀ i j,∀ m<k,iteratedDeriv m (fun x=> F x i j) 0=0) (u:∀ i j:Kt,iteratedDeriv k (fun x=> F x i j) 0=L i j) (h: (baseF false*L)* baseF true=L): iteratedDeriv k (fun s:ℝ=> ζOut G o (s • v) * (star (Blend G M M' false (s • v))* F s * Blend G M M' true (s • v)) x y) 0= (αN G.count^3:ℝ) • L x y:=by
 let A(i) (s:ℝ):= Blend G M M' i (s • v); let z(t:ℝ):= ζOut G o (t • v);
 let T (i j:Kt)(s:ℝ):= z s* star (A false s i x)* F s i j * A true s j y
 have ht(i j): ContDiffAt ℝ 2 (T i j) 0:=(((steamM v).mul ((starL' ℝ:ℂ ≃L[ℝ]ℂ).contDiff.contDiffAt.comp 0 (st_blend false (v:=v) e i x))).mul (p i j)).mul (st_blend true (v:=v) e j y)
 have he: (fun s:ℝ=> z s*(star (A false s)*F s* A true s) x y)= fun s=> ∑ i:Kt,∑ j:Kt,T i j s:=by
    funext s; rw [mul_assoc (star (A false s)),Matrix.mul_apply]; simp_rw [show ∀ i, (F s*A true s) i y= _ from fun i=>Matrix.mul_apply,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold T; rw [Matrix.star_apply]; ring
 have hx:=z_v (G:=G) (o:=o); let C:ℂ:=Real.sqrt (G.count.val:ℝ); have h0(b):A b 0=C • baseF b:=by unfold A; rw [zero_smul, Blend_zero b e]
 let q:= Next.Free.toll G.count 2
 have hJ(i j):iteratedDeriv k (T i j) 0=(q^2*C^2)*(baseF false x i) * L i j *baseF true j y:=by
    let W(s:ℝ):= z s *star (A false s i x); let X(s:ℝ):=W s* F s i j; let B(s:ℝ):= A true s j y; have hp:ContDiffAt ℝ 2 W 0:=(steamM v).mul ((starL' ℝ:ℂ ≃L[ℝ]ℂ).contDiff.contDiffAt.comp 0 (st_blend false (v:=v) e i x));
    have ha(s:ℕ)(l:s≤k): iteratedDeriv s X 0 = W 0* iteratedDeriv s (fun x=>F x i j) 0:= jitney hp (p i j) (fun n h=>w i j n (lt_of_lt_of_le h l)) (l.trans t)
    change iteratedDeriv k (fun t=> X t* B t) 0= _; rw [jitR (st_blend true (v:=v) e j y) (hp.mul (p i j)) (fun m h=> by rw [ha m h.le,w i j m h,mul_zero]) t,ha _ le_rfl,u]
    change W 0*L i j*A true 0 j y=_; unfold W z; rw [zero_smul,hx,h0,h0,Matrix.smul_apply,Matrix.smul_apply,smul_eq_mul,smul_eq_mul,star_mul,show star C=C from (by unfold C; simp), show star (baseF false i x)=baseF false x i from congrFun (congrFun (show star (baseF false)=baseF false from (bladeSeal _).2) x) i]; unfold q; ring
 change iteratedDeriv k (fun s:ℝ=> z s*(star (A false s)*F s *A true s) x y) 0= _; rw [he,iteratedDeriv_fun_sum (fun (i:Kt) _=> (show ContDiffAt ℝ 2 (fun s=>∑ j:Kt,T i j s) 0 from ContDiffAt.sum (fun j _=>ht i j)).of_le (show _ from (by exact_mod_cast t)))]; -- tune
 simp_rw [show ∀ i,iteratedDeriv k (fun s=>∑ j:Kt, T i j s) 0= _ from fun i=>iteratedDeriv_fun_sum (n:=k) (fun j (_:j∈ (univ:Finset Kt))=>(ht i j).of_le (by exact_mod_cast t)), hJ];
 have hz:q^2*C^2= ((ρ^3:ℝ):ℂ):=by
    unfold q C αN; have hp: (Real.sqrt G.count.val:ℝ)^2= G.count.val:= Real.sq_sqrt (Nat.cast_nonneg _)
    unfold Next.Free.toll; simp only [← Complex.ofReal_pow,hp, Complex.ofReal_natCast]; push_cast; field_simp -- tune
 rw [hz]; set N:=ρ^3; have hh: N • ((baseF false*L*baseF true) x y)=N • L x y:=by rw [h]
 rw [←hh,Complex.real_smul]; rw [mul_assoc (baseF false),Matrix.mul_apply]; simp_rw [show ∀ i,(L * baseF true) i y =_ from fun i=>Matrix.mul_apply,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
-- lower orientation from Eq Tab zero
omit M
lemma BaseSeq (V:PalOne)(k:ℕ)(p:k ≤2)(s:ℝ)(v:Views): part V k (s • v)= s^k • part V k v:=by -- tune need ≤2
 interval_cases k <;> simp [part, ContinuousLinearMap.smul_apply, smul_smul, pow_two]
lemma weigh_cut {r:ℕ}(q:KappaF k Z)(u:r≤k):KappaF r Z:= ⟨fun v=> q.u (v.trans u),fun v=> q.v (v.trans u),fun v=> q.q (v.trans u)⟩ -- binder r tune
include M
set_option maxHeartbeats 60000 in
lemma face_N (q:quote_B M Q o h k)(p:k≤2)(v:Views) : let S:=Strap M Q o h; let X:=part S k v
 baseF false* X* baseF true=X ∧ part (winJ o M h Q) k v=X:=by
 intro S X; obtain ⟨i,j⟩ : palCart (wheelP M false) S=S ∧ palCart S (wheelP M true)=S:=roll_star
 have ht : KappaF k S:= (cottonZ k).mp q
 unfold X
 suffices H: baseF false*part S k v * baseF true=part S k v by
    refine ⟨H, ?_⟩
    rw [tour_W]; apply Eq.trans _ H
    change part (palCart (palCart (bladeL false) S) (bladeL true)) k v=_; unfold palCart
    interval_cases k
    · rfl
    · unfold part; rw [cart_1,cart_1]; simp [bladeL]
    unfold part; rw [cart_2,cart_2]; simp [bladeL]
 have hh:baseF false*part S k v=part S k v:=by
    have he:=congrArg (fun i=>part i k v) i
    interval_cases k
    · simpa only [part,palCart,cart_0, plan_o] using he
    · simpa only [part,palCart,cart_1,ht.u (by omega),mul_zero,zero_add, plan_o] using he
    simpa only [part,palCart,cart_2,ht.u (by omega),ht.v (by omega),ContinuousLinearMap.zero_apply,mul_zero,zero_add,add_zero,plan_o] using he
 rw [hh]; have he:=congrArg (fun i=>part i k v) j
 interval_cases k
 · simpa only [part,palCart,cart_0, plan_o] using he
 · simpa only [part,palCart,cart_1,ht.u (by omega),zero_mul,add_zero,plan_o] using he
 simpa only [part,palCart,cart_2,ht.u (by omega),ht.v (by omega),ContinuousLinearMap.zero_apply,zero_mul,zero_add,add_zero,plan_o] using he
variable {U σ B: Bool→ℝ}{m:ℕ}(p:Silks σ U B m)(w:Odd G.count.val) (s:100<f.val)(T:quote_B M Q o h k)(q:SentK o Q)
include p w s T q
lemma leading_part (v:k≤2)(u:AptK (δInfty (RawInfinity G o (CoverPull M G o Q) h) M') Z)(X:Views) : PartT Z k X = ρ^(3+k) • PartT (winJ o M h Q) k X:=by
 ext i j
 have hz:= ζop o M M' G 0 m σ U B p w i j h Q X q s
 let S:= Strap M Q o h; let Q₀:= FullY M Q o h; let F(t:ℝ):= Q₀ (t • (ρ • X)); let u0:=σ true
 rw [show (fun l:ℝ=> ζOut G o (l • X)*(star (Blend G M M' false (l • X))* FullY M Q o h (ρ • (l • X)) * Blend G M M' true (l • X)) i j) = (fun s:ℝ=> ζOut G o (s • X)*(star (Blend G M M' false (s • X))*F s * Blend G M M' true (s • X)) i j) from ?hH] at hz -- tune target lhs rhs
 swap; · funext t; unfold F; rw [smul_comm ρ]; -- explicit
 let V :=PartT S k (ρ • X)
 have hp : baseF false*V*baseF true = V ∧ part (winJ o M h Q) k (ρ • X)= V:= face_N T v _
 have hu:=δFactor (o:=o) w (M:=M) (M':=M') X i j v F V (fun i j=>P_trK _ (H_cont Q₀ S flow_A _) i j) (fun i j m q=>by change iteratedDeriv m (fun t:ℝ=> FullY _ _ _ _ (t • ρ • X) i j) 0=0; rw [sliceTP _ S flow_A (ρ • X) m (by omega), part_z S ((cottonZ k).mp T) (by omega) q]; rfl) (fun i j=> sliceTP _ S flow_A _ k v i j) hp.1
 let U:=winJ o M h Q
 have he:= (κ_trans hz k v).trans hu
 rw [sliceTP _ Z u X k v] at he; change part Z k X i j = ρ^3 • V i j at he; have hv : V= ρ^k • PartT U k X:=hp.2.symm.trans (BaseSeq U k v ρ X) -- tune p binder
 change part Z k X i j = (ρ^(3+k)) • PartT _ k X i j; rw [he,hv,Matrix.smul_apply,smul_smul,pow_add] -- tune
lemma Flight_marks (v:k≤2)(u:AptK (δInfty (RawInfinity G o (CoverPull M G o Q) h) M') Z): ∀ i ≤ k,∀ X:Views, PartT Z i X = ρ^(3+i) • PartT (winJ o M h Q) i X := fun i he X=> leading_part p w s (weigh_cut T he) q (he.trans v) u X
end Boom
end YM.CF.TableF
end
