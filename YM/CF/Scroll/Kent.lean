/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Scroll.Sole
import YM.Next.FREE_KERNELS.Bank
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {a:Type*}[Fintype a][DecidableEq a]
lemma u_all {B:Type*}(F:B→Op a)(g:∀ i j,Summable fun x:B=> F x i j): Summable F:=by
  refine ⟨Matrix.of fun i j=>∑' x:B,F x i j,?_⟩; unfold HasSum; rw [Branch.kernel_test]; intro i j; simp only [Matrix.sum_apply]; exact (g i j).hasSum
lemma v_all {B:Type*}(F:B→Op a)(g: Summable F)(i j:a) : (∑' x,F x) i j=∑' x,F x i j:=by have he:= g.hasSum; unfold HasSum at he; rw [Branch.kernel_test] at he; refine Eq.symm (HasSum.tsum_eq (show HasSum (fun x=>F x i j) _ from ?_)); unfold HasSum; simpa only [Matrix.sum_apply] using he i j
lemma influxX (N:ℕ→Side)(H: Tendsto (fun i=>(N i).val) atTop atTop)(f: Cover→Op a)(h:∀ i j,Summable fun x:Cover=>‖f x i j‖)(z:Cover)(i j:a): Tendsto (fun x=>Rush.wind (0:Site (N x)) z * cart (N x) f (0,i) (wrap (N x) z,j)) atTop (𝓝 (f z i j)):=by
 let F(k:ℕ)(y:Cover):=wind (0:Site (N k)) z*wagon (N k) f y (0,i) (wrap (N k) z,j)
 let G(y:Cover):=if y=z then f y i j else 0
 have he(y): Tendsto (fun k=>F k y) atTop (𝓝 (G y)):=by
    apply Filter.EventuallyEq.tendsto; filter_upwards [eventually_unfold N H z,eventually_unfold N H y] with k hk p
    by_cases h:y=z; unfold F G; simp [wagon_app,h, ← mul_assoc, wind,fee_one]
    have hp:wrap (N k) y≠wrap (N k) z:=fun e=> h (p ▸ hk ▸ congr_arg Lattice.lift e)
    simp [F,G,h,hp,wagon_app]
 have hp(k y): ‖F k y‖ ≤ ‖f y i j‖ := by unfold F; rw [wagon_app,norm_mul]; split <;> simp [wind, fee_norm]
 have ht:= tendsto_tsum_of_dominated_convergence (h i j) he (Eventually.of_forall hp)
 simp only [F,G,tsum_mul_left] at ht; rw [tsum_eq_single z] at ht; swap; intro a h; simp [h]; simp only [ite_true] at ht
 exact ht
lemma Reads_u (A:Momentum→Op a) (F G:Cover→ Op a)(h: Reads F A)(g: Reads G A): F=G:=by
 let ss (k:ℕ):Side:=⟨k+1,Nat.zero_lt_succ _⟩; have he:Tendsto (fun k=>(ss k).val) atTop atTop:=tendsto_atTop_mono (fun i=>show i ≤ i+1 by omega) tendsto_id
 have hp(N:Side):cart N F=cart N G:=by rw [cart_traded h,cart_traded g]
 ext x i j; have hv:= influxX ss he F h.sumK x i j; simp_rw [hp] at hv; exact tendsto_nhds_unique hv (influxX ss he G g.sumK x i j)
lemma sum_ph (F:Cover→Op a)(A:Momentum→Op a)(h:Reads F A)(p:Momentum)(hp:p∈baseCube): Summable (fun z:Cover=> mode p z • F z) ∧ read F p=A p:=by
 have hx: Summable (fun z:Cover=> mode p z • F z):= u_all _ (fun i j=> Summable.of_norm (by simpa only [Matrix.smul_apply,norm_smul,mode_real _ _ hp.1,one_mul] using h.sumK i j))
 exact ⟨hx,(by ext i j; unfold Laurent.read; rw [v_all (fun _=>_) hx]; exact h.readK p hp i j)⟩
lemma mayF (b:Bool)(U:UNI a)(F:Cover→Op a)(h:∀ i j,Summable fun x:Cover=> ‖F x i j‖)(i j:a): Summable fun x:Cover=> ‖sings b U (F x) i j‖ :=by
 let Z:Op a→Op a:= windX b; have hk (x r t):‖(Z (F x)) r t‖=‖F x r t‖:=by cases b <;> simp [Z,windX]
 let H(x:Cover) (r t:a):= ‖U.val i t‖ * ‖F x t r‖ * ‖star U.val r j‖
 have hm : Summable (fun x:Cover=>∑ r, ∑ t,H x r t):= summable_sum fun r _=> summable_sum fun t _=> ((h t r).mul_left _).mul_right _
 apply hm.of_nonneg_of_le; intro; apply norm_nonneg
 intro x; unfold sings twist; -- tune
 change ‖((U.val * Z (F x))*star U.val) i j‖≤_
 simp only [Matrix.mul_apply,sum_mul]; apply le_trans (norm_sum_le ..) _; apply Finset.sum_le_sum; intro r _; refine (norm_sum_le ..).trans (le_of_eq ?_); simp only [norm_mul,hk,H]
lemma morphX (b:Bool)(s:Signed)(U:UNI a)(F H:Cover→Op a)(A B:Momentum→Op a)(h:Reads F A)(g: Reads H B)(hx:∀ p,p∈baseCube→ sings b U (A (cadence s b p))= B p)(x:Cover) : sings b U (F (s.act x))=H x :=by
 let K(y:Cover):=sings b U (F (s.act y)); have ht(i j:a): Summable (fun x=> ‖K x i j‖):= (mayF b U F h.sumK i j).comp_injective s.act_injective
 refine congr_fun (Reads_u B K H ⟨ht,fun p hp i j=>?_⟩ g) x
 let R(z:Cover):=mode p z • K z; have hp': Summable R:= u_all R (fun i j=>Summable.of_norm (by unfold R; simpa only [Matrix.smul_apply,norm_smul,mode_real _ _ hp.1,one_mul] using ht i j))
 let Y:= cadence s b p; obtain ⟨hh,hG⟩:=sum_ph F A h _ (cadence_base _ hp s b)
 have hy:(∑' z,R z)=B p:=by
    rw [←hx p hp,←hG,Laurent.read,sings_sumts _ _ _ hh,← s.actEquiv.toEquiv.tsum_eq (fun z=> sings b U (mode (cadence s b p) z • F z))]; refine tsum_congr fun z=>?_ -- tune
    change mode p z • sings b U _=sings b U (mode _ (s.act z) • _); rw [form p s b hp.1,singT,singT,win_c,twist_scalar]; cases b<;>simp [cSignX,Signed.actEquiv]
 rw [← hy,v_all R hp']; rfl
variable (b r:Bool)(s:Signed)(U:UNI SpinIdx)
lemma bent_v (h:JetS s b r U)(N:Side)(ho:Odd N.val)(x:Cover)(j:ℕ)(u:Bool)(he:1≤j) : sings b U (tub (bent u j N) (s.act x))=tub (bent (r.xor u) j N) x:= morphX b s U _ _ _ _ (cBar j N u he ho) (cBar j N _ he ho) (fun p hp=>bent_s h N ho p hp u j) x
end YM.CF.Scroll
