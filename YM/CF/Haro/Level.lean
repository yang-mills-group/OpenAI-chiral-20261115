import YM.CF.Haro.Lantern
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable {n:Side}(F:Op (Single n))(h:AxisB F)
variable {x:Site n}{m i:ℕ}
abbrev V' := SpinIdx × Slot
def powerV (U: Site n)(r:V') : Single n:=((U,r.1),r.2)
abbrev rakeV (m:ℕ)(x:Single n):= paidX (perk m x) fun y:Single n=> F x y
lemma paceS {x:Site n}(m:ℕ)(y:Cover)(s:y∈ portY x)(a b:V'): tweight m y ≤ 4^m* perk m (powerV (0:Site n) a) (powerV x b):=by
 obtain ⟨i,h⟩:= mem_filter.mp s; obtain ⟨⟨z,v⟩,k,rfl⟩:= mem_image.mp i; have hp : separation (node (0:Site n)) (node x) = 2*separation 0 x:= Cascade.verse _
 have hx:x=v.act z:=by rw [←h,←wrap_signed,wrap_lift]
 have hh:separation x 0=separation z 0:=by
    rw [hx,← show v.act (0:Site n)=0 from Signed.act_zero v]; rw [separation_signed,Signed.act_zero] -- tune both
 have hv: Laurent.size (v.act (lift z))≤ Fintype.card Axis *separation x 0:=by
    unfold Laurent.size; rw [←show (∑ _ :Axis,separation x 0) = Fintype.card Axis * separation x 0 from (by simp)]; refine sum_le_sum fun i _=>?_ ; obtain ⟨i,rfl⟩:= v.perm.surjective i; rw [Signed.act_at]; have he: (lift z i).natAbs≤ separation z 0:=by rw [separation,sub_zero]; exact component_le z i
    rw [hh]; cases p:v.flip i <;>simpa using he
 change (1+(Laurent.size _:ℝ))^m ≤ _ * (1+(separation (node (0:Site n)) (node x):ℝ))^m; rw [←mul_pow,hp]; apply pow_le_pow_left₀ (by positivity); change Laurent.size _ ≤ 4*separation x 0 at hv; rw [separation_comm x 0] at hv
 have ht:(Laurent.size (v.act (lift z)):ℝ)≤ 4*(separation 0 x):=by exact_mod_cast hv
 push_cast; linarith
lemma tideP (m:ℕ)(k:ℝ)(hz:∀ a:Single n,rakeV F m a ≤ k): RailP m (loft F) (4^m*k):=by
 let p:= porchY n; intro i j; unfold Cp; let f(x):= tweight m x * ‖loft F x i j‖; have hh(x:Cover)(t:x∉ p): f x=0:=by unfold f; simp [loft,t,p]
 refine ⟨fun _=>mul_nonneg (tw_pos ..) (norm_nonneg _),summable_of_ne_finset_zero (s:=p) hh,?_⟩
 have hx: p=univ.biUnion (portY (n:=n)):= Finset.ext fun i=>by rw [mem_biUnion]; constructor; intro h; exact ⟨wrap _ i,mem_univ _, mem_filter.mpr ⟨h,rfl⟩⟩; rintro ⟨x,-,h⟩; exact (mem_filter.mp h).1
 change (∑' x: Cover, f x)≤ _
 rw [tsum_eq_sum hh,hx,sum_biUnion]; swap; · intro x _ y _ h; exact disjoint_left.mpr fun i j k=> h ((mem_filter.mp j).2.symm.trans (mem_filter.mp k).2)
 let A:= powerV (0:Site n) i; let Y(x):= perk m A x* ‖F A x‖; let B(x:Site n):= powerV x j; have hf:∑ x: Site n, Y (B x)≤ k:=by
    have hp:Function.Injective B:= fun a b v=>congr_arg (fun z:Single n=> z.1.1) v
    rw [← sum_image (f:=Y) (g:=B) hp.injOn]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> mul_nonneg (by unfold perk; positivity) (norm_nonneg _))).trans (hz A) -- tune
 apply le_trans _ (mul_le_mul_of_nonneg_left hf (by positivity: 0≤ (4:ℝ)^m)); rw [mul_sum]; apply sum_le_sum; intro x _; let T:=portY x; have hk:0 < (T.card:ℝ):=by exact_mod_cast card_pos.mpr (port_p x)
 calc
   _ ≤ ∑ z∈T,(T.card:ℝ)⁻¹*(4^m*Y (B x)):= by
       apply sum_le_sum; intro z u; unfold f; obtain ⟨p',t⟩:= mem_filter.mp u; have hu: loft F z i j =(T.card:ℝ)⁻¹ • (Rush.wind (0:Site n) z • F A (B x)):=by
          unfold loft; rw [if_pos p']; unfold tapH; rw [t]; rfl
       rw [hu,norm_smul,norm_smul,Rush.wind,fee_norm,one_mul,Real.norm_of_nonneg (by positivity : 0≤(T.card:ℝ)⁻¹)]; refine (mul_le_mul_of_nonneg_right (paceS m z u i j) (mul_nonneg (by positivity) (norm_nonneg _))).trans_eq ?_; unfold Y B A; ring
   _ = _:=by rw [sum_const,nsmul_eq_mul, ←mul_assoc,mul_inv_cancel₀ hk.ne',one_mul]
include h
lemma pavR (m:ℕ)(u v:Site n)(i:V'): rakeV F m (powerV u i)= rakeV F m (powerV v i):=by
 let L(b:Site n): Equiv.Perm (Single n):= ((Equiv.addLeft b).prodCongr (Equiv.refl (SpinIdx))).prodCongr (Equiv.refl _)
 unfold rakeV paidX
 conv_lhs=> rw [← Equiv.sum_comp (L u)]
 conv_rhs=> rw [← Equiv.sum_comp (L v)]
 apply sum_congr rfl; rintro ⟨⟨x,p⟩,j⟩ _; let s:=(p,j); let y:=lift x
 have hg(t:Site n): perk m (powerV t i) (powerV (t+x) s)=(1+(2*separation (0:Site n) x:ℕ):ℝ)^m:=by
    unfold perk; rw [show separation _ _=2*separation (0:Site n) x from ?_]; change separation (node t) (node (t+x))= _; unfold node; rw [separation_translate]; rw [Ratio.root_embed,Ratio.root_embed,emptio]; congr 1; have hx:=separation_translate (0:Site n) x t; simpa [add_comm] using hx
 have hp(t:Site n): F (powerV t i) (powerV (t+x) s)= Rush.wind t y * tapH F y i s:=by
    have hv:= taff F h t y; rw [wrap_lift] at hv; exact Matrix.ext_iff.mpr hv i s -- tune
 change perk _ _ (powerV (u+x) s) * ‖F (powerV u i) (powerV (u+x) s)‖= perk _ _ (powerV (v+x) s)* ‖F _ (powerV (v+x) s)‖; rw [hp,hp,hg,hg]; simp [norm_mul,Rush.wind,fee_norm]
lemma daff {m:ℕ}(k:ℝ)(g: (∑ i:Single n,rakeV F m i)≤ Fintype.card (Site n)*k): ∀ i:Single n,rakeV F m i≤ k:=by
 rintro ⟨⟨b,i⟩,j⟩; apply le_of_mul_le_mul_left (LE.le.trans ?_ g) (by positivity)
 let A(v:Site n):= powerV v (i,j); rw [← show ∑ _i:Site n,rakeV F m (A b)=(Fintype.card (Site n):ℝ)*rakeV F m ((b,i),j) from (by simp only [sum_const,card_univ,nsmul_eq_mul]; rfl)]
 apply le_trans (b:=∑ i∈univ.image A,rakeV F m i) _ (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> sum_nonneg fun j _=> mul_nonneg (by unfold perk; positivity) (norm_nonneg _)); rw [sum_image (show Set.InjOn A _ from fun a _ c _ h=> congr_arg (fun y:Single n=>y.1.1) h)]; exact sum_le_sum fun a _=> (pavR F h m b a (i,j)).le
end YM.CF.Haro
