import YM.SU5.FiniteGaugeData.ArchiveK.Exhibit
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedVariables false
noncomputable section
namespace Midway
open Violas LightK Concert Waltz
-- Buyer rate. Eventual in census height ℒ.Re/use/inertial param. `τ_d = d0 * L`.
variable {n u J i d k:ℕ}{x p q X σ C b y ε:ℝ}{G:E4≃ₗᵢ[ℝ] E4}(L:FilterK)(P:Set E4)
abbrev perF(x:ℝ)(n:ℕ):=Real.exp (x*n)
lemma peri (n:ℕ)(x y:ℝ) : perF x n*perF y n=perF (x+y) n:=by unfold perF; rw [←Real.exp_add]; ring_nf
lemma per_le(t:x≤y)(n:ℕ) : perF x n≤ perF y n:=by unfold perF; gcongr
#check lt_of_mul_lt_mul_right
#check gt_mem_nhds
lemma surge_powers (p q:ℝ)(r q':ℝ) (g:p < q) (i:ℕ) (t:0<q'): ∀ᶠ n:ℕ in atTop,(n:ℝ)^i * r * perF p n < q' * perF q n:=by
 let f(x:ℝ):= x^i * Real.exp (-(q-p)*x); have he:Tendsto f atTop (𝓝 0):=by
    have h:= tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (i:ℝ) (q-p) (sub_pos.mpr g); simpa only [Real.rpow_natCast] using h
 let H:= (tendsto_natCast_atTop_atTop (R:=ℝ)); filter_upwards [((by simpa using ((he.comp H).mul_const r) : Tendsto (fun n:ℕ=> f n*r) atTop (𝓝 0))).eventually (gt_mem_nhds t)] with n h; -- `gt_` direction maybe
 have u:= Real.exp_pos (q*n); refine lt_of_mul_lt_mul_right ?_ (a:= (perF q n)⁻¹) (by unfold perF; positivity) -- tune lemma
 rw [mul_assoc (q':ℝ),mul_inv_cancel₀ (show perF q n≠0 from u.ne'),mul_one]; refine lt_of_le_of_lt (le_of_eq (b:= f n*r) ?_) h; unfold f perF; rw [mul_assoc,← Real.exp_neg,←Real.exp_add]; ring_nf
-- polynomial buffer
lemma block_cnt(n:ℕ) : (Lattice.box n).card=(2*n+1)^4:=by
 rw [Lattice.box,Pi.card_Icc]; simp_rw [Int.card_Icc]; rw [Finset.prod_const, card_univ,Fintype.card_fin]; have hp: ((n:ℤ)+1- -(n:ℤ)).toNat=2*n+1:= by omega
 rw [hp]
lemma volumeP(n:ℕ) : page (Beam (box n))= (2*n+1)^4 *4:=by unfold Beam page; rw [Fintype.card_prod,Fintype.card_coe, block_cnt,Fintype.card_fin]
lemma volumeP_m {A B:Finset Cover} (g:A⊆ B): page (Beam A) ≤ page (Beam B):= by unfold Beam page; rw [Fintype.card_prod, Fintype.card_prod,Fintype.card_coe,Fintype.card_coe]; gcongr
lemma volumeQ(n D:ℕ)(p:0<n): page (Beam (box (n*D))) ≤ n^4 * (2*D+1)^4*4 := by rw [volumeP, ← mul_pow]; apply Nat.mul_le_mul_right; gcongr; nlinarith only [p]
-- abbrevi λ.P.Dens.L.
abbrev TokenF(ε:ℝ):= ε+50000
lemma cloak_buy (t:400≥q):True:=trivial -- remove
-- inputs multiplicity i≠0; k=loss choose ∀; earn.Frame. combine . ℝ. pages limited since A⊆box n; B⊆box n. T comparison box n*(1+d). coupling. use nat.M sought n≫. 
def lien (G:E4≃ₗᵢ[ℝ] E4) (F:FilterK) (K σ C ε q:ℝ) (i d n r:ℕ): Prop:= let A:= box n; let T:=box (n+d*n); let m:=i*n^3; let J:=64*i;
 page (Invoice r)+m ≤2*m ∧
  2*(2*m*4+J^2* page (BddT r)) < J*n^3 ∧
 ∀ a b t:ℕ, a≤page (Beam A) → b ≤ page (Beam A) → t≤page (Beam T) →
  perF (-8192) n * coins G F (J*n^3) a b + ((J*n^3:ℕ):ℝ)^2*(bumble G F*q^r)< perF (-4096) n ∧
  stake K b t m (perF 8192 n) ≤ perF 16384 n ∧ inertial K q σ C b t m (d*n) r (perF 8192 n) ≤ perF (-ε) n -- includes each .
lemma quota (J:ℕ) (q:ℕ) (xt: ((64*J)^2+1)*500*q ≤ (q*q)^2):True:=trivial -- helper. choose `≥ scal`. 
lemma squares(i:ℕ)(u:0 < i) : ∃ q:ℕ,0<q ∧ ∀ x:ℕ,0<x → let n:= x*q; let m:= i*n^3; let j:=64*i;
    page (Invoice x)+m ≤ 2*m ∧ 2*(2*m*4+j^2*page (BddT x))<j*n^3:= by
 let j:=64*i; let q:= 10000*j^2; have ht:0<j:=Nat.mul_pos (by omega) u; have he:0<q:= (by unfold q; positivity); refine ⟨q,he, ?_⟩; intro x h n m J -- j shadow variable. tuning
 let z:= page (BddT x); have hb:z≤54*x^3:=by rw [show z= _ from BasisK_dim]; have hx:2*x+1 ≤3*x:=(by omega); nlinarith only [Nat.pow_le_pow_left hx 3] -- tune exponents
 have hm: page (Invoice x)= z*4:= (by unfold page Invoice; rw [Fintype.card_prod,Fintype.card_fin]); -- arithmetic plan j² z ≤ m, invoice z ≤ ≤m via size factor.g.Y
 have h1:54*4*x^3 * j^2 ≤ m:= by
    unfold m n; have hj:216*j^2 ≤ q:= by unfold q; omega; -- precedence
    calc 54*4*x^3*j^2 = (216*j^2)* x^3 := by ring
         _ ≤ q*x^3:= by gcongr
         _ ≤ q^3*x^3:= by gcongr; exact Nat.le_self_pow (by omega) _
         _ ≤ i*(x*q)^3:= le_trans (le_of_eq (by ring : q^3*x^3=1*(x*q)^3)) (Nat.mul_le_mul_right _ u)
 have ht: 1≤ j^2:= Nat.one_le_pow _ _ ht; change page (_) +_ ≤ _ ∧ 2*(2*m*4+j^2*z) < j*n^3; rw [hm, show j*n^3=64*m from (by unfold j m; ring)]; have hu:0<m := Nat.mul_pos u (by unfold n; positivity); have hy:= Nat.mul_le_mul_left (j^2) hb; constructor <;> nlinarith only [h1,ht,hb,hy,hu, show x^3*1 ≤ x^3*j^2 from Nat.mul_le_mul_left _ ht]
 -- ...
section scale
variable (G:E4≃ₗᵢ[ℝ] E4)(K σ C ε:ℝ)(t:0≤ε)(d0:0<σ)(s0:0≤C)(v:0≤K)
variable (P Q i:ℕ) (u:0<Q)(s: TokenF ε ≤ σ *P)
local notation "Θ"=> perF (-TokenF ε)
local notation "Xq"=> perF 8192
include t d0 s0 v s
lemma earning : ∀ᶠ n:ℕ in atTop,∀ r:ℕ, ∀ D:ℝ,D^r ≤ perF (-TokenF ε) n → ∀ t b a:ℕ, b ≤ page (Beam (box n))→a≤page (Beam (box n)) → t≤page (Beam (box (n + P*n))) → let m:=i*n^3; let J:=64*i;
 perF (-8192) n * coins G L (J*n^3) a b + ((J*n^3:ℕ):ℝ)^2*(bumble G L* D^r)< perF (-4096) n ∧ stake K b t m (perF 8192 n) ≤ perF 16384 n ∧ inertial K D σ C b t m (P*n) r (perF 8192 n) ≤ perF (-ε) n:= by
 let J:= 64*i; let β:= fareQ G; let ξ:=sir L; let y:=bumble G L; have heβ:0≤β:=fare_n _; have heξ:0≤ξ:=sir_n _; have hy:0≤ y:=bumble_n ..;
 let N:ℝ:=324; let T:ℝ:=(2*((1:ℕ)+ P:ℝ)+1)^4*4; have ht:0≤T:=by unfold T; positivity; -- cast weird
 let U:= TokenF ε; have hh:0<pride C:=pride_p _ s0; let A:= fareQ G*sir L*(J:ℝ)^2*N*N; let Y:=y*(J:ℝ)^2; let W:= T*i*4*N*K; have hu:0≤ W:=by unfold W N; positivity;
 let V1:=(4*N*pride C+ (C*4*N*rover)); let V2:= C*W + T*i*V1; have hp:0≤V1:=by have hm:= rover_n; unfold V1 N; positivity
 have hq: U≥50000:=by unfold U TokenF; linarith only [t]
 filter_upwards [surge_powers (-8192) (-4096) A (1/2) (by norm_num) 14 (by norm_num),surge_powers (-U) (-4096) Y (1/2) (by linarith only [hq]) 6 (by norm_num),surge_powers 8192 16384 W 1 (by norm_num) 11 (by norm_num),surge_powers (8192-U) (-ε) V2 1 (by unfold U TokenF; linarith only [hq]) 11 (by norm_num), eventually_gt_atTop 0] with n H h Hp Hq Hn r D p a x q z₁ z₂ w m J
 -- a t_upper=T size. x lower b. q upper a. z₁ x; z₂ q. shadow J ok.
 let M:ℝ:= n; have hm':(m:ℝ)=i*M^3:= by unfold m M; push_cast; rfl
 let t'_:= perF 8192 n; let τ' := perF (-TokenF ε) n
 have hv:0<t'_:= Real.exp_pos _; have hv0:0<τ':=Real.exp_pos _; have hw:(page (Beam (box n)):ℝ)≤ M^4*N:= (by have he:=volumeQ n 1 Hn; rw [mul_one] at he; apply (Nat.cast_le.mpr he).trans (le_of_eq ?_); unfold M N; push_cast; ring)
 have hz:(x:ℝ)≤ M^4*N:= (Nat.cast_le.mpr z₁).trans hw; have hz':(q:ℝ)≤ M^4*N:= (Nat.cast_le.mpr z₂).trans hw; have hz₁:(a:ℝ)≤ M^4*T:= by
    rw [show n+P*n=n*(1+P) from (by ring)] at w; refine (Nat.cast_le.mpr (w.trans (volumeQ n (1+P) Hn))).trans_eq ?_ -- trans_eq on LE? ok
    unfold T M; push_cast; ring
 have hp'(x:ℕ): x*0 =0:= by ring -- unused. use t foot
 have hs: stake K x a m t'_ ≤ M^11*W*t'_:= by
    unfold stake; rw [hm']; have hs:0≤M:=Nat.cast_nonneg n; refine le_trans (b:=M^4*T*((i:ℝ)*M^3)*(4*(M^4*N)*K*t'_)) ?_ (le_of_eq ?_); · gcongr
    unfold W; ring
 have hk:(↑(J*n^3:ℕ):ℝ)^2= (J:ℝ)^2 * M^6:=by unfold M; push_cast; ring
 refine ⟨?_, hs.trans (by simpa [M,t'_] using Hp.le),?_⟩;
 · let f:= perF (-8192) n; let c:=bumble G L; change f*coins G L _ _ _ + _ < _;
   have h1:f*coins G L (J*n^3) q x ≤ M^14*A*f:=by
      apply le_trans (b:=f*(β*ξ*((J:ℝ)*M^3)^2*(M^4*N)*(M^4*N))) ?_ (le_of_eq ?_);
      · unfold coins; rw [Nat.cast_mul, Nat.cast_pow]; have :0≤f:=(Real.exp_pos _).le; change f*(β*ξ*((J:ℝ)*M^3)^2*q*x) ≤_; gcongr
      unfold A; unfold β ξ J -- issue `J` earlier vs introduced J here.H.P.
      ring
   rw [hk]; have h2: (J:ℝ)^2 *M^6*(bumble G L*D^r) ≤ M^6*Y*τ':=by
      calc _ ≤ _ * _*(bumble G L*τ') := by gcongr
           _ = _ := by unfold Y y J; ring -- tune
   apply lt_of_le_of_lt (add_le_add h1 h2); change M^14*A*f < _ at H; change M^6*Y*τ' < _ at h; linarith only [h,H]
 let y:= Real.exp (-σ*↑(P*n:ℕ)); have he: y ≤ τ':= by apply Real.exp_monotone; push_cast; nlinarith only [mul_le_mul_of_nonneg_right s (show 0≤(n:ℝ) from Nat.cast_nonneg _)]
 let c:=feeKX x σ C D (P*n) r; have hτ:c ≤ M^4*V1*τ':= by
    change 4*(x:ℝ)*y*pride C+(C*4*x*rover)*D^r ≤_; have hv1:0≤N:=(by unfold N; norm_num); have hrb:= rover_n;
    apply le_trans (b:=4*(M^4*N)*τ'*pride C+(C*4*(M^4*N)*rover)*τ') ?_ (le_of_eq ?_); · -- gcongr issue D^r nonneg unknown. use multiply monotone.Const
      apply add_le_add; gcongr; refine le_trans (b:= C*4*x*rover *τ') ?_ ?_ <;> gcongr
    unfold V1; ring
 have hZ: inertial K D σ C x a m (P*n) r t'_ ≤ M^11*V2*(τ'*t'_):=by
    unfold inertial; have hz: 0≤(stake K x a m t'_):=by unfold stake; positivity
    have hv1:0≤ M:=Nat.cast_nonneg _
    change y*C*_+(a:ℝ)*m*(c*t'_)≤_; apply le_trans (b:=τ'*C*(M^11*W*t'_)+(M^4*T)*(m:ℝ)*(M^4*V1*τ'*t'_)) ?_ (le_of_eq ?_);
    · apply add_le_add; gcongr; refine le_trans (b:=a*(m:ℝ)*(M^4*V1*τ'*t'_)) ?_ ?_ <;> gcongr
    rw [hm']; unfold V2; ring
 apply hZ.trans; unfold τ' t'_ U at *; rw [peri,show -TokenF ε+8192 =8192-TokenF ε from (by ring)]; simpa [M] using Hq.le -- tune unfolds
#print axioms earning
end scale
end Midway
end
end YM.CF.Window.ArchiveK
