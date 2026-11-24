import YM.SU5.FiniteGaugeData.Nine.Gamma
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N : Side} {k:ℕ} {d b:ℝ}
section spin
open Brique
variable (k :ℕ) (M:Tulip.Male)(N:Side)(i:Axis)
local notation "b" x:max=> Brique.Φ0 k M x
local notation "g" x:max=> mixL k M.val x
local notation "s" x:max=> skin k M.val x
local notation "f" x:max=> shell k M.val x
local notation "U"=> (0: SpinIdx)
local notation "D"=> (3: SpinIdx)
abbrev η (v:Site N)(i:Axis) :ℝ:= (skin k M.val (mel v) i).re -- N arg order
lemma physicalR (v:Site N) : physical (skin k M.val (mel v)):=by
 rw [skin_mix k _ (base_subset_realCube zone_pos (mel_h _)),pilot_add]; rw [physical_iff]; let t:= phys_mix k M.val M.property _ (mel_h v).1; intro i; specialize t; simp only [Pi.smul_apply,smul_eq_mul,Complex.mul_im,Complex.ofReal_im,(physical_iff _).mp t, zero_mul,mul_zero,zero_add]
lemma eta_v (v:Site N) : (η k M N v i:ℂ)= skin k M.val (mel v) i:=by obtain u:=(physical_iff ..).mp (physicalR k M N v) i; exact Complex.ext rfl (by rw [u]; rfl)
private lemma A_sq (v:Site N) : (∑ i:Axis,(skin k M.val (mel v) i)^2)=(f (mel v))*(1-f (mel v)):=by
 let x:=mel v; let t:= base_subset_realCube zone_pos (mel_h v); let p:= skin_mix k M.val t; let h:=phys_mix k M.val M.property x t.1; simp_rw [p,Pi.smul_apply,smul_eq_mul,mul_pow,←mul_sum]; let z:=f x; let g':=g x; let S:=prodM g' g'; have he:S=∑ i:Axis,(g' i)^2:=by unfold S prodM; simp only [pow_two]
 have hp: (1+S)*z=1:=by rw [show z=_ from shell_inv k M.val t (mel_away v)]; exact mul_inv_cancel₀ (graphs_ne h)
 change z^2 * ∑ i:Axis,(g' i)^2=z*(1-z); rw [←he]; linear_combination z*hp
lemma cost_glow (v:Site N): (∑ i:Axis,(η k M N v i)^2)= (b v)*(1-b v):= by
 suffices h: ↑(∑ i:Axis,(η k M N v i)^2) = (↑(b v):ℂ)*(1-↑(b v)) by exact_mod_cast h
 push_cast; simp_rw [eta_v]; rw [A_sq,pilot_add]
-- perm swaps without SIGN on mel. hold altitude.
abbrev bl (i j:Axis): Signed:=⟨Equiv.swap i j,fun _=>false⟩
lemma scape (v:Site N)(e j:Axis):mel ((bl e j).act v)= cadence (bl e j) false (mel v):= by
 funext i; obtain ⟨i,rfl⟩:= (bl e j).perm.surjective i; unfold cadence; simp [mel,tmap, pm,bl,Signed.act]
lemma bond (v:Site N)(se j:Axis):
 shell k M.val (mel ((bl se j).act v))= shell k M.val (mel v) ∧ skin k M.val (mel ((bl se j).act v))= cadence (bl se j) false (skin k M.val (mel v)):=by
 let fe:= base_subset_realCube zone_pos (mel_h v); let h:=base_subset_realCube zone_pos (mel_h ((bl se j).act v)); let a:= scape N v se j; have he: shell k M.val (mel ((bl se j).act v))=shell k M.val (mel v):=by rw [shell_inv _ _ h (mel_away _), shell_inv _ _ fe (mel_away _), a, mixL_s _ M.property,prod_s]
 refine ⟨he,?_⟩; rw [skin_mix k _ h,skin_mix k _ fe, he,a,mixL_s _ M.property,cadence_m] -- `rw a` risk
lemma equal_trip (i j:Axis) : (∑ x:Site N,(η k M N x j)^2)= ∑ x:Site N,(η k M N x i)^2:=by
 let t:=(bl i j).actEquiv (R:=Per N); rw [← Equiv.sum_comp t.toEquiv]; apply sum_congr rfl; intro x v; unfold η; rw [show t.toEquiv x=(bl i j).act x from rfl,(bond k M N x i j).2]; simp [bl,cadence,Signed.act] -- tune Signed.act simp.
lemma same_twice :(2:ℝ)*(∑ i:Site N,((η k M N i 0)^2+(η k M N i 1)^2)) = ∑ i:Site N,(b i)*(1-b i):=by
 simp_rw [← cost_glow]; rw [sum_comm,sum_add_distrib]; let E(i:Axis):=∑ x:Site N,(η k M N x i)^2; have he(i:Axis):E i=E 0:= equal_trip k M N 0 i; rw [show (∑ i:Axis,E i)=(∑ _:Axis,E 0) from sum_congr rfl (fun i _=> he i),←he 1, sum_const, nsmul_eq_mul,card_fin] -- tune he orientation let
 push_cast; change 2*( E 0+E 1)=4*(E 1); rw [he 1]; ring
lemma tender_neg (v:Site N):shell k M.val (mel (backN v))=f (mel v) ∧ skin k M.val (mel (backN v))= - (s (mel v)):=by
 obtain ⟨w,a⟩:= dollar v; let x:= mel v; let p:=base_subset_realCube zone_pos (mel_h v); let u:=base_subset_realCube zone_pos (mel_h (backN v)); let t:= realCube_neg p; have h: shell k M.val (mel (backN v))= f (mel v):= by rw [shell_inv k _ u (mel_away _),shell_inv k _ p (mel_away _),show mel (backN v)=_ from a,mix_period,mix_neg _ _ M.property]; simp [prodM]
 refine ⟨h,?_⟩; rw [skin_mix k _ u, skin_mix k _ p,h, show mel (backN v)=_ from a,mix_period,mix_neg _ _ M.property,smul_neg]
lemma dawn_cross : ∑ v:Site N,(((1-bar k M.val (mel v)) * cutM {D} * (1-bar k M.val (mel v))) U D) = 0:= by
 simp_rw [cross_norm]; let F(v:Site N):=(shell k M.val (mel v))*(-(skin k M.val (mel v) 0)+Complex.I*(skin k M.val (mel v) 1)); change (∑ i,F i)=0; have he(i): F (backN i)= - F i:=by unfold F; rw [tender_neg k M N i|>.1,(tender_neg k M N i).2]; simp only [Pi.neg_apply]; ring
 have ht:= Equiv.sum_comp (backN (N:=N)) F; simp_rw [he,sum_neg_distrib] at ht; exact neg_eq_self.mp ht -- check
end spin
open Brique
private lemma mpos (x:Site N): mel x ∈ realCube zone:= base_subset_realCube zone_pos (mel_h x)
lemma ξn(k:ℕ)(M:Tulip.Male)(x:Site N):(0:ℝ)≤Φ0 k M x:=norm_nonneg _
lemma ξb(k:ℕ)(M:Tulip.Male)(x:Site N):Φ0 k M x≤1:=by
 let p:=mel x; let v:=mixL k M.val p; let S:ℝ:=∑ i:Axis,(v i).re^2; have h:S≥0:= sum_nonneg fun i _=>sq_nonneg _
 have ht := pilot_add k M x; rw [shell_inv _ _ (mpos x) (mel_away x),prodM_self _ (phys_mix k M.val M.property _ (mpos x).1)] at ht; change (1+ (S:ℂ))⁻¹=( _ :ℝ) at ht -- tune
 have hx: (1+S)⁻¹=Φ0 k M x:=by exact_mod_cast ht
 rw [←hx]; exact inv_le_one_of_one_le₀ (by linarith)
private lemma arrange {V:ℕ}(h:4≤ V)(t:V ≤ N.val):∃ T:ℕ,0<T ∧ N.val ≤ (T+1)*V ∧ T*V≤N.val:=by
 have he:0<V:=by omega
 refine ⟨N.val/V, Nat.div_pos t he, (by rw [Nat.add_mul,Nat.one_mul]; have h1:= Nat.mod_add_div N.val V; have h2:= Nat.mod_lt N.val he; rw [mul_comm] at h1; omega),Nat.div_mul_le_self ..⟩
abbrev rubra (k:ℕ)(N:Side)(M:Male):= ((N.val:ℝ)^4)⁻¹*(∑ i:Site N,((Φ0 k M i)*(1-Φ0 k M i)))/2 -- parentheses big operator! denotes ∑(per /2) Lean? Need mean after same_twice.
abbrev villa (k:ℕ)(N:Side)(M:Male):= ((N.val:ℝ)^4)⁻¹ * (∑ i:Site N,(Φ0 k M i)^2)
lemma duly (k:ℕ)(hk:1≤k):∃ c:ℝ,0<c∧ c<1∧ ∃ V:ℕ,∀ N:Side,V ≤ N.val→∀ M:Tulip.Male, c ≤ rubra k N M ∧ c ≤ villa k N M:=by
 obtain ⟨b,T,g,e,P⟩:=Jill.zip hk
 -- choose V so T* (4*pi)^2 / V^2 small
 let x:= 2*T*(4*Real.pi)^2
 obtain ⟨i,u⟩:= exists_nat_gt x; let v:=i+4; have he:4≤v:=by omega
 have hp:4≤(v:ℝ):= Nat.ofNat_le_cast.mpr he; have hv:0<(v:ℝ):=by linarith
 have ht : T*(4*Real.pi/v)^2 ≤ 1/2:=by
    have hx:x ≤ (v:ℝ):= u.le.trans (Nat.cast_le.mpr (show i ≤ v from by omega)); unfold x at hx; rw [div_pow, ←mul_div_assoc]; apply (div_le_iff₀ (pow_pos hv _)).mpr; nlinarith only [hx,sq_nonneg ((v:ℝ)-1),hp]
 let q:= Real.pi/v; let f:= ((2*(v:ℝ))^4)⁻¹*(min (b*q^2) (1/2))^2 /2; let w:= min f (1/2); have hy:0< q:=by unfold q; positivity
 have hh:0 < w:=lt_min (half_pos (mul_pos (inv_pos.mpr (by positivity)) (pow_pos (lt_min (by positivity) (by norm_num)) _))) (by norm_num)
 refine ⟨w,hh,(min_le_right ..).trans_lt (by norm_num),v,fun N t M=>?_⟩; obtain ⟨j,h,H,S⟩:=arrange he t
 have l(i:Site N): Jill.Bound Real.pi (pm i):=(pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun x=> abs_le.mpr ⟨(pm_zone i x).1.le,(pm_zone i x).2⟩
 have hz(i:Site N)(g':i∈spanned j N): min (b*q^2) (1/2)≤ Φ0 k M i ∧ min (b*q^2) (1/2) ≤ 1-Φ0 k M i:=by
    let X':= l i; obtain ⟨p,w⟩:= P M (pm i) X'; obtain ⟨r,v⟩:=travel_budget he H S h i g'
    have hr : b*q^2 ≤ b*‖pm i‖^2:=by gcongr; -- tune q nonneg
    have hy: Φ0 k M i ≤ 1/2:= w.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) v _) e.le).trans ht); exact ⟨(min_le_left ..).trans (hr.trans p), (min_le_right ..).trans (by linarith)⟩
 let A:=min (b*q^2) (1/2); have hA(i y:ℝ)(hi:i≥A)(hv:y≥A):A^2 ≤ i*y:= by
    have h:0≤A:= le_min (by positivity) (by norm_num); rw [pow_two]; exact mul_le_mul hi hv h (h.trans hi)
 have hz':= tiny_funds he H S h (fun i=> (Φ0 k M i)*(1-Φ0 k M i)) (A^2) (by positivity) (fun i=> mul_nonneg (ξn k M i) (sub_nonneg.mpr (ξb k M i))) (fun i u=> hA _ _ (hz i u).1 (hz i u).2)
 have hw:= tiny_funds he H S h (fun i=> (Φ0 k M i)^2) (A^2) (by positivity) (fun _=>sq_nonneg _) (fun i u=>pow_two (Φ0 k M i) ▸ hA _ _ (hz i u).1 (hz i u).1)
 dsimp only [A] at hz' hw; have he:w ≤ f:= min_le_left ..; unfold f at he; unfold rubra villa; constructor <;> linarith
lemma ax_top (k:ℕ)(N:Side)(M:Male): rubra k N M ≤1 ∧ villa k N M ≤ 1:=by
 let n:=(N.val:ℝ)^4; have he:0<n:=pow_pos (nPos N) _; have h(F:Site N→ℝ)(t:∀ i,F i ≤1): n⁻¹*(∑ i: Site N,F i) ≤ 1:=by
    have hz:(∑ i:Site N,F i) ≤ ∑ _i:Site N,(1:ℝ):= sum_le_sum (fun i _=>t i); simp only [sum_const,card_univ,site_card,nsmul_eq_mul,mul_one,Nat.cast_pow] at hz; exact (mul_le_mul_of_nonneg_left hz (inv_pos.mpr he|>.le)).trans_eq (inv_mul_cancel₀ he.ne')
 have hv:= h _ (fun i=> show (Φ0 k M i)*(1-Φ0 k M i)≤ 1 from ((mul_le_of_le_one_right (ξn k M i) (by linarith only [ξn k M i])).trans (ξb k M i))); exact ⟨(show _ /2 ≤ (1:ℝ) from by linarith), h _ (fun i=> pow_le_one₀ (ξn k M i) (ξb k M i))⟩
#print axioms duly
end YM.CF.Window.Pivot
