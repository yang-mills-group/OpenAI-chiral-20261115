import YM.SU5.SatinWard.Resolution.WardGeom
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Filter Metric
open scoped Topology NNReal
namespace Carousel
/- Mixed quadrature expenditure, needed for true multi price. Already uniform on the unselected price axes, without C* algebra assumptions.
-/
variable (M: Mesh) {α:ℝ} {X G I:Type*} [NormedAddCommGroup X][NormedSpace ℝ X][AddCommGroup G] (D:I→ℕ→G) (u:X) {f:G→X}
variable (C:ℝ)(p:0<α)(e:α<1)
variable (U:PaidR M D)(F:Spark M D C f α)
local notation "σ" h:max=> (mill M h:ℝ)
local notation "Λ"=> (M.L:ℝ)
local notation "Φ" i:max h:max=> boltDiff M D i h f
local notation "Δ" g:max i:max h:max=> stroll D g i h
local notation "α✧" v:max=> (σ v)^α
local notation "AX" h:max=> (σ h)^(1+α:ℝ)
noncomputable def strollBudget (M:Mesh)(α:ℝ):ℝ:=4/( (mill M 0:ℝ)^(1+α:ℝ))+4*M.L/(1-(M.L:ℝ)^(α-1))
local notation "E"=>strollBudget M α
include p e
lemma scale_four : 0< 4/( (mill M 0:ℝ)^(1+α:ℝ)) ∧ 0< 4*Λ/(1-Λ^(α-1)):=by
 have hp0:=gear_pos M 0; have h:=gear_inc M; have hx:Λ^(α-1)<1:=Real.rpow_lt_one_of_one_lt_of_neg h (by linarith); exact ⟨by positivity,div_pos (by positivity) (sub_pos.mpr hx)⟩
omit p e
include F U
lemma stroll_fare (x:G)(i:I)(v:ℕ):
 ‖((M.L:ℝ)⁻¹ • (stroll D f i v x))-stroll D f i (v+1) x‖ ≤ Λ*C*((σ (v+1))^(1+α:ℝ)):=by
 let h:=drift_v M D C U F i x v; let A:= Δ f i v; let B:= D i v; let Q:= (Φ i v) x; let Y:=(Φ i (v+1)) x; let r:= σ (v+1); have hp:=gear_inc M; have h₀:= gear_pos M (v+1); have ht:0< r:=gear_pos ..
 have he: Λ⁻¹ • ((Δ f i v) x)=r • Q:=by change _=r • ((σ v)⁻¹ • ((Δ f i v) x)); rw [speedup M v, smul_smul, ←show r=σ (v+1) from rfl, mul_inv_rev,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
 rw [he, show stroll D f i (v+1) x= r • Y from (smul_inv_smul₀ ht.ne' _).symm,←smul_sub,norm_smul,Real.norm_of_nonneg ht.le]; refine (mul_le_mul_of_nonneg_left h ht.le).trans_eq ?_; unfold r; rw [Real.rpow_add h₀,Real.rpow_one]; ring
-- mixed cost.
omit F U in
lemma stroll_comm (i j:I)(k l:ℕ)(x:G):stroll D (Δ f i k) j l x= stroll D (Δ f j l) i k x:=by unfold stroll; rw [add_right_comm x]; abel
include p e
lemma mixed (i j:I)(x:G)(v:ℕ): ‖stroll D (Δ f i v) j v x‖≤C*E*(AX v):=by
 let K:= E; let V:= C*K; let h0:=gear_inc M; have h₀:0<Λ:=zero_lt_one.trans h0; let W(k:ℕ):= stroll D f i k; let B:= Λ^(α-1); let A:= Λ^(1+α:ℝ); have h₁:0<Λ^(α-1):=by positivity
 have hx0:Λ^(α-1)<1:=Real.rpow_lt_one_of_one_lt_of_neg h0 (by linarith); have he:4*Λ+K*(Λ^(α-1))≤K:=by
    let δ:=1-B; have hδ:0<δ:=sub_pos.mpr hx0; let hs(V:ℝ)(b:0≤V):V+4*Λ/(1-B)≥ 4*Λ+(V+4*Λ/(1-B))*B:=by
       have hx:4*Λ/δ *δ=4*Λ:=div_mul_cancel₀ _ hδ.ne'; unfold δ at hx; nlinarith only [hx,mul_le_of_le_one_right b hx0.le] -- V ≥ V*B
    exact hs _ (scale_four M p e).1.le
 have hv:0≤C:= F.pos
 induction v generalizing x with
 | zero=>
    let d:=σ 0; have hd:0< (AX 0):=Real.rpow_pos_of_pos (gear_pos _ _) _; have h:(4:ℝ)/(AX 0)≤E:= by unfold strollBudget; exact le_add_of_nonneg_right (scale_four M p e).2.le
    unfold stroll; refine (norm_sub_le ..).trans (le_trans (add_le_add ((norm_sub_le ..).trans (add_le_add (F.norms _) (F.norms _))) ((norm_sub_le ..).trans (add_le_add (F.norms _) (F.norms _)))) ?_); nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ hd).1 h) F.pos]
 | succ v ih=>
    let w:=(Δ (W v) j v) x; let T:=(Λ*C*(AX (v+1))); let t:= Λ⁻¹; have ht0:0≤ T:=by unfold T; have ht:=gear_pos M (v+1); positivity; -- all
    have ht:0≤ t:=(inv_pos.mpr h₀).le
    have hr:t≤1:=inv_le_one_of_one_le₀ h0.le
    have hp(b k:I)(l:ℕ)(y:G) : ‖t • (stroll D (Δ f k v) b l y)- stroll D (Δ f k (v+1)) b l y‖≤2*T:= by
       rw [show t • (stroll D (Δ f k v) b l y)-stroll D (Δ f k (v+1)) b l y=(t • (stroll D f k v (y+D b l))-stroll D f k (v+1) (y+D b l)) - (t • (stroll D f k v y)- stroll D f k (v+1) y) from ?_]; exact (norm_sub_le ..).trans ((add_le_add (stroll_fare M D C U F _ _ _) (stroll_fare M D C U F _ _ _)).trans_eq (two_mul T).symm); unfold stroll; module
    let z:= stroll D (W v) j (v+1) x; let u:=t • z; let y:= stroll D (Δ f i (v+1)) j (v+1) x
    have h': ‖(t*t) • w-u‖≤2*T:=by
       rw [mul_smul]; unfold u; rw [←smul_sub,norm_smul,Real.norm_of_nonneg ht]
       have hx:‖t • w-z‖≤2*T:=by unfold w z W; rw [stroll_comm D i j v v x, stroll_comm D i j v (v+1) x]; exact hp i j v x
       exact (mul_le_mul_of_nonneg_left hx ht).trans (mul_le_of_le_one_left (by positivity) hr)
    have hx:‖t • (stroll D (W v) j (v+1) x)-y‖≤2*T:=hp j i (v+1) x; let g:=(t*t) • w; have hu:‖g-y‖ ≤ 4*T:=(norm_sub_le_norm_sub_add_norm_sub _ u _).trans ((add_le_add h' hx).trans_eq (by ring))
    have hk:‖g‖≤ (t*t)*(C*K*(AX v)):=by rw [show g=(t*t) • w from rfl,norm_smul,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (ih x) (by positivity)
    have hp:‖y‖≤ ‖g‖+‖g-y‖:= Eq.trans_le (congrArg norm (show y= g-(g-y) from (by abel))) (norm_sub_le ..)
    refine hp.trans ((add_le_add hk hu).trans ?_); rw [sideScale M v]; have hv:t*t*Λ^(1+α:ℝ)=Λ^(α-1):=by unfold t; rw [←Real.rpow_neg_one Λ,←Real.rpow_add h₀,←Real.rpow_add h₀]; ring_nf
    have hh:0≤ AX (v+1):= by have ht:= gear_pos M (v+1); positivity
    calc
       _ = (4*Λ+K* (Λ)^(α-1))*C*(AX (v+1)):=by unfold T; nth_rw 1 [←hv]; ring
       _ ≤ _:=by rw [mul_comm C E]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he F.pos) hh
variable [CompleteSpace X]
noncomputable def κK(α:ℝ):ℝ:=2*roseMax M α+strollBudget M α
omit U F in
lemma κK_pos:0<κK M α:=add_pos (by have t:=rosePos M p; positivity) (add_pos (scale_four M p e).1 (scale_four M p e).2)
lemma at_spiral (i j:I)(x:G)(v:ℕ): let B:=gradPrice (f:=f) M D i; ‖B (x+D j v)-B x‖ ≤ C*(κK M α)*(α✧ v):=by
 intro B; let y:=x+D j v; let F':=Φ i v; let Eℓ:=C*roseMax M α*(α✧ v); let z:=σ v; have h₁:= gear_pos M v
 have hv:‖F' y-F' x‖≤ C*E*(α✧ v):=by
    change ‖z⁻¹ • (Δ f i v) y-z⁻¹ • (Δ f i v) x‖≤_; rw [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_pos.mpr h₁).le]; refine (mul_le_mul_of_nonneg_left (mixed M D C p e U F i j x v) (by exact (inv_pos.mpr h₁).le)).trans_eq ?_; rw [Real.rpow_add h₁,Real.rpow_one]; field
 have hp:‖B y-F' y‖≤ Eℓ:= (quorum M D C p U F ..).2; have hx:‖F' x-B x‖≤Eℓ:= (norm_sub_rev ..).trans_le (quorum M D C p U F ..).2
 change ‖B y-B x‖≤_; exact (norm_sub_le_norm_sub_add_norm_sub _ (F' y) _).trans ((add_le_add hp ((norm_sub_le_norm_sub_add_norm_sub _ (F' x) _).trans (add_le_add hv hx))).trans_eq (by unfold κK Eℓ; ring))
#print axioms at_spiral
end Carousel
end YM.CF.Buffered.Afterglow.Tower.MeshClock
