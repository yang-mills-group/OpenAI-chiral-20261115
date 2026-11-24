import YM.CF.BProof.Angular.Plaque

/- Relative geometry works with tile qualifications from eq:B-dy. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable (K : Chart G)(X : Design)

abbrev sizeP (y:ℝ):= coin y 1 (-2) 0
structure SizedP (P:ℕ)(y:ℝ): Prop where
  lower : sizeP y≤(P:ℝ)
  upper : (P:ℝ)<2*sizeP y
lemma sized_e (y:ℝ): sizeP y=(thresh y ^2)⁻¹:=by rw [coin_pow,coin_inv]; unfold sizeP; ring_nf

include K
lemma calm_D_p : ∃ C > (0:ℝ), ∀ᶠ y:ℝ in atTop, ∀ i:TAxis, group.chord (comm y (f₁ i) (f₂ i)) +4*xi y ≤ C*mA y ∧ C*mA y≤ thresh y/2:= by
 obtain ⟨C,hc,H⟩:= launch_face K (D:=1) one_pos
 obtain ⟨D,hD,E⟩:= bounds K
 have v:= mul_pos (a:=2) (by norm_num : 0<(2:ℝ)) hD; refine ⟨_,v,?_⟩
 filter_upwards [H,E,coin_budget (a:= -3/2) (b:=0) (c:=0) (d:= -1/2) (e:=3/4) (f:=0) (by norm_num) 4 D hD,coin_budget (a:= -1/2) (b:=3/4) (c:=0) (d:= -1/2) (e:=1) (f:=0) (by norm_num) (2*D) (1/2) (by norm_num)] with y H E hx hk
 let s:= (1:Side); let U:= mag (s:=s) y; let x : Space s:=0; let W:=sheet U 0; let k:= orient K y W x 0
 have he(i:TAxis): comm y (f₁ i) (f₂ i)=CF.BProof.Face.read W x i:=by simp only [W,U,Mag.comm,CF.BProof.Face.read,sheet,mag_h] -- tune
 intro i; rw [he]; have hm:Mood K y W x k:= (H s W x (fun i=> by rw [he,cd_self]; exact mul_nonneg zero_le_one (coin_pos ..).le) 0).1
 change 4*xi y<D*mA y at hx; change _*mA y<(1/2)*thresh y at hk; constructor <;> linarith [E s W x k hm i]
-- threshold buys for open prices. l ≥ sizeP y /2 use as qualification.
include X
lemma price_N : ∀ᶠ v:ℝ in atTop, v≥1 ∧ ∃ C > (0:ℝ), ∀ᶠ y:ℝ in atTop,∀ {s:Side} (S:Hall s)(a : Per s) (l:ℕ), S.K=K→ S.X=X→ Sized v S.g y S.k → X.k₀≤S.k → sizeP y≤2*(l:ℝ) →
    ∀ U:Config G s,∀ b:Eyes s,lifts a l y S U b →
      let r:= blendR X K S.g; let m:= C*mA y; (∀ i,Firm S.K (outlook a l S U b i) r m) ∧ r≤S.K.size ∧ max (qoriz (r:=r) (m:=m) S) (qnorm (r:=r) l S)+4*xi y ≤ thresh y/2:=by
 let B:=4*K.bump/group.colorScale*(K.C*X.K)^2
 have ht:=K.C_one; have hk:=zero_lt_one.trans_le ht; have hg:=X.budget; have hK:=group.colorScale_pos
 have h₀:0≤4*K.bump/group.colorScale:=div_nonneg (mul_nonneg (by norm_num) (K.bump_pos.le)) hK.le -- tune
 filter_upwards [eventually_ge_atTop (1:ℝ), (tendsto_pow_atTop (by decide : 2≠0)).eventually_ge_atTop (B*8)] with v hv hv'
 obtain ⟨C,hc,H⟩:= firm_read X K v (zero_lt_one.trans_le hv)
 let V:=2*K.size; have hV:0≤V:=by have := K.admitted; unfold V; positivity
 refine ⟨hv,C,hc,?_⟩
 filter_upwards [H,coin_budget (a:= -1/2) (b:=3/4) (c:=0) (d:=-1/2) (e:=1) (f:=0) (by norm_num) C (1/8) (by norm_num),coin_budget (a:=-3/2) (b:=0) (c:=0) (d:=-1/2) (e:=1) (f:=0) (by norm_num) 4 (1/4) (by norm_num),coin_budget (a:= -1) (b:=2) (c:=0) (d:=-1/2) (e:=1) (f:=0) (by norm_num) (K.C*4*V) (1/4) (by norm_num)] with y H h1 h2 h3
 intro s S a l e e' h hh hP U b hU
 rcases S with ⟨X',K',c,g,k⟩; dsimp only at *; subst X' K'; let S:Hall s:=⟨X,K,c,g,k⟩; let r:=blendR X K g; let m:=C*mA y; have hh' (i:Bool):= @H c s g k h hh (inlet a l U i) (b i) (hU i); have hr:r≤K.size:=(hh' false).2
 change C*mA y < (1/8)*thresh y at h1; change 4*xi y<(1/4)*thresh y at h2; have hp:0<sizeP y:=coin_pos ..; have hp':0<(l:ℝ):=by linarith
 let T:=4*K.bump/group.colorScale; have hk':0<(g.count.val:ℝ):=by positivity
 have heL:0<rY y:=coin_pos ..; have hc':=zero_lt_one.trans_le hv
 change (∀ i,Firm K (outlook a l S U b i) r m) ∧ r≤K.size ∧ _
 refine ⟨fun i=>(hh' i).1,hr,?_⟩; rw [← max_add_add_right]; apply max_le
 · have he : T*r^2 ≤ thresh y/8 :=calc
     _ = B/(g.count.val:ℝ)^2:=by unfold T r B blendR; ring
     _ ≤ B/(v*rY y)^2:=by gcongr; exact h.lower
     _ ≤ _ := by
        have hv : thresh y*(rY y)^2=1:=by rw [coin_pow,coin_mul]; ring_nf; rw [coin_zero]
        rw [div_le_iff₀ (by positivity)]; change B*8≤v^2 at hv'; rw [mul_pow]; nlinarith only [hv', show v^2*(thresh y*rY y^2)=v^2 by rw [hv,mul_one]] -- tune
   change C*mA y+T*r^2+_≤_; linarith
 change K.C*(2/(l:ℝ)*(2*r))+_≤_; have he:K.C*(2/(l:ℝ)*(2*r)) ≤ (1/4)*thresh y:= by
   apply le_trans (b:=K.C*(2/(l:ℝ)*V)) (by gcongr; change _≤2*K.size; gcongr) -- tune
   rw [show coin y (-1) 2 0=(sizeP y)⁻¹ from by rw [coin_inv]; ring_nf] at h3
   refine le_trans ?_ h3.le; calc
     _ ≤ K.C*(4/(sizeP y)*V):=by gcongr K.C*(?_ * V); rw [div_le_div_iff₀ hp' hp]; linarith
     _ ≤ _ := le_of_eq (by ring)
 linarith
end YM.CF.BProof.Angular
