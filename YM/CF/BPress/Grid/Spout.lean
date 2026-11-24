import YM.CF.BPress.Grid.Double
/-! Frame smoothing dyadic tower, estimate & lookup radii at all strata. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid.Half
open Function Filter Lattice Finset SU MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
local notation "nρ" => fun i:ℕ => 2^i
private def chargeA (C b r R : ℝ) := (2*C - C*b*(r/R))*(r/R)
private lemma moment_note {δ K m C b r R : ℝ} (h:0<C)(p:Price δ K)(x:0<b)(v:0<r)(y:0<R)(l:b* (2*r) ≤ R)(t:R^2*m ≤1)
    (e:5*C/b ≤ δ)(g:4*(1+25*K*C^2) ≤ 2/3*C*b) :
    let A:=chargeA C b (2*r) R
    ∃ d f : ℝ, 0 ≤ A ∧ (A+3*d)/2=chargeA C b r R ∧ A+3*d < f ∧ 0≤d ∧ f≤δ ∧ 4*(r^2*m+K*f^2)≤d := by
 intro A; let q:= r/R; let D:=2/3*C*b*q^2; let F:=5*C*q; have he:0<q:=div_pos v y; have hz: b*q≤1/2:= by unfold q; rw [←mul_div_assoc,div_le_iff₀ y]; linarith
 have hm:r=q*R:=(div_mul_cancel₀ r y.ne').symm
 have hp:A= (2*C-C*b*(2*q))*(2*q):=by unfold A q chargeA; ring
 have hd: (A+3*D)/2=chargeA C b r R:=by rw [hp]; unfold D chargeA q; ring
 have hv:0≤A:=by rw [hp]; apply mul_nonneg _ (by positivity); nlinarith only [h,hz,p.positive]
 refine ⟨D,F,hv,hd,?_,by unfold D; positivity,?_,?_⟩
 · change _<5*C*q; unfold D; rw [hp]; have hp:0<C*b*q^2:=by positivity
   nlinarith only [hp, mul_pos h he]
 · apply le_trans _ e; change 5*C*q ≤ _; rw [le_div_iff₀ x]; nlinarith only [hz,h]
 change 4*(_+K*(5*C*q)^2)≤_; rw [hm]; let w :=4*(1+25*K*C^2); calc
   _ ≤ w*q^2:= by unfold w; nlinarith only [mul_le_mul_of_nonneg_left t (sq_nonneg q)]
   _ ≤ D:= mul_le_mul_of_nonneg_right g (sq_nonneg q)

variable {s : Side}
abbrev Flow (s : Side) := GaugeField group 3 s × Fabric 3 s E
def bound (b:Side)(w l:ℕ):=10*(w*b.val)-3*l
def radixRead (b:Side) (i n:ℕ)(φ:Flow s→Fabric 3 s E): Prop := Measurable φ ∧ (∀ x o, o∈mesh ((2^n)*b.val)→ φ x o=x.2 o) ∧
 ∀ x y : Flow s, ∀ o∈mesh (2^i), (∀ k ≤ n, i ≤ k → NearLine (2^k) x.1 y.1 (bound b (2^k) (2^i)) o) → NearRead ((2^n)*b.val) x.2 y.2 (bound b (2^n) (2^i)) o → φ x o=φ y o
lemma multi_frame : ∃ N : ℕ, ∃ C : ℝ, 0<C ∧ ∀ b:Side, N≤b.val → ∀ (s:Side)(n:ℕ), let R:= (2^n)*b.val; R ∣ s.val → R<s.val →
    ∃ φ: Flow s→ Fabric 3 s E, radixRead b 0 n φ ∧ ∀ (m:ℝ)(U: GaugeField group 3 s) (F: Fabric 3 s E), Flat U m → (R:ℝ)^2*m ≤1 → arcFee 1 U (φ (U,F)) (2*C/R) := by
 obtain ⟨C,h,H⟩:= Grid.begin_B; obtain ⟨δ,K,p,g,G⟩:= mean_taylor group; have he:Price δ K:=⟨g,p,fun P i j a t u=> G a t i j u (P.pick (i,j)) (P.chosen i j)⟩
 obtain ⟨N,hN⟩:=exists_nat_gt (max (5*C /δ) (4*(1+25*K*C^2)/(2/3*C))); refine ⟨N,C,h,?_⟩; intro b v s n R hR r
 have hp:5*C/ (b.val:ℝ) ≤ δ:= by have hb:5*C/δ ≤ b.val:=le_trans ((le_max_left ..).trans hN.le) (Nat.cast_le.mpr v); apply (div_le_iff₀ (by positivity)).mpr; rw [mul_comm δ]; exact (div_le_iff₀ p).mp hb
 have hv:4*(1+25*K*C^2)≤2/3*C*b.val:= by apply le_trans _ (mul_comm (b.val:ℝ) _|>.le); exact (div_le_iff₀ (show 0 < 2/3*C by positivity)).mp (le_trans ((le_max_right ..).trans hN.le) (Nat.cast_le.mpr v))
 have hout:R = 2^n*b.val:=rfl; have hX:0<(R:ℝ):=by rw [hout]; positivity
 have W (i:ℕ)(u:i ≤ n): ∃ F: Flow s→ Fabric 3 s E, radixRead b i n F ∧ ∀ (m:ℝ) x, Flat x.1 m → (R:ℝ)^2*m ≤1 → arcFee (2^i) x.1 (F x) (chargeA C b.val ((2:ℝ)^i) R):=by
    induction u using Nat.decreasingInduction with
    | self =>
      let k:Tiling s:= ⟨2^n,b,by simpa using hR,by simpa using r⟩
      obtain ⟨F,T,X⟩:= H s k
      have hz:k.R=R:=by simp [Tiling.R,k,hout]; -- tune
      have hi:k.r.val=2^n:=by simp [k];
      rw [hi,hz] at T; refine ⟨F,⟨T.borel, T.leave,fun x y o e l q=> T.see x y o e ?_ ?_⟩,fun m x g p=>?_⟩; -- bound sizes
      · intro i t p; apply l n le_rfl le_rfl i t; refine p.trans ?_; unfold bound; rw [hout]; have he:2^n≤2^n*b.val:= Nat.le_mul_of_pos_right _ b.property; omega
      · intro i t p; apply q i t; refine p.trans ?_; unfold bound; rw [hout]; have he:2^n≤2^n*b.val:=Nat.le_mul_of_pos_right _ b.property; omega
      rw [←hi]; have hb:chargeA C b.val ((2:ℝ)^n) R=C/b.val:=by rw [hout]; unfold chargeA; push_cast; field_simp; ring -- tune
      rw [hb]; exact X _ x.1 x.2 g (hz.symm ▸ p)
    | of_succ j pM ih=>
      obtain ⟨F,t,W⟩:=ih; let r:=2^j; have hr:0<r:=by unfold r; positivity
      have hb: 2^(j+1)=r+r:=by unfold r; rw [pow_succ]; omega
      have hx:(r+r)∣ R:= hout ▸ dvd_mul_of_dvd_left (hb ▸ pow_dvd_pow 2 pM) _
      have hS: r+r∣s.val:=dvd_trans hx hR
      obtain ⟨F',t',W'⟩:= half_step provides.some (d:=3) hS hr; let f(x:Flow s):=(x.1,F x)
      refine ⟨ F'∘f, ⟨ t'.borel.comp (measurable_fst.prodMk t.1), fun x i p=> ?_, fun x y o e l q=> ?_⟩, fun m x g' p=>?_⟩
      · exact (t'.leave (f x) i (align_subdiv i p hx)).trans (t.2.1 x i p)
      · refine t'.see _ _ o e ?_ ?_
        · intro i y p; apply l j (Nat.le_of_lt pM) le_rfl i y; unfold bound; apply le_trans p; have he:r≤ r*b.val:=Nat.le_mul_of_pos_right _ b.property; change r*3 ≤ 10*(r*b.val)-3*r; omega
        have hQ(k:ℕ)(p:j<k): r+r ≤ 2^k:=hb ▸ Nat.pow_le_pow_right (by decide : 0<2) p
        have step(i : Space 3 s)(k:ℕ)(p:j<k)(x:delta o i≤ r*3) : bound b (2^k) (2^(j+1))+ delta o i ≤ bound b (2^k) (2^j):= by
           have he:2^k≤2^k*b.val:=Nat.le_mul_of_pos_right _ b.property; have hp:= hQ k p; unfold bound; rw [hb]; change _ ≤ 10*(2^k*b.val) - 3*r; omega
        intro i p h; refine t.2.2 x y i (hb.symm ▸ p) (fun k p' z j' v l'=> l k p' (by omega) j' v (near_mono (step i k z h) _ l')) fun j a l=> q j a (near_mono (step i n pM h) _ l)
      have hd:(b.val:ℝ)*(2*r) ≤ R := by
        have t := Nat.mul_le_mul_right b.val (Nat.pow_le_pow_right (by decide : 0 < 2) (pM : j+1 ≤ n)); rw [hb] at t; rw [hout, mul_comm (b.val:ℝ)]; norm_cast; rw [two_mul]; exact t
      obtain ⟨g'',e,A,hB,hF,k,a,l⟩:= moment_note h he (b:= (b.val:ℝ)) (by positivity) (r:= (r:ℝ)) (by positivity) hX hd p hp hv
      have Hx : (2:ℝ)^(j+1)= 2*r:= by rw [pow_succ']; unfold r; push_cast; rfl -- tune redundant
      rw [Function.comp_apply]
      have X:=W m x g' p; rw [hb,Hx] at X
      have hk: (r:ℝ)=(2:ℝ)^j:= by unfold r; push_cast; rfl
      rw [←hk, ←hB]; exact_mod_cast W' (chargeA C b.val (2*r) R) g'' e K δ m (f x) he A (by exact_mod_cast hF) k a l g' X
 obtain ⟨F,h,V⟩:=W 0 (by omega); refine ⟨F,h,fun m U X p q=>?_⟩; have hv:= V m (U,X) p q; rw [pow_zero,pow_zero] at hv; intro x t i; apply (hv _ t i).trans; unfold chargeA; field_simp; simp
end YM.CF.BPress.Grid.Half
