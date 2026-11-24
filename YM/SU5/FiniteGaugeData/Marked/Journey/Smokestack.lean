import YM.SU5.FiniteGaugeData.Marked.Chamber

/-!
# Period-local version of the dyadic estimate independent of having
`Histories`; exactly the same chamber calculation here with a `Metered`
functional instead (used when working directly above calibrated resolutions
in `Voyage`, even on periods outside the `takes` and without
electing ANY period-common beta, tilt or regulator data).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

-- packaging charged hypotheses at *one* period. All ties to actual course
-- then in Journey/Livery etc.
variable {K: Calibration} {m:Side} {L:Loom (K.c m)} {X: Mark (K.c m)→ℂ}{D:ℝ}
structure Metered (K:Calibration)(m:Side)(L:Loom (K.c m))(X:Mark (K.c m)→ℂ) (D:ℝ):Prop where
  positive : 0 ≤ D
  tally(f:Mark (K.c m))(h:Envelope f): ‖X f‖ ≤ Real.exp (D * (m.val:ℝ)^4) * cash L f
  sum (f g:Mark (K.c m))(h:Envelope f)(p:Envelope g): X (f+g)=X f+X g
  mult(a:ℂ)(f:Mark (K.c m)):X (a • f)=a*X f
  unit:X 1=1
  fund (a:Axis)(z:ℤ)(f:Mark (K.c m))(h:AtSupport false (band (K.c m) a (Heat.gaugeShift K.B z) K.ℓ) f):
    0 ≤ X (reflMark a (Heat.gaugeShift K.B z) f*f)
  roof: ∃ c t k,Skye.Roof (K.c m) c t k L
  territory: Advance.LoomLaw L K.w
namespace Metered
variable (p:Metered K m L X D)
-- same two and cinder as in Marked/Core
private lemma two (x y v : ℂ) (h : 0 ≤ v)
    (e : ∀ a:ℂ, 0 ≤ v + a*y + star a*x + star a*a) : ‖x‖^2 ≤ ‖v‖ := by
  have h0:= Complex.le_def.mp h
  have h1:= (Complex.le_def.mp (e 1)).2
  have hI:= (Complex.le_def.mp (e Complex.I)).2
  simp [Complex.mul_im] at h0 h1 hI
  have hp:y.re=x.re:= by linarith
  have hx:y.im = -x.im:= by linarith
  have ht:= (Complex.le_def.mp (e (-x))).1
  simp only [Complex.add_re, Complex.mul_re,Complex.neg_im,Complex.neg_re, Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.zero_re,hp,hx] at ht
  have hk:= Complex.re_le_norm v
  rw [Complex.sq_norm,Complex.normSq_apply]; nlinarith
local notation "bandZ" i:max z:max => band (K.c m) i (Heat.gaugeShift K.B z) K.ℓ
include p
lemma twiceX (i:Axis) (z:ℤ) {f:Mark (K.c m)} (w:AtSupport false (bandZ i z) f) :
    ‖X f‖^2 ≤ ‖X (reflMark i (Heat.gaugeShift K.B z) f*f)‖ := by
  let T:=reflMark (n:=K.c m) i (Heat.gaugeShift K.B z)
  let S:=bandZ i z
  have W:= (w.refl i (Heat.gaugeShift K.B z)).env
  apply two _ (X (T f)) _ (p.fund i z f w)
  intro a
  let u:Mark (K.c m):=1
  have he:=p.fund i z (f+a • u) (w.addM ((AtSupport.oneM S).smulM a))
  have ht : T (f+a • u) = T f+star a • u := by
    funext x; unfold T reflMark; rw [Pi.add_apply, Fock.theta_add,Pi.smul_apply,Fock.theta_smul]; rw [show Fock.theta _ (u _) = 1 from Fock.theta_one _]; rfl
  change 0 ≤ X (T (f+a • u)*(f+a • u)) at he
  rw [ht, add_mul,mul_add,mul_add,Algebra.mul_smul_comm,mul_one,Algebra.smul_mul_assoc,one_mul,Algebra.smul_mul_assoc,one_mul] at he
  have ha : Envelope (a • T f) := ((w.refl ..).smulM _).env
  have hb : Envelope (star a • f) := (w.smulM _).env
  have hc : Envelope (star a • a • u) := (((AtSupport.oneM S).smulM a).smulM (star a)).env
  have hd : Envelope (T f*f) := env_mult W w.env
  have hD : Envelope (T f*f+a • T f) := Girt.kitE _ _ (·+·) (by fun_prop) hd ha
  have hE : Envelope (star a • f+star a • a • u) := Girt.kitE _ _ (·+·) (by fun_prop) hb hc
  rw [p.sum _ _ hD hE,p.sum _ _ hd ha,p.sum _ _ hb hc] at he
  rw [p.mult,p.mult,p.mult,p.mult,p.unit,mul_one] at he
  convert he using 1; ring
lemma twiceCash (i:Axis)(z:ℤ) {f:Mark (K.c m)} (w:AtSupport false (bandZ i z) f):
    cash L (reflMark i (Heat.gaugeShift K.B z) f * f) ≤ cash L f ^ 2 := by
  obtain ⟨a,v,g,A⟩:= p.roof
  have hp:= cash_mult (w.refl i (Heat.gaugeShift K.B z)) w A.bill p.territory
    (fun x t y e=> by have he:= margin_separate i (Heat.gaugeShift K.B z) K.buffer x y t e; omega)
  rw [cash_turn A] at hp
  rw [sq]; exact hp

local notation "N"=> K.c m
local notation "Φ"=> X
local notation "ν"=> cash L
structure Flare (t:ℕ)(x y:Mark (K.c m))(X:Mark (K.c m) → ℂ)(L:Loom (K.c m)):Prop where
  value : ‖X x‖^t ≤ ‖X y‖
  cost : cash L y ≤ cash L x ^ t

omit p in
private lemma blaze {l n:ℕ} {f g y:Mark N}(h:Flare l f g X L)(s:Flare n g y X L): Flare (l*n) f y X L := by
  constructor
  · rw [pow_mul]; exact (pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) h.value n).trans s.value
  rw [pow_mul]; exact s.cost.trans (pow_le_pow_left₀ (cash_nonneg ..) h.cost n)

lemma funnel (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤ (N).val) {S:Support (More N)}(w:rest K m S i d)
    {x:Mark N} (c:AtSupport false S x):
    ∃ (y:Mark N) (T:Support (More N)), AtSupport false T y ∧ Flare (2^k) x y X L ∧
           ∀ j:Axis,j≠i → ∀ d', rest K m S j d' → rest K m T j d' := by
  induction k generalizing d S x with
  | zero=> exact ⟨x,S,c,⟨by simp,by simp⟩,fun _ _ _ v=>v⟩
  | succ k ih=>
    have ht:d+addgap K ≤ (N).val:=h.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _))
    obtain ⟨z,u,v,e⟩:= twice i w ht; let s:=Heat.gaugeShift K.B z
    let M:=S.image ((plane i s).anon N) ∪ S
    have hp:AtSupport false (band N i s K.ℓ) x := by
      exact c.mono u
    let g:=reflMark i s x
    let y:=g*x
    have hz: AtSupport false M y:= ((c.refl i s).mono subset_union_left).mulM (c.mono subset_union_right)
    obtain ⟨Y,T,a,b,q⟩:= ih (d:=2*d+addgap K) (by rw [pow_succ] at h; exact h.trans' (le_of_eq (by ring))) v hz
    · exact ⟨Y,T,a,pow_succ' 2 k ▸ blaze (show Flare 2 x y X L from ⟨p.twiceX i z hp,p.twiceCash i z hp⟩) b,fun j a d f=> q j a d (e j a d f)⟩


lemma brush (k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤ (N).val) {S:Support (More N)}(R:Finset Axis)(w:∀ i∈R,rest K m S i d)
    {x:Mark N} (c:AtSupport false S x):
    ∃ (y:Mark N) (T:Support (More N)), AtSupport false T y ∧ Flare ((2^k)^R.card) x y X L := by
  induction R using Finset.induction_on generalizing S x with
  | empty=> exact ⟨x,S,c,⟨by simp,by simp⟩⟩
  | @insert i R v ih=>
    obtain ⟨y,T,a,b,e⟩:=p.funnel i k h (w _ (mem_insert_self _ _)) c
    obtain ⟨Y,M,q,g⟩:= ih (S:=T) (fun j u=> e j (fun V=> v (V ▸ u)) d (w j (mem_insert_of_mem u))) a
    rw [card_insert_of_notMem v,pow_succ']; exact ⟨_,_,q,blaze b g⟩

omit p in
private lemma goldi {x y:ℕ} (p:0<y) (t:y ≤ x): ∃ k:ℕ, 2^k*y ≤ x ∧ x ≤ 2*(2^k)*y := by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e:Nat.find ht=k
  cases k with
  | zero=> simpa using t
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega

/-- Uniform four-axis estimate. -/
lemma homestead {d:ℕ}{S:Support (More N)}(w:∀ i,rest K m S i d)
    (h:d+addgap K ≤ (N).val){f:Mark N}(v:AtSupport false S f): let B:ℕ:=d+addgap K
    ‖Φ f‖ ≤ Real.exp (D * ((2*B:ℕ):ℝ)^4) * ν f := by
  intro B
  obtain ⟨k,ht,e⟩:= goldi (lt_of_lt_of_le addgap_pos (Nat.le_add_left (addgap K) d)) h
  obtain ⟨y,T,a,b⟩:=p.brush k ht univ (fun i _=> w i) v
  let J:ℕ:= (2^k)^4
  have hd: (univ:Finset Axis).card=4 := card_fin 4
  have hb:Flare J f y X L:=by simpa only [hd] using b
  have hr: m.val^4 ≤ J*(2*B)^4 := by
    unfold J B
    rw [← mul_pow]
    refine pow_le_pow_left' ?_ _
    calc
      _ ≤ (N).val := side_lower K
      _ ≤ 2*2^k*(d+addgap K):=e
      _ = _:=by ring
  have hs: (m.val:ℝ)^4 ≤ J*((2*B:ℕ):ℝ)^4:=by exact_mod_cast hr
  apply (pow_le_pow_iff_left₀ (norm_nonneg (Φ f)) (mul_nonneg (Real.exp_pos _).le (cash_nonneg ..)) (n:=J) (by unfold J; positivity)).mp
  calc
    ‖Φ f‖^J ≤ Real.exp (D * (m.val:ℝ)^4)*ν y := hb.value.trans (p.tally y a.env)
    _ ≤ _ := by
      rw [mul_pow,←Real.exp_nat_mul]
      apply mul_le_mul ?_ hb.cost (cash_nonneg ..) (Real.exp_pos _).le
      apply Real.exp_le_exp_of_le
      calc
        _ ≤ D*(J*((2*B:ℕ):ℝ)^4):=mul_le_mul_of_nonneg_left hs (p.positive)
        _ = _:=by ring
end Metered
private lemma rests (S:Finset Cover):∃ d:ℕ,∀ (K:Calibration)(m:Side)(i:Axis), rest K m (S.image (wrap (More (K.c m)))) i d := by
  let r:= S.sup (fun x=>univ.sup fun i:Axis=> (x i).natAbs)
  refine ⟨2*r,fun K m i=> ⟨-(r:ℤ),?_⟩⟩
  intro x hx; obtain ⟨y,hp,rfl⟩:=mem_image.mp hx
  have he : (y i).natAbs ≤ r:= (le_sup (f:=fun i:Axis=> (y i).natAbs) (mem_univ i)).trans (le_sup (f:=fun y=>univ.sup fun i:Axis=> (y i).natAbs) hp)
  exact ⟨y i,by omega,by omega,(wrap_here ..).symm⟩
lemma albums (K:Calibration)(S:Finset Cover)(D:ℝ):∃ u:ℝ,0<u ∧ ∀ᶠ m:Side in atTop,∀ (l:Loom (K.c m))(X:Mark (K.c m)→ℂ), Metered K m l X D→ ∀ f:Mark (K.c m),
    AtSupport false (S.image (wrap (More (K.c m)))) f → ‖X f‖ ≤ u*cash l f := by
  obtain ⟨d,p⟩:= rests S
  refine ⟨_,Real.exp_pos (D * ((2*(d+addgap K):ℕ):ℝ)^4),?_⟩
  filter_upwards [(c_grows K).eventually (eventually_ge_atTop (d+addgap K))] with m h l X v f w
  exact v.homestead (p K m) h w
end YM.CF.Buffered.Afterglow.Journey
