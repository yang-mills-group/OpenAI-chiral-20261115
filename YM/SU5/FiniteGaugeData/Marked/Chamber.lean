import YM.SU5.FiniteGaugeData.Marked.Domino

/-!
# Controlling the mirrored marks' place in the periodic field

The only periods used here are the physical ones of the given W. No
extension of that history to new, specially divisible sizes: it is enough
to repeat RP from one side f to its double as long as possible. With d
doubles along ONE axis we attain width ≤ 2^d*(oldWidth + fixed stride cost)
on that axis; transverse supports are unchanged. Use planes 4B apart so the
comparison's Donor step reaches the legal microscopic plane (and to allow
the uses also with the AP convention in effect).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

variable {K:Calibration} {m:Side}
local notation "N"=> K.c m

def Chord (b:ℤ) (d:ℕ) {n:Side} (x:Per n) := ∃ y:ℤ, b ≤ y ∧ y ≤ b+d ∧ (y:Per n)=x
def rest (K:Calibration)(m:Side) (S:Support (More (K.c m)))(i:Axis)(d:ℕ) :=
  ∃ b:ℤ,∀ x∈S,Chord b d (x i)

private lemma anon_cross (i j:Axis)(e:j ≠ i)(s:ℤ)(x:Seat N) : (plane i s).anon N x j=x j := by
  simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,e,e.symm]

def stepgap (K:Calibration) := K.ℓ+4*K.B.val
def addgap (K:Calibration) := 2*stepgap K
lemma gap_pos : 0 < stepgap K := by unfold stepgap; have ht : 0<K.B.val:=K.B.property; omega
lemma addgap_pos : 0 < addgap K := Nat.mul_pos two_pos gap_pos

private lemma aligned_before (b:ℤ):
    ∃ z:ℤ, let s:=Heat.gaugeShift K.B z; s+K.ℓ ≤ b ∧ b ≤ s+stepgap K := by
  let c:ℤ:=4*K.B.val
  have hc:0<c:=by unfold c; positivity
  let z:=(b-K.ℓ)/c
  refine ⟨z,?_⟩; change c*z+K.ℓ ≤ b ∧ b ≤ c*z+stepgap K
  have he:=(Int.emod_add_mul_ediv (b-(K.ℓ:ℤ)) c)
  have hv:=Int.emod_nonneg (b-(K.ℓ:ℤ)) hc.ne'
  have h':=Int.emod_lt_of_pos (b-(K.ℓ:ℤ)) hc
  unfold stepgap; push_cast; change _ ∧ b ≤ c*z + ((K.ℓ:ℤ)+c)
  change _ + c*z = _ at he
  omega

/-- Leave room on the other side too. -/
private lemma inhalf {x:Seat N} (i:Axis){d:ℕ}{s b:ℤ}(a:s+K.ℓ ≤ b)(r:b ≤ s+stepgap K)(p:Chord b d (x i)) (h:d+addgap K ≤ (N).val):
    x∈ band N i s K.ℓ := by
  obtain ⟨y,t,e,q⟩:=p
  let n:=N
  have hz: (K.ℓ:ℤ) ≤ y-s := by omega
  have hp: y-s+(K.ℓ:ℤ) ≤ (N).val := by
    unfold addgap stepgap at *; omega
  let Y:=(y-s).toNat
  have hh:Y<(More n).val:=by change _< n.val*2; have w:0<n.val:=n.property; change _≤(n.val:ℤ) at hp; unfold Y; omega
  apply (band_spec ..).mpr
  rw [show x i - (s:Per (More N))=(Y:Per (More n)) from ?_,ZMod.val_natCast_of_lt hh]; swap
  · rw [←Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_sub,q]
  unfold Y; omega

lemma twice (i:Axis) {d:ℕ} {S:Support (More N)} (a:rest K m S i d)(h:d+addgap K≤ (N).val) :
    ∃ z:ℤ, let s:=Heat.gaugeShift K.B z; let T:Support (More N):= S.image ((plane i s).anon N) ∪ S
           S ⊆ band N i s K.ℓ ∧ rest K m T i (2*d+addgap K) ∧
           ∀ j:Axis,j≠i → ∀ d', rest K m S j d' → rest K m T j d' := by
  obtain ⟨b,a⟩:=a; obtain ⟨z,u,v⟩:=aligned_before (K:=K) b
  let s:=Heat.gaugeShift K.B z
  change s+K.ℓ ≤ _ at u; change _≤ s+_ at v
  refine ⟨z,fun x p=>inhalf i u v (a x p) h,⟨2*s-(b+d),?_⟩,?_⟩
  · intro x tx; rcases mem_union.mp tx with E|E
    · obtain ⟨p,t,rfl⟩:= mem_image.mp E; obtain ⟨y,hp,e,q⟩:= a p t
      refine ⟨2*s-y,by omega,by unfold addgap; push_cast; omega,?_⟩
      let x:=(plane i s).anon N p
      have ht : x i-(s:Per (More N))=-(p i-(s:Per (More N))) := across_coord i s _
      change ((2*s-y:ℤ):Per (More N)) = x i
      rw [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,q,eq_add_of_sub_eq ht]; ring
    obtain ⟨y,p,v',q⟩:=a _ E; refine ⟨y,by omega,?_,q⟩; unfold addgap; push_cast; omega
  intro j hv d' ⟨b,w⟩; refine ⟨b,?_⟩; intro x hx; rcases mem_union.mp hx with y|y
  · obtain ⟨x,hx',rfl⟩:=mem_image.mp y; rw [anon_cross i j hv]; exact w x hx'
  exact w x y

namespace Wick
variable {H:Histories K}{t:ℕ} (p: Wick H m t)
local notation "Φ" => hearth H m t
local notation "ν" => cash (H.loom m 0)

structure Flare (t:ℕ)(x y:Mark (K.c m)) (H:Histories K)(q:ℕ):Prop where
  value : ‖hearth H m q x‖^t ≤ ‖hearth H m q y‖
  cost : cash (H.loom m 0) y ≤ cash (H.loom m 0) x ^ t

private lemma blaze {l n:ℕ} {f g y:Mark N}(h:Flare l f g H t)(s:Flare n g y H t): Flare (l*n) f y H t := by
  constructor
  · rw [pow_mul]; exact (pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) h.value n).trans s.value
  rw [pow_mul]; exact s.cost.trans (pow_le_pow_left₀ (cash_nonneg ..) h.cost n)

include p
lemma funnel (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤ (N).val) {S:Support (More N)}(w:rest K m S i d)
    {x:Mark N} (c:AtSupport false S x):
    ∃ (y:Mark N) (T:Support (More N)), AtSupport false T y ∧ Flare (2^k) x y H t ∧
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
    · exact ⟨Y,T,a,pow_succ' 2 k ▸ blaze (show Flare 2 x y H t from ⟨p.cinder i z hp,p.domino i z hp⟩) b,fun j a d f=> q j a d (e j a d f)⟩


lemma brush (k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤ (N).val) {S:Support (More N)}(R:Finset Axis)(w:∀ i∈R,rest K m S i d)
    {x:Mark N} (c:AtSupport false S x):
    ∃ (y:Mark N) (T:Support (More N)), AtSupport false T y ∧ Flare ((2^k)^R.card) x y H t := by
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
    (h:d+addgap K ≤ (N).val){f:Mark N}(v:AtSupport false S f): let D:ℕ:=d+addgap K
    ‖Φ f‖ ≤ Real.exp (tariff H * ((2*D:ℕ):ℝ)^4) * ν f := by
  intro D
  obtain ⟨k,ht,e⟩:= goldi (lt_of_lt_of_le addgap_pos (Nat.le_add_left (addgap K) d)) h
  obtain ⟨y,T,a,b⟩:=p.brush k ht univ (fun i _=> w i) v
  let J:ℕ:= (2^k)^4
  have hd: (univ:Finset Axis).card=4 := card_fin 4
  have hb:Flare J f y H t:=by simpa only [hd] using b
  have hr: m.val^4 ≤ J*(2*D)^4 := by
    unfold J D
    rw [← mul_pow]
    refine pow_le_pow_left' ?_ _
    calc
      _ ≤ (N).val := side_lower K
      _ ≤ 2*2^k*(d+addgap K):=e
      _ = _:=by ring
  have hs: (m.val:ℝ)^4 ≤ J*((2*D:ℕ):ℝ)^4:=by exact_mod_cast hr
  apply (pow_le_pow_iff_left₀ (norm_nonneg (Φ f)) (mul_nonneg (Real.exp_pos _).le (cash_nonneg ..)) (n:=J) (by unfold J; positivity)).mp
  calc
    ‖Φ f‖^J ≤ Real.exp (tariff H * (m.val:ℝ)^4)*ν y := hb.value.trans (p.chimney y a.env)
    _ ≤ _ := by
      rw [mul_pow,←Real.exp_nat_mul]
      apply mul_le_mul ?_ hb.cost (cash_nonneg ..) (Real.exp_pos _).le
      apply Real.exp_le_exp_of_le
      calc
        _ ≤ tariff H*(J*((2*D:ℕ):ℝ)^4):=mul_le_mul_of_nonneg_left hs (tariff_nonneg H)
        _ = _:=by ring
end Wick

private lemma rests (S:Finset Cover):∃ d:ℕ,∀ (K:Calibration)(m:Side)(i:Axis), rest K m (S.image (wrap (More (K.c m)))) i d := by
  let r:= S.sup (fun x=>univ.sup fun i:Axis=> (x i).natAbs)
  refine ⟨2*r,fun K m i=> ⟨-(r:ℤ),?_⟩⟩
  intro x hx; obtain ⟨y,hp,rfl⟩:=mem_image.mp hx
  have he : (y i).natAbs ≤ r:= (le_sup (f:=fun i:Axis=> (y i).natAbs) (mem_univ i)).trans (le_sup (f:=fun y=>univ.sup fun i:Axis=> (y i).natAbs) hp)
  exact ⟨y i,by omega,by omega,(wrap_here ..).symm⟩

/-- The local norm estimate. All Borel even chiral marks on the box
(in particular the output links ARE allowed here). Each financed entry
with period past a threshold only in the box. -/
lemma bank (H:Histories K)(S:Finset Cover):∃ D:ℝ,0 < D ∧ ∀ᶠ m:Side in atTop,∀ t:ℕ,Wick H m t → ∀ f:Mark (K.c m),
    AtSupport false (S.image (wrap (More (K.c m)))) f → ‖hearth H m t f‖ ≤ D*cash (H.loom m 0) f := by
  obtain ⟨d,u⟩:= rests S
  let D:=Real.exp (tariff H * ((2*(d+addgap K):ℕ):ℝ)^4)
  refine ⟨D,Real.exp_pos _,?_⟩
  filter_upwards [(c_grows K).eventually (eventually_ge_atTop (d+addgap K))] with m h t hp f v
  exact hp.homestead (u K m) h v
end YM.CF.Buffered.Afterglow
