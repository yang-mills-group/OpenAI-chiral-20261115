import YM.SU5.Interaction.Kerosene.Contour

/- single ledge purchase, compile sequence later -/
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 710000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)

abbrev Tape {A:Type*} : Type _ := Palot.leaf A → Finset A → ℝ -- preserve projection and burn separately
variable (z:Tape (A:=A))(κ:ℝ)(s:1≤κ)
variable (P E:Palot.leaf A→ℝ)(p:0≤P)(e:0 ≤ E)
local notation "η"=> (farW A)
def charglass (P E:Palot.leaf A→ℝ)(z:Tape (A:=A))(X:Palot.leaf A)(D: Finset A):ℝ:=(if D.Nonempty then 0 else E X)+∑ Y:Palot.leaf A,P Y*blast X Y (farW A) z D
abbrev Fiery {A:Type*}[DecidableEq A](z:Tape (A:=A)): Prop:=∀ X:leaf A,∀ D⊆X.val,0≤ z X D
include p e
lemma charglass_burn (v:Fiery z):Fiery (charglass P E z) := fun X D _=> add_nonneg (ite_nonneg le_rfl (e X)) (sum_nonneg fun Y _=> mul_nonneg (p Y) (sum_nonneg fun i g=> prod_nonneg fun j _=> v _ _ inter_subset_right))
omit p e
lemma Fiery.roof (v:Fiery z)(q:1 ≤ κ):0 ≤ roofL z κ:=fun X=> sum_nonneg fun i p=> mul_nonneg (zero_le_one.trans (duty_i _ q)) (v _ _ (mem_powerset.mp p))
include p s
lemma charRoof (v:Fiery z)(X:leaf A): roofL (charglass P E z) κ X ≤ E X + ∑ Y:Palot.leaf A, ode0 P (roofL z κ) X Y :=by
 unfold roofL; simp_rw [charglass,mul_add,mul_sum]; rw [sum_add_distrib]
 have h: (∑ i∈X.val.powerset,duty κ i*if i.Nonempty then 0 else E X)=E X:=by
    rw [sum_eq_single ∅]; simp [duty]; intro i _ v; rw [if_pos (Finset.nonempty_iff_ne_empty.mpr v),mul_zero]; simp
 rw [h,sum_comm]; apply add_le_add_right; apply sum_le_sum; intro Y _; have ht:= mul_le_mul_of_nonneg_left (nodeV Y z v s X (farW A)) (p Y); simp_rw [mul_sum] at ht; refine le_trans (le_of_eq ?_) ht; exact sum_congr rfl fun i _=> by apply sum_congr rfl; intro j _; rw [mul_left_comm] -- tune left
variable (Q W W':Palot.leaf A→ℝ)(r:ℝ)
include e
variable (m:0≤W)(w:WarmStyle W) (v:Fiery z)
include v m w
-- note Q used as C envelope, not confused with P cost.
lemma charContour (γ:ℝ)(h:0 ≤ γ)(a:fog W P γ ≤ Q)(u:W ≤ W')(g:∀ i:A,nook (roofL z κ*W) i ≤ γ)(x:A) : nook (roofL (z+charglass P E z) κ* W) x ≤ nook (roofL z κ*style W Q) x + (nook (E*W') x + shelfR Q x*γ):=by
 let X0:=z; let M:=κ; let C:=roofL z κ; let V:=charglass P E z; have hK:=(wake_contour Q W C P w m (Fiery.roof z κ v s) p γ h g a x); let X:=roofL (z+V) κ;
 have hp(i:leaf A): X i ≤ C i + E i + ∑ Y:leaf A, ode0 P C i Y:=by
    apply le_trans ?_ (show C i+_≤_ from (?_ : C i + (roofL V κ i) ≤ _)); swap; · rw [add_assoc]; exact add_le_add_right (charRoof z κ s P E p v i) _
    unfold C; unfold X roofL; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; rfl -- tune rfl? le reflexive
 let A0:= ∑ i∈spark x,E i*W i
 have hy:= sum_le_sum (s:=spark x) (fun i _=>mul_le_mul_of_nonneg_right (hp i) (m i))
 simp_rw [add_mul,sum_add_distrib] at hy -- dsimp applied? tune expands too much?
 have he: A0 ≤ nook (E*W') x:= sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (u _) (e i)
 change nook (X*W) x ≤ _
 change nook (X*W) x ≤ nook (C*W) x+A0+vaultℜ C P W x at hy
 change _+ vaultℜ C P W x ≤ _ at hK
 change _≤ nook (C*_) x+_
 linarith only [hy,he,hK]
omit p s e v m w
variable {I:Type*}[DecidableEq I]
variable (H K B:I→ Palot.leaf A→ℝ)(G T:Finset I)(W_:Palot.leaf A→ℝ)
variable (hB:∀ i∈G,0 ≤ B i)(hE:∀ i∈G,0 ≤ H i)(hK:∀ i∈G,0 ≤ K i)
local notation "w[a:" G:max "]"=> maestro B G W
abbrev πSeat (K H:Palot.leaf A→ℝ)(γ:ℝ)(W:Palot.leaf A→ℝ)(o:A):=nook (H*W) o + shelfR K o*γ
local notation "Wq" f:max=> πSeat (B f) (H f) r W_
structure SafeBand (z:Tape (A:=A))(κ:ℝ)(H B:I→Palot.leaf A→ℝ)(r:ℝ)(W W':Palot.leaf A→ℝ)(G:Finset I):Prop where
 share : ∀ i:A,nook (roofL z κ*maestro B G W) i+∑ q∈G,πSeat (B q) (H q) r W' i≤r
include hB hE
lemma seatSparks (q:T ⊆ G)(V:0≤W_)(hr:0≤r) (i:A) :0≤∑ v∈T,(Wq v) i:=sum_nonneg fun j t=>add_nonneg (sum_nonneg fun i _=>mul_nonneg (hE j (q t) _) (V _)) (mul_nonneg (sum_nonneg fun i _=> mul_nonneg (hB j (q t) _) (Nat.cast_nonneg _)) hr)
include hK m s w v
variable {g:ℝ}
variable (u:maestro B G W ≤ W_)(hr: 0 ≤ r)(hZ:∀ i∈ G,fog W_ (K i) r≤ B i)
include u hr hZ
lemma SparkPlot (ν:I)(t:ν ∉ T)(p': insert ν T ⊆ G)(V: SafeBand z κ H B r W W_ (insert ν T)): SafeBand (z+charglass (K ν) (H ν) z) κ H B r W W_ T := by
 let D(x):= Wq x; let s0:=insert ν T; let S:= maestro B s0 W; let X:=maestro B T W
 have hp:ν∈ G:= p' (mem_insert_self ..); have hd:T⊆ G:=(subset_insert ..).trans p'; have hx: S=style X (B ν):= maestro_insert W B T _ t
 have h0:WarmStyle X:=maestro_warm W B T (fun i v=>hB i (hd v)) m w
 have hu:0≤X:= m.trans (maestro_lo W B T (fun i v=>hB i (hd v)) m); have he:X ≤ S:= maestro_plus W B (subset_insert ..) m (fun i v=>hB i (p' v)); let ht:=he.trans ((maestro_plus W B p' m hB).trans u)
 let C:= roofL z κ; let γ:= Fiery.roof z κ v s
 have hw(i:A): nook (C*X) i ≤ r:= by
    have hk:nook (C*X) i≤ nook (C*S) i:= sum_le_sum (fun _ _=> mul_le_mul_of_nonneg_left (he _) (γ _)); exact (hk.trans (le_add_of_nonneg_right (seatSparks r H B G s0 W_ hB hE p' (hu.trans ht) hr i))).trans (V.share i) -- order check
 have hz:fog X (K ν) r≤ B ν:=fun i=> (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht _) (hK ν hp _)) (Real.exp_pos _).le).trans (hZ ν hp _)
 constructor; intro i; let U:= V.share i; have hy:= charContour z κ s (K ν) (H ν) (hK ν hp) (hE ν hp) (B ν) X W_ hu h0 v r hr hz ht hw i
 rw [sum_insert t, maestro_insert _ _ _ _ t,←add_assoc] at U; exact (add_le_add_left hy _).trans U
end YM.CF.Cadre
#print axioms YM.CF.Cadre.SparkPlot
