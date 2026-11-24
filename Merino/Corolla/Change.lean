import YM.SU5.Exchange.Seed.Station
import YM.SU5.Exchange.Pilot.Contour
import YM.SU5.Exchange.Seed.Flow

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog

variable(P:BudgetPoint){n:Side}
local notation "E"=> (P.B:ℝ)⁻¹
local notation "U"=> spanV P.B
local notation "M"=> (1:ℝ)+5/(P.B:ℝ)
/-- Starter purse. The scale `g` will include Q, small. -/
structure Thimble(g:ℝ): Prop where
 support:P.supportExponent ≤ 1
 grant:0 < g
 tiny:800*g*U ≤ E

lemma bpos:0 < (P.B:ℝ):= Nat.cast_pos.mpr P.B_pos
lemma puck:(0 < E ∧ E ≤ 1) ∧ (1 ≤ U ∧ 0 < U):=by
 have v:=P.B_pos
 have w:1 ≤ (P.B:ℝ):=by exact_mod_cast v
 have ht:1 ≤ U:=by
   exact_mod_cast (show 1≤ (P.B+P.B+1)^4 from one_le_pow₀ (by omega))
 exact ⟨⟨inv_pos.mpr (bpos _), inv_le_one_of_one_le₀ w⟩,ht, zero_lt_one.trans_le ht⟩

variable {P}{g:ℝ}(t:Thimble P g)
include t

lemma hush:(1-degreePrice P.B g E)⁻¹≤2 ∧ 0 < 1-degreePrice P.B g E ∧
    g≤1/2 ∧ degreePrice P.B (100*g) E ≤1/2:=by
 obtain ⟨⟨h0,h1⟩,a,A⟩:=puck P
 have w:=t.tiny
 have h2:(Push.AbsoluteSums.Animals.ballCost P.B:ℝ) = U:=rfl
 have h3 : degreePrice P.B (100*g) E ≤ 1/2:=by
   unfold degreePrice stretch; rw [h2,mul_div_assoc']
   apply (div_le_iff₀ h0).mpr; linarith only [w]
 have y:1/2 ≤1-degreePrice P.B g E:=by
   rw [show degreePrice P.B (100*g) E=100*degreePrice P.B g E by unfold degreePrice stretch; ring] at h3
   linarith only [h3] -- ≤.005

 have hy:0<1-degreePrice P.B g E:=by linarith only [y]
 refine ⟨?_,hy,?_,h3⟩
 · rw [←one_div]; exact (div_le_iff₀ hy).mpr (by linarith only [y])
 linarith only [h1,w,mul_le_mul_of_nonneg_left a (t.grant.le)]

omit t
def till : Occlus P where
 κ:=1
 uΓ:=1+5/P.B
 w:=E
 γ:=g
 c:=E/(4*U)
 d:=E/4
 e:=E*g/4
 η:=E
 hγ:= t.grant
 hη:= (puck P).1.1
 hw:=by rw [div_eq_mul_inv]; linarith only [t.support] -- issue rewrites
 degree:= (hush t).2.2.2
 degree0:= by linarith only [(hush t).2.1]
 still:= (mul_le_mul_of_nonneg_left (hush t).1 t.grant.le).trans (by linarith only [(hush t).2.2.1])
 covers:=by
   have h : Real.exp 1 < 3:=by
     linarith only [Real.exp_one_lt_d9]
   have w0:=mul_le_mul h.le (mul_le_mul_of_nonneg_left (hush t).1 t.grant.le)
     (mul_nonneg t.grant.le (inv_pos.mpr (hush t).2.1).le) (by norm_num)
   linarith only [w0,t.grant]


/-- Grant for a *simultaneous* budget at support-rate seven, including all
payments required by uChip; old forces start on five. -/
abbrev satin(k:ℕ):ℝ:=1+7/(k:ℝ)
abbrev lapel(k:ℕ):ℝ:=1+5/(k:ℝ)
abbrev zpay(k:ℕ):ℝ:= (k:ℝ)⁻¹/(4*spanV k) * (k:ℝ)⁻¹
abbrev bpay(k:ℕ)(g:ℝ):ℝ:= (k:ℝ)⁻¹*g/4
def timely(P:BudgetPoint)(g:ℝ) (z b:Aura n→ℝ) (r:Aura n→Finset (Seat n)→ℝ):Prop:=
 (∀ i, nook (z*tact (satin P.B) P.B) i ≤ zpay P.B) ∧
 (∀ i, nook (b*tact (satin P.B) P.B) i ≤ bpay P.B g) ∧
 (∀ i, nook ((roofL r 1)*tact (lapel P.B) P.B) i < g)


local notation "U0"=> (1:ℝ)+6/(P.B:ℝ)
variable(z b:Aura n→ℝ)
local notation "fogZ"=> Cadre.fog (tact M P.B) z g
include t in
private lemma bleed (hz:0 ≤ z)(i:Aura n):
 fogZ i ≤ z i*tact U0 P.B i :=by
 obtain ⟨_,hu⟩:=(puck P).2
 have hgy: U*g ≤ E:=by linarith only [t.tiny,mul_pos hu t.grant]
 have hr: i.val.card*g ≤ E*widthK n P.B i:=by
    let r:=vigor n P.B
    nlinarith only [mul_le_mul_of_nonneg_right (r.rate i) t.grant.le,
        mul_le_mul_of_nonneg_right hgy (zero_le_one.trans (r.pos i))]
 unfold Cadre.fog waveL
 rw [mul_assoc]
 apply mul_le_mul_of_nonneg_left _ (hz i)
 unfold tact; rw [← Real.exp_add]
 apply Real.exp_le_exp.mpr
 simp_rw [div_eq_mul_inv]; linarith only [hr]


variable(r:Aura n→Finset (Seat n)→ℝ)(hz:0 ≤ z)(hb:0 ≤ b)(hr:∀ X D, D ⊆ X.val→ 0 ≤ r X D)
local notation "T"=>till t
include t hz hb hr

theorem escapement(k:timely P g z b r): Timer (uChip z b r) z (T).κ (T).uΓ (T).w (widthK n P.B) U (T).γ (T).c (T).d (T).e 1 b:=by
 obtain ⟨⟨h0,h1⟩,_,A⟩:=puck P
 have hc:0<E/(4*U):=by positivity
 have hce: U*(E/(4*U))=E/4:=by field_simp
 have ht: M ≤ U0 ∧ U0+E= satin P.B ∧ U0≤ satin P.B:=by unfold satin; simp_rw [div_eq_mul_inv]; constructor; linarith only [h0]; constructor; ring; linarith only [h0]
 have hvv: loom_v M E (widthK n P.B) 0 = tact M P.B :=by funext i; simp only [loom_v,mul_zero,sub_zero]
 change Timer _ _ (1) M E _ U g (E/(4*U)) (E/4) (E*g/4) _ _
 refine uGears _ _ _ hz hb hr _ _ _ _ _ _ _ _ _ (vigor n P.B) ?_ ?_ ?_ le_rfl A.le h0.le t.grant.le
    (by rw [hce]; linarith only [h0]) hc.le ?_ ?_ ?_
 · intro i; unfold Cadre.nook
   have v: nook fogZ i ≤ zpay P.B :=by
     apply le_trans _ (k.1 i); refine sum_le_sum fun j _=> (bleed t z hz j).trans
        (mul_le_mul_of_nonneg_left (tact_para ht.2.2 j) (hz j))

   rw [hvv]
   exact v.trans (mul_le_of_le_one_right hc.le h1)
 · intro i
   have v: shelfR fogZ i ≤ (U * E⁻¹)*zpay P.B:=by
     apply le_trans _ (mul_le_mul_of_nonneg_left (k.1 i) (by positivity:0≤ U*E⁻¹))
     rw [nook,mul_sum]
     refine sum_le_sum fun j _=> (mul_le_mul_of_nonneg_right (bleed t z hz j) (Nat.cast_nonneg _)).trans ?_
     have hj:= shelf_pay (k:=P.B) (s :=U0) h0 j
     rw [ht.2.1] at hj
     simp only [Pi.mul_apply]; linarith only [mul_le_mul_of_nonneg_left hj (hz j)]
   rw [hvv]
   refine v.trans_eq ?_
   unfold zpay; field_simp [(bpos P),A.ne']
 · rw [hvv]
   intro i; apply le_trans _ (k.2.1 i); exact sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (tact_para (ht.1.trans ht.2.2) j) (hb j)
 · rw [mul_one]; simp only [div_eq_mul_inv]; linarith only [h0]
 · rw [hce]; linarith only [mul_pos h0 t.grant]
 intro i; rw [hvv]; exact k.2.2 i

end YM.CF.Merino.Corolla

