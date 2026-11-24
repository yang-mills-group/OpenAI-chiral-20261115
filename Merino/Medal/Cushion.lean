import Merino.Medal.Scepter
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Medal
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Vale RG
open scoped Matrix Matrix.Norms.L2Operator Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Py.Rate Py.Rate.LocalLimit Preparation
open Skye Scree Buffered Afterglow MeasureTheory
open Yoke Papal Garter Gleam
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))


open Finset Cuff Hem Fock StepIn Lamour.Bridge.Celeste.Clock.Fabric Py.Rate.Pannier
open Lamour.Bridge.Celeste.Clock
open Journey
variable {n:Side}
open CF.Pannier.Chancel
open Reed

open Diadem Tower.SlabMark clocks
variable (H:Real.exp 1≤P.x)
variable {s i k:ℕ}
local notation "N"=> count Y s i
local notation "x"=> hat P.R.L P.x s
local notation "K"=> tent Y H
local notation "β" => (gram Y s i k).beta
local notation "E"=>Real.exp
local notation "ℒ"=>Journey.compass Y i k s

open Lace

/-- scaled to actual beta -/
def Cameo (ε:ℝ)(f:Pane (count Y s i)→ℂ)(T:Bundle SU.group (More (count Y s i))):Prop:=
 ∀ {t},Strut x t→
 /- band eligibility even for scalar multiple. -/
 (∀ c, AtSupport false (Buffered.band N pole 0 (tent Y H).ℓ) (staged t c f))∧
 let μ:=chat Y s i k T (showtime _ t)
 |(ℒ (photo (staged t β f))).re - μ| ≤ 3*lean x∧
 (miles t)^8*(3*lean x) ≤ ε∧
 illuminated (P.V.L.mood (Y.uv k-s)) (P.V.L.tied (Y.uv k-s)) T t ε



#check Cameo
lemma feast (L J a r:ℝ)(h:0<L)(ha:0<a)(hr:0<r)(j:0≤J)(ε:ℝ)(b:0<ε):
 ∀ᶠ u in atTop, let y:=hat P.R.L P.x u; ∀ᶠ i in atTop, ∀k,
   Ferry Y u i k → IcePlot Y u i k → ∀A,ShelterCost A Y u i k →
   ∀ f T,Scar (shellC (height y)) (Pressure.temp y) r L (tarnish a y * J) f T →
     Cameo Y H (s:=u) (i:=i) (k:=k) ε f T :=by
 let D:=stage_slope P.V P.x
 obtain ⟨t₀,d⟩:=eventually_atTop.1 <|
    burning SU.group P.K.top.clip L P.V.W.parcel (warmIdee P)
       P.K.width ε b
 let C:=L^2*noodlePrice (glint P.K.top.clip)
 have v:0≤C:=by unfold C noodlePrice tile; positivity
 filter_upwards [D.eventually (above t₀),D.eventually (offPeak (tent Y H).ℓ),
    D.eventually (harvest K C),D.eventually (melt ε b), polarReady Y, burn.{0} Y L J a r hr ha h.le j,
    D.eventually_gt_atTop 0] with s a₀ w p f g u e
 intro y;let l:=shellC (height y)
 have e':=twilightPos _ e


 filter_upwards [
   (count_grows Y s).eventually_ge_atTop (diameter y ^2),
   (count_grows Y s).eventually (growing K y L C v e e' (diameter y))]
   with i ht y' k F ice A Z M T U t t₁
 obtain ⟨j₀,q⟩:=strut_d t₁
 have a₁:l+ (tent Y H).ℓ ≤ t:=le_trans ?_ (w t t₁)
 swap
 · apply le_trans _ (Nat.le_self_pow (by decide : 2≠0) _); change _ ≤ 2*(l+_)+4;omega
 have q₀:= (Nat.le_self_pow (by decide: 2≠0) _).trans ht
 let n:=count Y s i
 have r':Steam (More n) t:=by
    have i₁:t≤diameter y:=(le_trans (by omega:t≤4*t) q)
    have d':= (Nat.pow_le_pow_left i₁ 2).trans ht
    unfold Steam; exact_mod_cast (d'.trans <|Nat.le_mul_of_pos_right _ (by decide:(0:ℕ)<2))
 have E₀:Even (More n).val:=⟨n.val,by exact Nat.mul_two n.val⟩
 have p₀:Reach t (slim l):=by
   have d':= (slim_le l).trans (Nat.le_add_right l (tent Y H).ℓ)
   have i₁:=(Nat.pow_le_pow_left
     (by omega:2*slim l+4≤2*(l+(tent Y H).ℓ)+4) 2).trans (w t t₁)
   unfold Reach miles;exact_mod_cast i₁.trans (Nat.le_mul_of_pos_left _ (by decide:(0:ℕ)<2))


 have q':t+l+ (tent Y H).ℓ ≤ n.val:=
   (le_trans (by omega:t+l+_≤4*t) q).trans q₀
 have pf:2*(t+l)≤diameter y:=(le_trans (by omega:2*(t+l)≤4*t) q)
 have hab:=f t t₁
 have it:=P.V.L.roof (Y.uv k-s)
 refine ⟨fun c=> (staged_job M c ⟨U.readable,_,U.bound⟩ U.region).mono <|
                        matinee_up a₁ q',?_,
   by simpa only [miles,Nat.cast_mul,Nat.cast_ofNat] using hab,
   d t (a₀ t t₁) p₀ r' E₀ it.1 (it.2.1 _) (it.2.2 _) _ _ T U.cloth⟩
 have c:stint.{0} Y s i k M T:=codified Y Z (g i k F.enters) (u i k F.enters M T U)
 have v₀: wiggle (clocks.height y) ≤ l:= by unfold l shellC wiggle;omega
 have t:=weigh Y H U (showtime _ t) (false,true) F ice c y' (fun _=>noon_cows _ pf _) v₀
   (meal_low _ _ _ _ _ U.cloth.rent) e e' p.2.2.2 p.1 p.2.1 p.2.2.1
 rw [polka_pose] at t;exact t


variable {f:Pane (count Y s i)→ℂ}{T:Bundle SU.group (More (count Y s i))}
variable (χ:Stripe SU.group→ℝ) (α:ℝ)
local notation "π₀"=>leadCoin χ α

lemma coin_cash {ε t} (h:Strut x t) (p:Cameo Y H (k:=k) ε f T) (q:ε≤π₀/2)
 (v:0<α)(u:α≤dripQ T (χ∘ridge) (χ∘ridge)):
   π₀/2 ≤ miles t ^8 * (ℒ (photo (staged t β f))).re := by
 obtain ⟨_,a,b,c⟩:=p h
 have u₀:=
   illum_charge (P.V.L.mood (Y.uv k-s)) (P.V.L.tied (Y.uv k-s))
      T t χ α v u (show illuminated _ _ _ _ _ from c.trans (q.trans (half_le_self (shines χ α v).le)))
 have a':=mul_le_mul_of_nonneg_left (neg_le_of_abs_le a)
    (show 0 ≤ miles t^8 from by unfold miles;positivity)
 let y:=chat Y s i k T (showtime _ t)
 change π₀ ≤ miles t ^8 * y at u₀
 change _ ≤ _*((ℒ (photo (staged t β f))).re - y) at a'
 linarith only [b,a',u₀,q]

lemma scale_read (t:ℕ)(c:ℝ)(F:Pane (count Y s i)→ℂ) :
 (ℒ (photo (staged t c F))).re=
 c^2*(ℒ (icon (polka 1 (showtime _ t) (false,true) F))).re:=by


 rw [pose_line,←Complex.ofReal_pow]
 unfold Journey.compass
 rw [mark_smul,mul_div_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- price in *any* mass u including Q/(τ²); miles t=2t. -/
lemma coin_rate {ε t} (g:matchedX x β)(j:0<x)
 (h:Strut x t)(p:Cameo Y H (k:=k) ε f T)(q:ε≤π₀/2)
 (v:0<α)(u:α≤dripQ T (χ∘ridge) (χ∘ridge))(a:ℝ):
   π₀/8 * (a/(x * miles t ^4))^2 ≤ (ℒ (photo (staged t a f))).re := by
 have r:=coin_cash Y H χ α h p q v u
 rw [scale_read Y] at r ⊢
 let y:=(ℒ (icon (polka 1 (showtime _ t) (false,true) f))).re
 change _≤_*y
 apply le_trans _ (mul_le_mul_of_nonneg_left
     (show π₀/8/(x*miles t^4)^2 ≤ y from ?_) (sq_nonneg a))
 · rw [div_pow]; exact le_of_eq (by ring)
 have ht:=strut_d h
 have j₀:0 < miles t:=by
     have h₀:0<t:=ht.1
     unfold miles; positivity
 rw [div_le_iff₀ (by positivity:(0:ℝ)<(x*miles t^4)^2)]
 have a₁:0<π₀/2:=half_pos (shines χ α v)
 have e₀:0<y:=pos_of_mul_pos_right (show 0<(miles t)^8 * β^2 * y by
      rw [mul_assoc];exact a₁.trans_le r) (by positivity)


 have d:=mul_le_mul_of_nonneg_left
   (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ ((by positivity:0≤x/2).trans g.1) g.2 2) e₀.le)
    (show (0:ℝ) ≤ miles t^8 by positivity)
 linarith only [r.trans d]

#check feast
#check Cameo
#check coin_rate

end YM.CF.Merino.Medal

