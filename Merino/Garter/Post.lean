import Merino.Garter.Map
import Merino.Garter.Duck
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

/-- L cost. e0 raw defect after β scaling, h scalar bound **on used ice coordinates**, M reciprocal clip scale, π max tilt size. -/
def slip(L h M:ℝ):=L*((M⁻¹)^2*2*h^4)
def nick(L e0 h M):= e0+slip L h M
def basisCost(L e0 h M):=nick L e0 h M+L*h^2
def sceneTick (L e0 h M π:ℝ):=
 let w:=basisCost L e0 h M
 2*w*nick L e0 h M+π*((w^2)^2/2)

-- Single
variable {L e0 h M τ E:ℝ}{f:Config G n→ℂ} {T:Bundle G n}

abbrev yStep(f:Config G n→ℂ)(t:Bool)(β:ℝ)(a:StepIn n)(U:Config G n):=
 dart t ((β:ℂ)*f (a.cabin U))
lemma posty
 (t:Scar (shellC m) p.threshold τ L E f T)
 (X:Altar G n)(a:StepIn n)
 (hs:∀ i:Husk G n,separation 0 i.1.1 ≤ slim (shellC m) → |silver q a i X|≤ h)
 (M:ℝ):
 |gleam T q M⁻¹ a X| ≤ L*h^2 ∧
 |gleam T q M⁻¹ a X-gloss T q a X| ≤ slip L h M:=by


 have u(i j)(k:T i j≠0): |shine q M⁻¹ a X i|≤ h ∧ |shine q M⁻¹ a X j|≤ h:=
   ⟨(chew_small ..).trans (hs _ (t.cloth.both k).1),
    (chew_small ..).trans (hs _ (t.cloth.both k).2)⟩
 refine ⟨splash _ t.cloth.rent u,?_⟩
 rw [←gleam_zero]
 unfold gleam
 simp_rw [show ∀ u v, dripQ T u v=pour T (fun i j=>u i*v j) from fun _ _=>rfl]
 rw [pour_sub]
 exact pour_abs _ (by positivity) t.cloth.rent fun i j k=>pair_gap _
    (hs _ (t.cloth.both k).1) (hs _ (t.cloth.both k).2)

lemma postg (t:Scar (shellC m) p.threshold τ L E f T)
 (Y:ℂ)
 (X:Altar G n)(a:StepIn n)
 (hs:∀ i:Husk G n,separation 0 i.1.1 ≤ slim (shellC m) → |silver q a i X|≤ h)
 (u:‖Y-gloss T q a X‖ ≤ e0)
 (b:Bool)(M:ℝ):
   ‖dart b Y-(gleam T q M⁻¹ a X)‖ ≤ nick L e0 h M ∧
   |gleam T q M⁻¹ a X| ≤ basisCost L e0 h M ∧ ‖dart b Y‖ ≤ basisCost L e0 h M:=by
 obtain ⟨c,g⟩:=posty t X a hs M


 have y:‖dart b Y- (gleam T q M⁻¹ a X)‖ ≤ nick L e0 h M:=by
    rw [dart_bit]
    apply (norm_sub_le_norm_sub_add_norm_sub _ (gloss T q a X : ℂ) _).trans
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm (gloss ..)]
    exact add_le_add u g
 exact ⟨y,c.trans (le_add_of_nonneg_left ((norm_nonneg _).trans y)),
   (norm_le_norm_add_norm_sub ((gleam T q M⁻¹ a X):ℂ) _).trans ((add_le_add
      (Complex.norm_real _|>.trans_le c) ((norm_sub_rev ..).trans_le y)).trans_eq (add_comm ..))⟩

lemma postBill {W I:ℝ}(p:0≤I){x y:ℂ}{a b:ℝ}
 (hx:‖x-(a:ℂ)‖≤I ∧ |a|≤W ∧ ‖x‖≤W)(hy:‖y-b‖≤I ∧ |b|≤W ∧ ‖y‖≤W):
  ‖x*y-((a*b:ℝ):ℂ)‖ ≤ 2*W*I ∧ ‖x*y‖ ≤ W^2 := by
 have z:0≤W:=(abs_nonneg _).trans hx.2.1
 constructor
 swap; · rw [norm_mul,pow_two]; exact mul_le_mul hx.2.2 hy.2.2 (norm_nonneg _) z
 rw [Complex.ofReal_mul,show x*y-↑a*↑b=(x-↑a)*y+↑a*(y-↑b) from by ring]
 apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]
 exact (add_le_add (mul_le_mul hx.1 hy.2.2 (norm_nonneg _) p)
   (mul_le_mul (Complex.norm_real _|>.trans_le hx.2.1) hy.1 (norm_nonneg _) z)).trans_eq (by ring)


lemma postLog {z a s X W u:ℝ}{x:ℂ}(t:|z|≤ s)(d:‖x-a‖≤X)(M:‖x‖≤W):
 logₛ u ((z:ℂ)*x)-z*a≤ |z| * (X+s*(W^2/2)):=by
 refine (sub_le_sub_right (min_le_left ..) _).trans ?_
 have y: (z*x-z*a : ℂ).re≤ |z| * X:=calc
    _ ≤ ‖(z:ℂ)*x-z*a‖:=Complex.re_le_norm _
    _ ≤ _:=by
      rw [←mul_sub,norm_mul, Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left d (abs_nonneg _)
 have r: ‖(z:ℂ)*x‖^2≤ |z| * (s*W^2):=by
    rw [norm_mul,mul_pow, Complex.norm_real,Real.norm_eq_abs,pow_two |z|,mul_assoc]
    exact mul_le_mul_of_nonneg_left
       (mul_le_mul t (pow_le_pow_left₀ (norm_nonneg _) M _) (sq_nonneg _) ((abs_nonneg _).trans t)) (abs_nonneg _)
 rw [Complex.sub_re,← Complex.ofReal_mul,Complex.ofReal_re] at y
 linarith only [y,r]


structure Offer (R:Rules G)(p:BudgetPoint)(m:ℕ)(L β E τ e0 h M P v:ℝ):Prop where
 roomy : 400 ≤ m
 mp : 0 < M
 ep : 0≤e0
 h0 : 0 ≤ v
 radius : v ≤ R.c
 aperture : 2*v ≤ τ
 bill : 0 ≤ β
 dollars : β*(L*(2*v)^3+E) ≤ e0
 cents : Real.sqrt β*(p.threshold+faceCutError R v) ≤ h
 spare : P*(L*M^2)^2 ≤ 1
 cap : 1+P*(β*L)^2 ≤ Real.exp (wiggle m)

variable (B:Z.Bounds q η C S)(P0:Attached H Z){R:Rules G}{z P:ℝ}
  {X Y:Dir G n}{U:Config G n}
lemma postGood 
 (t:Scar (shellC m) p.threshold τ L E f T)
 (u:Offer R p m L β E τ e0 h M P v)
 (e:N=meek p U)
 (l:TrustLogs (X+Y) U r A v)
 (x:ProbeBox (X+Y) (2*v))
 (hp:|z|≤P)
 (g:Duo n)(b:Tint)
 (a:Deep r A N (living m) g.1.there)
 (d:Deep r A N (living m) g.2.there):
   logₛ (wiggle m) ((z:ℂ)*polka β g b f U) -
    z* couple T q M⁻¹ g (iceCost B P0 r A m N Y β X)
    ≤ |z| * sceneTick L e0 h M P:=by


 let V:=iceCost B P0 r A m N Y β X
 let y:=fun(a:StepIn n)=>(β:ℂ)*f (a.cabin U)
 have p₂(a:StepIn n)(d:Deep r A N (living m) a.there)(e':Bool): 
    ‖dart e' (y a)-gleam T q M⁻¹ a V‖ ≤ nick L e0 h M ∧
    |gleam T q M⁻¹ a V| ≤ basisCost L e0 h M ∧
    ‖dart e' (y a)‖ ≤ basisCost L e0 h M:=by
    obtain ⟨g',b'⟩:=payment B P0 t u.aperture u.roomy d u.bill e l u.h0 u.radius x
    exact postg t (y a) V a (q:=q) (fun i h=>(b' i h).trans u.cents)
       (g'.trans u.dollars) e' _
 have o:=p₂ _ a b.1
 have p':=postBill ((norm_nonneg _).trans o.1) o (p₂ _ d b.2)
 exact postLog hp p'.1 p'.2


lemma postRim {P0:Attached H Z}
 (t:Scar (shellC m) p.threshold τ L E f T)
 (u:Offer R p m L β E τ e0 h M P v)
 (k:hallBill m ≤ r.count.val/2)(d:Odd r.count.val)
 [Fintype I]{g:Duo n}{j:I→StepIn n}(hj:Pavilion (wiggle m) g j)
 (b:I→Tint)
 (hp:|z|≤P)(s₀:ℝ) :
  RimScene B P0 p r m β v
    (2 * (Fintype.card I*(|z| * sceneTick L e0 h M P))+
       fritTrap r m A N) s₀ A N
    2 (lorg β z g m f j b) (displayBoard T q M⁻¹ g j z):=by
 intro V X Y _ γ x l
 apply (sub_le_iff_le_add').mp -- sub≤iff? 
 rw [←mul_sub,lorg,displayBoard,mul_sum,←sum_sub_distrib]
 have ht:0≤ |z| * sceneTick L e0 h M P:=by
   have L0:0≤L:=(norm_nonneg _).trans (t.bound V)
   have e':=u.ep
   have h0:0≤P:=(abs_nonneg _).trans hp
   unfold sceneTick nick slip basisCost
   unfold nick slip
   positivity


 refine gates d k hj _ ht ?_ (fun i a w=>postGood B P0 t u γ l x hp _ _ a w)
 intro i; rw [sub_eq_add_neg]
 apply add_le_add (min_le_right ..)
 apply le_trans (neg_le_abs _)
 rw [abs_mul]
 exact le_trans (mul_le_mul hp
    (couple_free _ t.cloth.rent u.mp ..) (abs_nonneg _) ((abs_nonneg _).trans hp)) u.spare
end YM.CF.Merino.Garter
