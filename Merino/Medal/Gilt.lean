import SatinThinCrystal
import Merino.Medal.Chess
import Merino.Medal.Diadem
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

variable {f:Pane (count Y s i)→ℂ}{r δ e L:ℝ}{m:ℕ}{T:Bundle SU.group (More (count Y s i))}
variable (w:Scar m r δ L e f T) (z:ℝ) (a:Duo (More (count Y s i))) (b:Tint)

include w in
lemma expose_mark (u:Ferry Y s i k) :
  ℒ (icon (flipper β z a b f))=1+(z:ℂ)*ℒ (icon (polka β a b f)):=by
 rw [icon_flipper]
 have he:=AtSupport.oneM (duet m a)
 unfold Journey.compass
 rw [mark_add (roofage Y i s).bill he.env ((polka_job w β a b).smulM _).env
    (Marks.can_read _ _ _ _ (Y.each_level i k s u.depth u.enters)),mark_smul,add_div,markvac,mul_div_assoc]
 congr 1
 exact div_self (part_here Y i s k u)


/-- non-tilt large volume qualification for chess -/
def Looming (K₀:Calibration)(t L C:ℝ)(l:ℕ)(q:ℕ) :=
 let P₀:=tiltB t
 let D:=clasp (2*t) L P₀
 l+addgap K₀≤ q ∧ Icicle q (dusk t*Diadem.tariff K₀ l) (P₀*C) D

lemma growing (K₀:Calibration)(t L C:ℝ)(C0:0≤C)(hx:0<t)(dc:0<dusk t)
 (l:ℕ):∀ᶠ q in atTop,Looming K₀ t L C l q:=by
 have u:0≤ tiltB t:=(Real.rpow_pos_of_pos hx _).le
 exact (eventually_ge_atTop (l+addgap K₀)).and (ramp (mul_pos dc (tariff_pos ..)) (mul_nonneg u C0) (clasp₀ u (2*t) L))

variable {C:ℝ}{B:ℕ}
include w
lemma pressed (u:Ferry Y s i k)(I:IcePlot Y s i k)(R:stint.{0} Y s i k f T)
 (g:Looming K x L C B (N).val)(h:∀i,cows i (Lattice.halo 0 (duet m a)) B)
 (e': wiggle (height x) ≤ m)
 (c:|chat Y s i k T a|≤C)(X0:0<x)(D0:0<dusk x)(p: |z| ≤ tiltB x):
 ‖1+(z:ℂ)*ℒ (icon (polka β a b f))‖ ≤
 E ((z*chat Y s i k T a + |z| * lean x)+3*(dusk x *Diadem.tariff K B)):=by

 rw [←expose_mark Y w z a b u]
 have h₀:0≤tiltB x := (abs_nonneg _).trans p
 have V:Marble ℒ (solder Y i k u.depth s):=I u.depth
 have X:matchedX x β := (prices_plot Y s i k ?_).2.2.2.1
 swap
 · exact u.enters
 have v:‖β‖≤2*x:=by
    rw [Real.norm_eq_abs,abs_of_nonneg ((show 0≤x/2 by positivity).trans X.1)]; exact X.2
 have j:(0:ℝ)≤C:=(abs_nonneg _).trans c
 refine chess (W:=Patchwork β z a m f) (dusk x) D0 (mul_nonneg h₀ j)
    (clasp₀ h₀ _ _) ?_ g.2 V (fun h=>Patchwork.shift _ _ _ h)
    (Patchwork.job w β z a) ?_ ?_ (revive Y H s i k u)
    (terrain Y H (Y.ir i) s).symm g.1
    (flare β z a b m f) (flare_pay ..) h
 · have h':0≤ |z| * lean x:=mul_nonneg (abs_nonneg _) (Real.rpow_pos_of_pos X0 _).le
   apply le_add_of_le_of_nonneg _ h'; apply neg_le_of_abs_le
   rw [abs_mul];exact mul_le_mul p c (abs_nonneg _) h₀
 · intro A g'
   obtain ⟨r,_,b,s⟩:=g'
   rw [s]; exact iconPay _ _ fun a'=> claspPay β z _ _ a' _ _ _ v w.bound p
 intro U g'
 obtain ⟨j,q,y,e⟩:=layout β z a g' e'
 rw [e]
 have := R a j y q z p
 rw [Fintype.card_fin] at this
 exact this


omit w


lemma answer {C ρ l q t:ℝ}{V:ℂ}
  (h: |t|≤C)(v:0<ρ)(u:ρ*(C+2)≤1)(w:0≤q)(b:q≤ρ*l)
  (j:l≤1)(r:(C+2)^2*ρ≤l)
 (p: ∀z:ℝ,|z| ≤ ρ→ ‖1+(z:ℂ)*V‖≤ E ((z*t+|z| *l)+q)):
 |V.re-t|≤3*l :=by
 have h₁:0≤C:=(abs_nonneg _).trans h
 have h₀:0≤l:=(by positivity : (0:ℝ)≤(C+2)^2*ρ).trans r
 have ht(z:ℝ)(g:|z|=ρ) : z*(V.re-t) ≤ ρ*(3*l):=by
    have h':|z*t+|z| *l+q|≤ρ*(C+2):=by
      have a:=abs_add_le (z*t+|z| *l) q |>.trans <|
         add_le_add (abs_add_le (z*t) (|z| *l)) le_rfl
      rw [abs_mul z t,g,abs_of_nonneg (mul_nonneg v.le h₀),abs_of_nonneg w] at a
      rw [g]; nlinarith only [a,mul_le_mul_of_nonneg_left h v.le,b,mul_le_mul_of_nonneg_left j v.le]
    have a:=le_of_abs_le (Real.abs_exp_sub_one_sub_id_le (h'.trans u))
    have f:=(sq_le_sq.mpr (h'.trans (le_abs_self _))).trans
       (show (ρ*(C+2))^2 ≤ ρ*l from (mul_le_mul_of_nonneg_left r v.le).trans' (le_of_eq (by ring)))


    have g': 1+z*V.re≤ E ((z*t+|z| *l)+q):=(le_trans
       (by simp) <| (Complex.re_le_norm _).trans (p z g.le))
    rw [g] at a f g'; linarith only [a,f,g',b]
 refine abs_le.mpr ⟨?_,(mul_le_mul_iff_right₀ v).mp (ht ρ (abs_of_pos v))⟩
 apply (mul_le_mul_iff_right₀ v).mp
 linarith only [ht (-ρ) (by rw [abs_neg,abs_of_pos v])]

include w in
lemma weigh (u:Ferry Y s i k)(I:IcePlot Y s i k)(R:stint.{0} Y s i k f T)
 (g:Looming K x L C B (N).val)(h:∀i,cows i (Lattice.halo 0 (duet m a)) B)
 (e':wiggle (height x) ≤ m)
 (c:|chat Y s i k T a|≤C)(X0:0<x)(D0:0<dusk x)
 (D:3*(dusk x*Diadem.tariff K B)≤ tiltB x*lean x)
 (U:tiltB x*(C+2)≤1)(j:lean x≤1)(a₀:(C+2)^2*tiltB x≤lean x):
 |(ℒ (icon (polka β a b f))).re-chat Y s i k T a|≤3*lean x :=
  answer c (Real.rpow_pos_of_pos X0 _) U (mul_nonneg (by norm_num) (mul_pos D0 (tariff_pos ..)).le)
   D j a₀ (fun z h'=> pressed Y H w z a b u I R g h e' c X0 D0 h')

end YM.CF.Merino.Medal
