import YM.SU5.WindTorque.Issuance
import Lucent.Preset
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Buffered.Afterglow.Tower
open Gist Kea Onyx Papal
open Vale Jewel
variable {I:Type}[Fintype I]
local notation "X" s:max => hat P.R.L P.x s
local notation "λₐ" s:max t:max => sPow P s t
local notation "ψ" s:max => chip (hat P.R.L P.x s) (-3)

/-- all-stage wavelength P-ledger. Here standard fixes r=zoomR in
materia, R=sPow in gauge, exactly the Agenda AP pair convention;
can use any coupled subpowers in subsequent stages. -/
structure Velocity (P: Preparation)(R:ℕ→ℝ)(r:ℕ→ℕ):Prop where
  gauge: Tendsto R atTop atTop
  matter: Tendsto (fun n=>(r n:ℝ)) atTop atTop
  coupled: Tendsto (fun n=> R n/(r n:ℝ)) atTop (𝓝 2)
  p:∀ n,0<R n
  t:∀ n,0<(r n:ℝ)
  book:∃ A:ℝ,0<A ∧ ∀ᶠ s in atTop,R s ≤ sPow P s A

abbrev gyrP (P:Preparation)(z:ℝ)(s:ℕ):= sPow P s z
lemma zooming_p (P:Preparation) (z:ℝ)(s:ℕ): 0<(zoomR P z s:ℝ) := (half_pos (BProof.coin_pos ..)).trans_le (Nat.le_ceil _)
lemma Velocity.normal (P:Preparation) {a:ℝ}(b:0<a):
 Velocity P (gyrP P a) (zoomR P a):=by
 refine ⟨sPower_pay P b,tendsto_natCast_atTop_atTop.comp (zoom_grows P b),?_,fun _=>BProof.coin_pos ..,zooming_p P _,_,b,Eventually.of_forall fun _=> le_rfl⟩
 have v:=(fray_lift P b).mul_const (2:ℝ)
 rw [one_mul] at v
 refine v.congr fun n=> ?_
 have t:= zooming_p P a n; unfold frayR; field_simp
lemma maxnorm {u:ℝ}(m a:ℕ)(p:0≤u):
 ‖maxZoom u m a‖≤u^(2*m+3*a):=by
 unfold maxZoom; simp only [norm_mul,norm_div,norm_pow, Complex.norm_real,Real.norm_of_nonneg p, pow_add,pow_mul]
 gcongr; exact div_le_self (by positivity) (by norm_num)

lemma Velocity.small {R r}(h:Velocity P R r) (m a:ℕ):
   Tendsto (fun s=> ‖maxZoom (R s) m a‖*(ψ s)) atTop (𝓝 0):= by
 obtain ⟨A,p,w⟩:=h.book
 refine Metric.tendsto_nhds.mpr fun e k=>?_
 let v:=2*m+3*a
 let l:=A*v
 have t:= BProof.coin_budget (a:=-3/400000) (b:=l) (c:=0) (e:=0) (f:=0) (d:=0) (Or.inl (by norm_num)) 1 e k
 filter_upwards [w,(turnover P).eventually t] with s g u
 have hz:= (chip_pos (X s) (-3)).le
 rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg (norm_nonneg _) hz)]
 apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_trans (maxnorm m a (h.p s).le) (pow_le_pow_left₀ (h.p s).le g v)) hz)
 rw [sPow, BProof.coin_pow,WakeInvestment.chip,BProof.coin_mul,zero_mul,zero_add,add_zero,add_zero]
 simpa [BProof.coin_zero] using u

/-- Toll-rider. Width and room payments for the assembled decoded Mark.
 Uniform personnel tickets. -/
def Expense(P:Preparation)(s:ℕ)(A:ℝ)(S:Stencil I)(W:I→Staff)(b:ℕ):Prop:=
 Singing W S ∧ ∃ (w e:ℕ),
 (∀ n:Side, ∃ o:Seat n,rail W b w n o e) ∧
 (w:ℝ) ≤ sPow P s A ∧ (e:ℝ) ≤ sPow P s A

abbrev ridingRaw(P:Preparation)(β:ℕ→ℝ)
    (W:I→Staff)(b:ℕ)(S:Stencil I)(s:ℕ):= kite b (κFix β s) (temp (hat P.R.L P.x s)) W S -- uses P x defined notation "X" resolves?
abbrev riding (P:Preparation)(β:ℕ→ℝ)
    (W:I→Staff)(b:ℕ)(S:Stencil I)(s:ℕ)(R:ℝ)(m a:ℕ):= qr W (κFix β s) R (temp (hat P.R.L P.x s)) S m a b
abbrev rider (P:Preparation)(β:ℕ→ℝ)(K:Calibration)(W:I→Staff)(b:ℕ)(S:Stencil I)(s:ℕ)(R:ℝ)(m a:ℕ):=
 Papal.household K (riding P β W b S s R m a)

abbrev band (W:I→Staff)(b:ℕ):Finset Cover:= by classical exact univ.biUnion (fun j=>(W j).skyRent b)
lemma ridingPermit {W:I→Staff} {b:ℕ} {A:ℝ}{S:Stencil I}
    (K:Calibration) (s:ℕ)(t:Expense P s A S W b)(β:ℕ→ℝ):
   TestFamily K true (household K (ridingRaw P β W b S s)):= by
 classical
 obtain ⟨x,w,e,h,u,z⟩:=t
 obtain ⟨o,c⟩:=h ⟨1,Nat.one_pos⟩
 exact (singing_test W S K (κFix β s) (temp (hat P.R.L P.x s)) x
      (show Charter W (band W b) b w from fun j=>⟨(c j).1,fun x h=>Finset.mem_biUnion.mpr ⟨j,mem_univ _,h⟩⟩)).1

open Buffered.Afterglow.Tower
variable {ζι ζη π μ:ℕ→ℕ} {H:Real.exp 1≤P.x}
variable {Φ0:ℕ→ Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→ Buffered.Family (tent Y H)→ℂ}
variable {D:ℕ→ Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
variable (U:Universal Y H ζι ζη Φ0 E) (Q:Coherent (i:=ζι) (k:=ζη) (E:=E) Y H D π μ)
local notation "iA" => ζι ∘ π
local notation "kA" => ζη ∘ μ
include U Q

variable {A:ℝ}
lemma sharpScale {β:ℕ→ℝ}{W:I→Staff}{b}{S}{R:ℝ}{m a} (s:ℕ)
   (h:Expense P s A S W b):
   Tendsto (fun j=> maxZoom R m a * signature Y s (iA j) (kA j) W (κFix β s) S b)
     atTop (𝓝 (E s (rider P β (tent Y H) W b S s R m a))):=by
 let G:=ridingRaw P β W b S s
 let F:= household (tent Y H) G; have t:TestFamily (tent Y H) true F:=ridingPermit _ _ h β; let c:= maxZoom R m a
 change Tendsto _ atTop (𝓝 (E s (c • F))); rw [E_scale Y H U s t]
 refine ((sharp_on_track Y U Q s t).const_mul c).congr fun j=>?_ -- tune U
 rw [show Journey.sharp _ _ _ _ _ _ = Journey.compass Y (iA j) (kA j) s (expSrc Y s (iA j) H (household _ G)) from rfl,lift_book]
