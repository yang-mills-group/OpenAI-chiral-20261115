import YM.SU5.FiniteGaugeData.Marked.Journey.Wood
import YM.SU5.FiniteGaugeData.Marked.Journey.Smokestack

/-!
# Charges for application of Metered/albums.
Need all these partners' estimates together with their heat histories on the
course. Pay them eventually in UV (periodwise kick and heatGap cutoff).
Read the actual full-volume prices with the actual four-volume at this
level, even though only F*bra directions need be tested.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Py Heat

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x) (i k:ℕ)(p:(Y.voyage i).kick ≤ k) (s:ℕ)
local notation "Xₛ" => ((Y.voyage i).X (Y.uv k)).gram s
local notation "Zₛ" => ((Y.voyage i).Q k p).gram s
local notation "lₛ" => (Y.voyage i).CapeT s
local notation "K" => tent Y h
local notation "σ" => Λ.block
local notation "m"=> Y.ir i
abbrev momentm := mesh (Y.ir i) Λ.R.L s
local notation "μ"=> momentm Y i s

private theorem ij : MeterQ Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ Λ.x Y.meter:= Y.paidM
abbrev side := Λ.Ctor (Y.ir i) s
local notation "α" => side Y i s
/-- Account at observing s in cover units for that observing lattice. -/
def vowel (f:Buffered.Mark α)(he:Bool:=false):ℂ:=if he then markedRead f lₛ (denZ Zₛ Λ.U lₛ)/partitionZ Zₛ Λ.U lₛ else markedRead f lₛ (denZ Xₛ Λ.U lₛ)/partitionZ Xₛ Λ.U lₛ
abbrev solder (f:Buffered.Mark α):ℂ:= markedRead f lₛ (denZ Zₛ Λ.U lₛ)/partitionZ Zₛ Λ.U lₛ
abbrev compass (f:Buffered.Mark α):ℂ:= markedRead f lₛ (denZ Xₛ Λ.U lₛ)/partitionZ Xₛ Λ.U lₛ
private lemma depth : Py.buoy (Y.ivory k) < Y.uv k:= LocalLimit.deeper ..

def heating := LocalLimit.Donor.thermalCost Λ.C Λ.R Λ.x Y.τ s+ |serviceCost Y.meter s|
-- `Momentm` refers to actual mesh at s. Consequently adjust by block size
-- but NOT L^(4s), already in momentm.
def duetCharge:= |heating Y s| *(4*(Λ.block.val:ℝ))^4
lemma duetCharge_nn : 0≤duetCharge Y s:= by unfold duetCharge; positivity
private lemma charge : heating Y s*sites (Λ.Ctor m s) ≤ duetCharge Y s * ((μ).val:ℝ)^4:= by
  refine le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by unfold sites; positivity)) (le_of_eq ?_)
  unfold sites Preparation.Ctor cell CSide More
  unfold duetCharge momentm
  push_cast
  ring_nf

variable (g:LocalLimit.Donor.Gap Y.meter (Y.voyage i).funds Λ.C Λ.δ Λ.R0 Y.τ ((Y.voyage i).X (Y.uv k)) ((Y.voyage i).Q k p) s)
include g
local notation "X"=> solder Y i k p s

private lemma feeL (f:Mark α): X f = markedRead f lₛ (ratioField Λ.V Zₛ lₛ Λ.U):= Marks.normalized Λ.V Λ.U _ _ (f ∘ drawn lₛ)
private lemma fee (f:Mark α)(w:Envelope f):
    ‖X f‖ ≤ Real.exp (duetCharge Y s * ((μ).val:ℝ)^4) * cash lₛ f := by
  let V₀:= Real.exp (duetCharge Y s * ((μ).val:ℝ)^4)
  have ht x: ‖ratioField Λ.V Zₛ lₛ Λ.U x‖ ≤ V₀:= (g.priceH.rate x).trans (Real.exp_le_exp_of_le (charge Y i s))
  rw [feeL Y i k p s g,mul_comm (Real.exp _)]; unfold markedRead cash; rw [←integral_mul_const]
  exact (norm_integral_le_integral_norm ..).trans (integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _))
    ((cashable ((Y.voyage i).ownership s).paid.bill w).mul_const _)
    (Eventually.of_forall fun i=>(mark_bound ..).trans (mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _))))
private lemma burning {a:Axis}{z:ℤ}{f:Mark α} (j:s ≤ Y.uv k) (w:AtSupport false (band α a (Heat.gaugeShift σ z) (reserve Λ l)) f):
    0 ≤ X (reflMark a (Heat.gaugeShift σ z) f*f):=by
  have he: 0 ≤ partitionZ Zₛ Λ.U lₛ:=by
    have hp:= throbbing Y i k p s j a z 1 (AtSupport.oneM (band α a (Heat.gaugeShift σ z) (reserve Λ l)))
    rwa [mul_one,show reflMark a (Heat.gaugeShift σ z) (1:Mark α)=1 from funext fun _=> Fock.theta_one _,markvac] at hp
  exact div_nonneg (throbbing Y i k p s j a z f w) he
-- cast from observing level s to the tent family, level 0 language at mesh m L s.
-- keep it explicit to see which data are re-read.
def deltaL : Loom ((K).c μ):= (terrain Y h m s).symm ▸ lₛ
def send (f:Mark ((K).c μ)):Mark (Λ.Ctor m s):= (terrain Y h m s) ▸ f
def collector (f:Mark ((K).c μ)):= X (send Y h i s f)
def listen (f:Mark ((K).c μ)):= compass Y i k s (send Y h i s f)


omit g in
private theorem congrMeter {K':Calibration}{A M:Side}(H:A=K'.c M)
    (F:Mark A→ℂ)(L:Loom A)(D:ℝ) (hd:0 ≤ D)
    (hE:∀ f:Mark A,Envelope f → ‖F f‖ ≤ Real.exp (D*(M.val:ℝ)^4)*cash L f)
    (h1:∀ f g:Mark A,Envelope f→ Envelope g→F (f+g)=F f+F g) (h2:∀ (a:ℂ)(f:Mark A),F (a • f)= a*F f)(h3:F 1=1)
    (h4:∀ (a:Axis)(z:ℤ)(f:Mark A), AtSupport false (band A a (gaugeShift K'.B z) K'.ℓ) f → 0 ≤ F (reflMark a (gaugeShift K'.B z) f*f))
    (w:∃ a b c,Roof A a b c L)(t: Advance.LoomLaw L K'.w):
    Metered K' M (H ▸ L) (fun (x:Mark (K'.c M))=> F (H.symm ▸ x)) D:=by subst_vars; exact ⟨hd,hE,h1,h2,h3,h4,w,t⟩

lemma boxprice (j:s≤Y.uv k): Metered (tent Y h) μ (deltaL Y h i s) (collector Y h i k p s) (duetCharge Y s):=by
  have e:Measurable lₛ:= ((Y.voyage i).ownership s).paid.bill
  have ht':= Marks.can_read _ _ _ _ g.priceH
  apply congrMeter (terrain Y h m s).symm X lₛ _ (duetCharge_nn Y s) (fee Y i k p s g)
    (fun f t v w=> by unfold solder; rw [mark_add e v w ht',add_div])
    (fun c f=> by unfold solder; rw [mark_smul,mul_div_assoc])
    (by unfold solder; rw [markvac]; exact div_self g.priceH.valid)
    (fun a z f u=> burning Y i k p s g j u)
    ⟨_,_,_,((Y.voyage i).ownership s).paid⟩ (tissue Y i s)

omit g in
lemma move_law : VolumeCape.Dream.Nimbus l _ (deltaL Y h i s):= by
  unfold deltaL; generalize e:lₛ=r at * -- maybe
  have u:VolumeCape.Dream.Nimbus l α r:=e ▸ ((Y.voyage i).craft s)
  exact transport (terrain Y h m s).symm u
where
 transport{t u:Side}{a:Loom t} (h:t=u)(p:VolumeCape.Dream.Nimbus l t a) : VolumeCape.Dream.Nimbus l u (h ▸ a):=by subst t; exact p
end YM.CF.Buffered.Afterglow.Journey
