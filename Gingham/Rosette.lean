import Gingham.Shuttle
/-!
Strict budgets for the chosen appointments: Eu literal widths and limiting
pair; real widths at projected prices (WPermit, same election) then removal of
pads. Continuation to the real edge does not call for transporting the size
of the Eu margin numerically. There is one positive margin for both
discrepancies before taking real pad limits, and the real discrepancy
with all heats removed, even at the original positive charge.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration YM.Velour
variable (a:Weave)
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


def guess (r:Parts) := r.2.1*r.2.2

/-- Two readings accounted separately (so not just controlling discrepancy).
Also pay each factor, to be clear about scope even when products are small. -/
def Topaz (t r:Parts)(ε:ℝ):Prop :=
    dist t.1 r.1< ε ∧ dist (guess t) (guess r)<ε ∧
    dist t.2.1 r.2.1 < ε ∧ dist t.2.2 r.2.2 < ε

def Jubilation (r:Parts)(ε:ℝ):Prop := 8*ε < ‖discrepancy r‖

lemma keep_encounter (r t:Parts) {ε:ℝ} (s:Jubilation r ε)
    (h:Topaz t r ε):
    6*ε < ‖discrepancy t‖ := by
  
  have e: dist (discrepancy t) (discrepancy r)< 2*ε:= by
    rw [dist_eq_norm]
    rw [show discrepancy t - discrepancy r = (t.1-r.1)-(guess t - guess r) by
      unfold discrepancy guess; abel]
    refine (norm_sub_le ..).trans_lt ?_
    rw [←dist_eq_norm,←dist_eq_norm]
    linarith only [h.1,h.2.1]
  rw [dist_comm,dist_eq_norm] at e
  unfold Jubilation at s
  have b:=norm_add_le (discrepancy r - discrepancy t) (discrepancy t)
  rw [sub_add_cancel] at b
  linarith only [b,s,e]

lemma likelier (x y:Parts){δ:ℝ}
    (t:Topaz y x δ):
    {z | Topaz z x δ}∈𝓝 y := by
  have m (g:Parts→ℂ)(p:Continuous g)
    (v:dist (g y) (g x)<δ) :
     ∀ᶠ z in 𝓝 y, dist (g z) (g x)<δ :=
       ((p.tendsto y).dist tendsto_const_nhds).eventually (gt_mem_nhds v)
  show ∀ᶠ z in 𝓝 y,Topaz z x δ
  filter_upwards [m (·.1) continuous_fst t.1, m guess
    (continuous_snd.fst.mul continuous_snd.snd) t.2.1,
    m (·.2.1) continuous_snd.fst t.2.2.1,
    m (·.2.2) continuous_snd.snd t.2.2.2]
    with z a b c d
  exact ⟨a,b,c,d⟩

lemma Topaz.refl (x:Parts){ε:ℝ}(p:0<ε):Topaz x x ε:=by
  simp [Topaz,p]

abbrev silk₁ (y:D) : ℂ := inner ℂ ω₁ y.val
local notation "𝐄"=> Module.End ℂ D

def rtux (X Y:𝐄): Parts :=
  (rcoupled 𝓢 Ω X Y,rcup 𝓢 Ω X,rcup 𝓢 Ω Y)

lemma rtux_surging {ι:Type} {p:Filter ι}{X Y:ι→𝐄}{B C:𝐄}
    (h:(𝓢).Surges p X B)
    (k:(𝓢).Surges p Y C):
    Tendsto (fun i=>rtux P x (X i) (Y i)) p (𝓝 (rtux P x B C)) :=
 (tendsto_const_nhds.inner (((h.mul k).at_one Ω).plain)).prodMk_nhds
    ((tendsto_const_nhds.inner (h.at_one Ω).plain).prodMk_nhds
       (tendsto_const_nhds.inner (k.at_one Ω).plain))


variable (g m:Hook P x)

abbrev AudReal : Parts :=
   rtux P x (RealLeft P x a (pelisse P x g)) (RealRight P x a (pelisse P x m))

lemma guesses_related : guess (AudEu a P x g m) = guess (AudReal a P x g m):=by
  change cup ω₁ (EuLeft P x a _) * cup ω₁ (EuRight P x a _) =
     rcup 𝓢 Ω (pelisse P x g (sachet_LocalFieldBounds a.blot)) *
     rcup 𝓢 Ω (pelisse P x m (sachet_LocalFieldBounds a.well))
  rw [real_dose_actual P x _ a.topay _ a.blot_one,real_dose_actual P x _ a.topay _ a.well_one,
      EuLeft,EuRight, Eu_dose_actual _ _ _ _ _ _ _ a.blot_one,
      Eu_dose_actual _ _ _ _ _ _ _ a.well_one]

/-- Appointment with strictly positive budget e on both sides of both
inputs. An ordered way, not a simultaneous worst-case heat→0,
width→0 limit. Includes width already at consultations. -/
def StageReal (e:ℝ≥0) : Parts :=
   rtux P x ((𝓢).labelled (toll P x g e) (sachet_LocalFieldBounds a.blot))
            ((𝓢).labelled (toll P x m e) (sachet_LocalFieldBounds a.well))
def WidthReal (e:ℝ≥0) (i k:ℕ) : Parts :=
   rtux P x
     ((𝓢).labelled (g.arms.Wstage x 3 e e i) (sachet_LocalFieldBounds a.blot))
     ((𝓢).labelled (m.arms.Wstage x 3 e e k) (sachet_LocalFieldBounds a.well))

lemma rt_without : Tendsto (StageReal a P x g m) (𝓝[>] 0)
    (𝓝 (AudReal a P x g m)) := rtux_surging _ _
      ((collects P x g).harvest _) ((collects P x m).harvest _)
lemma rt_with (e:ℝ≥0) (b:0<e)
    {s u:ℕ→ℕ}(t:Tendsto s atTop atTop)
    (n:Tendsto u atTop atTop):
    Tendsto (fun i=> WidthReal a P x g m e (s i) (u i)) atTop
      (𝓝 (StageReal a P x g m e)):=
   rtux_surging _ _
     ((𝓢).surges_width ((flew (g.earns.arriving _ b)).glints t)
       (tendsto_const_nhds (x:=sachet_LocalFieldBounds a.blot)))
     ((𝓢).surges_width ((flew (m.earns.arriving _ b)).glints n)
       (tendsto_const_nhds (x:=sachet_LocalFieldBounds a.well)))


abbrev HeatPaid (e:ℝ≥0) (i k:ℕ):Prop :=
 (g.arms.fieldA i).allowance P 3 < e ∧ (m.arms.fieldA k).allowance P 3 < e

lemma resists (e:ℝ≥0) (b:0<e)
    (W:Set Parts)(p:W∈𝓝 (StageReal a P x g m e)) :
    ∃ n:ℕ,∀ i k:ℕ, n ≤ i→ n ≤ k →
      HeatPaid P x g m e i k ∧ WidthReal a P x g m e i k∈ W:=by
  by_contra! h
  choose s₁ s₂ t u z using h
  have h₁ := tendsto_atTop_mono t tendsto_id
  have h₂ := tendsto_atTop_mono u tendsto_id
  have v:∀ᶠ _n:ℕ in atTop,False:=by
    filter_upwards [h₁.eventually ((g.earns.thin (3:Axis)).eventually (gt_mem_nhds b)),
                    h₂.eventually ((m.earns.thin (3:Axis)).eventually (gt_mem_nhds b)),
                    (rt_with a P x g m _ b h₁ h₂).eventually p] with n a d t
    exact z n ⟨a,d⟩ t
  obtain ⟨i,h⟩ := v.exists
  contradiction

/-- Keep this assessment without dependence on the representatives.
Crossed answers at *both* limiting tests have margin >8δ; by
`keep_encounter`, each ledger precursor has margin >6δ.
Premise is the M8 elected device itself; **not changing election anywhere**.
The pressure account costs no rate on testing a smearing outside the ordered
placements; heat protocol is real, symmetric common total price.
-/
structure Glory (δ:ℝ):Prop where
  cash : 0<δ
  at_eu: Jubilation (AudEu a P x g m) δ
  at_real: Jubilation (AudReal a P x g m) δ
  eu_ledger :
     ∃ n,∀ i k t:ℕ, n ≤ i → n ≤ k → n ≤ t → Height P x g m i k t →
       InBuoy a P x g m i k t ∧
       Topaz (GridEu a P x g m i k t) (AudEu a P x g m) δ
  real_ledger :
    ∀ᶠ e in 𝓝[>] (0:ℝ≥0),
       Topaz (StageReal a P x g m e) (AudReal a P x g m) δ ∧
       ∃ n:ℕ,∀ i k:ℕ, n ≤ i→ n ≤ k →
       HeatPaid P x g m e i k ∧
       Topaz (WidthReal a P x g m e i k) (AudReal a P x g m) δ


lemma blush (J:P.Ellis 3 x) (h:simultaneous_at P x a g m):
    ∃ δ, Glory a P x g m δ := by
  let R:=AudReal a P x g m
  let E:=AudEu a P x g m
  let d:=min ‖discrepancy R‖ ‖discrepancy E‖
  have t:0< d := lt_min (norm_pos_iff.mpr h.2.2) (norm_pos_iff.mpr h.2.1)
  let δ:= d/9
  have u:0<δ:=div_pos t (by norm_num)
  have p:8*δ< d:=by unfold δ; linarith only [t]
  refine ⟨δ,u,p.trans_le (min_le_right ..),p.trans_le (min_le_left ..),
    wide_travel a P x g m J _ (likelier E E (Topaz.refl E u)), ?_⟩
  have n := (rt_without a P x g m).eventually (likelier R R (Topaz.refl R u))
  filter_upwards [n,eventually_mem_nhdsWithin] with e he b
  exact ⟨he, resists a P x g m e b _ (likelier R _ he)⟩

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

