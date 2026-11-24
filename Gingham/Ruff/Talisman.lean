import Gingham.Ruff.Falcon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false


open Lander
variable {a c μ d}
variable {F:ℕ→Fleece P.calibration}{ν:ℕ→ℕ}
variable (β:Lander P a c μ d ν F)
   {δ t:ℝ}{X:Rialto 6 P.par.d δ t}
   (w:Anthem P a c μ d δ t X)(hp:1≤ρ)
local notation "w'"s:max=>peak P s
local notation "Q"s:max=>chi P s
local notation "g"s:max=>w' s * (Q s / (~p~ s).threshold^2)


def honey (P:Spine)(ρ δ a c:ℝ):ℝ:=
  1 + 2*(|resin P δ a c|+8*cream P ρ a c)
def loud(P:Spine)(s:ℕ):ℝ:=
 peak P s * (chi P s / (P.run.meter.a s).threshold^2)
def soft(P:Spine)(s:ℕ):ℝ:=
 chi P s / (P.run.meter.a s).threshold^2
open Six
variable {C₀:ℝ}
structure Amethyst (P:Spine)(F:ℕ→Fleece P.calibration)(ρ:ℝ)(ν:ℕ→ℕ)(s:ℕ)
     (C:ℝ): Prop where
 pos : 1≤C
 bass : ∀j, Regalia P ρ s ν (wisp (P.run.meter.a s))
        (Ante (chi P s) j (F s)) (C*chi P s)
 gauge : ∃ r: Regalia P ρ s ν (wisp (P.run.meter.a s))
        (YokeTicket (soft P s) (F s)) (C*chi P s), PureGauge P.calibration r.ticket
 soprano: Regalia P ρ s ν (frond P.calibration (P.run.meter.a s))
        (wingtip (loud P s) (F s)) (C/(peak P s)^7)
 toe: Regalia P ρ s ν (frond P.calibration (P.run.meter.a s))
        (wingtip (soft P s) (F s)) (C/(peak P s)^8)





include β w hp
lemma stanza : ∀ᶠ s in atTop, Amethyst P F ρ ν s (honey P ρ δ a c):=by
 let D:= cream P ρ a c
 let T:= resin P δ a c
 let H:= honey P ρ δ a c
 have h₀:0≤|T|:=abs_nonneg _
 have d₀:0≤D:=le_max_left ..
 have hH:H=1+2*(|T|+8*D):=rfl
 filter_upwards [β.collar (zero_le_one.trans hp),β.lamps (ρ:=ρ) w,
        β.ensemble w (zero_le_one.trans hp),giltS β]
          with s k l j ⟨ts,tb,v,u⟩
 let I:= T*(~p~ s).threshold^2
 let z:=soft P s
 let L:=peak P s
 have p:0<z:=div_pos ts (pow_pos tb _)
 have m₀ : I≤|T|:= (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg ..)).trans
       (mul_le_of_le_one_right h₀ (pow_le_one₀ tb.le v))
 have a₀:0<L:=zero_lt_one.trans_le (pkPos P s)
 refine ⟨show 1≤H from by linarith only [h₀,hH,d₀],?_,?_,?_,?_⟩
 · intro i
   apply ((k i).scale (Q s)).raise
   rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ts,mul_comm]
   exact mul_le_mul_of_nonneg_right (show D≤H from by linarith only [hH,h₀,d₀]) ts.le


 · have a: |z| * I ≤ H * chi P s:= by
     have i:z*I= T*chi P s:= by
        unfold z I soft
        rw [mul_comm (chi P s / _), mul_assoc, ←mul_div_assoc,
            mul_comm ((~p~ s).threshold^2), mul_div_cancel_right₀ _ (pow_pos tb 2).ne']
     rw [abs_of_pos p,i]
     exact mul_le_mul_of_nonneg_right ((le_abs_self T).trans
        (by linarith only [hH,h₀,d₀])) ts.le
   let r: Regalia P ρ s ν (wisp (~p~ s)) (YokeTicket (soft P s) (F s)) (H*chi P s):=
       (l.choose.scale (soft P s)).raise (show _ from (by rw [Complex.norm_real,Real.norm_eq_abs];exact a))
   refine ⟨r,(pale_iff P _).mp ?_⟩
   have h: Paleness K l.choose.ticket:=(pale_iff P l.choose.ticket).mpr l.choose_spec
   exact fun m x=>Submodule.smul_mem _ (soft P s:ℂ) (h m x)
 · apply (j (loud P s)).raise
   rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<loud P s from mul_pos a₀ p)]
   have y:L*z≤2/L^7:=by
      refine (mul_le_mul_of_nonneg_left (show z≤2/L^8 from u) a₀.le).trans_eq ?_
      field_simp
   change L*z*(I+8*D) ≤ H/L^7
   refine (mul_le_mul_of_nonneg_left (add_le_add_left m₀ (8*D)) (mul_pos a₀ p).le).trans
     ((mul_le_mul_of_nonneg_right y (show 0≤|T|+8*D from by positivity)).trans ?_)
   rw [div_mul_eq_mul_div]
   exact div_le_div_of_nonneg_right (by linarith only [hH]) (by positivity)
 apply (j z).raise
 rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos p]
 change z*(I+8*D) ≤ H/L^8
 refine (mul_le_mul_of_nonneg_left (add_le_add_left m₀ (8*D)) p.le).trans
     ((mul_le_mul_of_nonneg_right (show z≤2/L^8 from u) (show 0≤|T|+8*D from by positivity)).trans ?_)
 rw [div_mul_eq_mul_div]
 exact div_le_div_of_nonneg_right (by linarith only [hH]) (by positivity)
#print axioms stanza
