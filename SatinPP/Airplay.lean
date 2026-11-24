
import SatinPP.Troupe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Set MeasureTheory
open Silk OS OS.Semigroup Spectral Boundary Probe Hierarchy.Seld
open YM.Quays YM.SatinJets
open scoped Topology Matrix BigOperators InnerProductSpace NNReal ContDiff
open Ballad DoseTravel -- check Lean
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "π'"=>P.wealth 3 (P.advocate 3 x 3)
local notation "η"=>P.enter 3 (P.advocate 3 x 3)
local notation "ε"=>P.seasons 3 (P.advocate 3 x 3)
local notation "E"=> (P.seasons 3 (P.advocate 3 x 3)).E
local notation "Ω"=>P.heaven 3 (P.advocate 3 x 3)
local notation "Γ"=>P.cartage 3 (P.advocate 3 x 3)
local notation "ℜ"=> Lead.Clan 
variable (w:ℜ→Prism)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (D:P.Concert x)
local notation "X'"=> P.headliner x D w

local notation "Ω'"=>P.occupant x

variable (A:ℕ→P.Apron)(Y:ℜ→Spool (P.ManyF 3 (P.advocate 3 x 3)))
local notation "λ₁"=>P.flare1 x Y
local notation "λ₂"=>P.flare2 x Y
local notation "V₁"=>P.leaderW x w D
local notation "V₂"=>P.laterW x w D
local notation "S'"=>P.scoreW x Y
variable {P x Y w V D A}(r:Played P x w V D A Y)
variable {F U:SampleDose} {l u q t μ:ℝ}

-- index sold consultations i,t
variable {c s n:ℕ→ℕ}{X:P.HandleWith x c s A n}

variable {g k:ℕ}(J:P.Ellis 3 x)(B:P.ThinArmada x A c s n w X V g k)
variable (e:Agenda μ F U l u q t)
include e
lemma Agenda.pose {b:ℝ}(h:0<b): Agenda (b*μ) (puffup F h) (puffup U h)
   (b*l) (b*u) (b*q) (b*t):=
 ⟨mul_pos h e.cash,pu_sites₁ h e.ago,pu_sites₂ h e.soon,
    mul_nonpos_of_nonneg_of_nonpos h.le e.L,mul_nonneg h.le e.R,
    mul_lt_mul_of_pos_left e.sep h,pu_strict h e.strict,pu_strict h e.widen⟩
include B J in
lemma Agenda.paid : P.AuthorizedPair x A c s n w V X μ F U:=
 P.authorizePair x A c s n w V _ _ X B J μ F U e.cash e.ago e.soon


lemma lone_harbors(a:ℜ): Harbor (λ₁ F l u a) ∧ Harbor (λ₂ U q t a):=
 ⟨solo_harbor _ _ _ _ _ _ (bandp e.strict), solo_harbor _ _ _ _ _ _ (bandp e.widen)⟩
lemma score_harbors (a b:ℜ):Harbor (fun z=>S' F U l u q t z a b):=
    pair_harbor (ε) (Ω') _ _ _ _ _ _ (Y a).dual (Y b) (bandp e.strict) (bandp e.widen) e.sep
include r
lemma spin {b:ℝ}(h:0<b):
 S' F U l u q t (b:ℂ)=P.readPrism x V w (b*μ) (puffup F h) (puffup U h):=by
 rw [←score_value r (e.pose h)]
 ext1 a c; unfold scoreW
 rw [Matrix.of_apply,Matrix.of_apply,puffup_ok,puffup_ok]
 exact pair_reduce _ _ _ _ _ _ _ _ _ _ (bandp e.strict) (bandp e.widen) h



include B J
lemma lone_spin (a:ℜ){b:ℝ}(h:0<b):
 λ₁ F l u a (b:ℂ)=0 ∧ λ₂ U q t a (b:ℂ)=0:= by
 have A':=e.pose h
 have α:=lone_value r A' a (A'.paid J B)
 unfold flare1 flare2 at *
 rw [puffup_ok,puffup_ok] at α
 rw [solo_reduce _ _ _ _ _ _ (bandp e.strict) h,solo_reduce _ _ _ _ _ _ (bandp e.widen) h]
 exact α
lemma lone_shell (a:ℜ) (z:ℂ) (p:z∈sheath):
 λ₁ F l u a z=0 ∧ λ₂ U q t a z=0:=
 ⟨(lone_harbors e a).1.beacons (Harbor.const 0)
     (fun _ h=>(lone_spin r J B e a h).1) p,
  (lone_harbors e a).2.beacons (Harbor.const 0)
     (fun _ h=> (lone_spin r J B e a h).2) p⟩

omit e r J B
-- analytic table & iterated release predicate

variable (P A c s n x w)
-- Pair meter at height
abbrev ChartLimit (N: ℕ→ℕ→ CrossRead) (M:CrossRead):Prop:=
   ∃ G':ℕ→ CrossRead,(∀ᶠ i in atTop, Tendsto (N i) atTop (𝓝 (G' i))) ∧
     Tendsto G' atTop (𝓝 M)
-- ∀z in sheath continuous etc
abbrev TableW:=ℂ→CrossRead
abbrev Sea (M:TableW):Prop:= ∀ a b, Harbor (fun z=>M z a b)
-- dynamic functionals, input doses incl at every rescaling; opponent same marks same BILL
abbrev Canvas (P:Spine):= ∀ t:ℕ, P.Test→ₗ[ℂ]ℂ
abbrev trueScan : Canvas P:=fun t=>P.singleState 3 t x
abbrev splitScan : Canvas P:=fun t=>P.thinSplit x t
def scannedW (F U:SampleDose)(W:P.Canvas)(i m:ℕ):CrossRead:=
    P.reportPrism A c s n w F U i m (W m)
/-- M with each entry continued on sheath, by identifying the iterated-limit prices
at every rescaling of the measurement. -/
def Screen (F U:SampleDose)(W:P.Canvas)(M:TableW):Prop:=
    Sea M ∧ ∀(b:ℝ)(h:0<b), ChartLimit (P.scannedW w A c s n (puffup F h) (puffup U h) W)
       (M b)

variable {P x w A c s n}


open Six
variable {W:P.Canvas}{M N:TableW}
local notation "put"=>P.Screen w A c s n F U

/-- Raw Gauge × Matter-only comparison at each resolution,
same program input, factorized and Ward. -/
def IsOpponent (P:Spine)(W:P.Canvas):Prop:=
   ∀ t:ℕ, Factors P.calibration (W t) ∧
      (MatterWard P.calibration (W t) ∨ GaugeWard P.calibration (W t))

lemma split_opposes :IsOpponent P (P.splitScan x):= fun t=>
  ⟨(P.thin_comparator_LocalFieldBounds x t).1.factors,Or.inr (P.thin_comparator_LocalFieldBounds x t).2.2.1⟩

lemma chart_unique {Q}{s t:CrossRead}(g:ChartLimit Q s)(h:ChartLimit Q t):s=t:=by
 obtain ⟨f,G',j⟩:=g
 obtain ⟨l,i,y⟩:=h
 have e:f=ᶠ[atTop] l := (G'.and i).mono fun _ h=>tendsto_nhds_unique h.1 h.2
 exact tendsto_nhds_unique (j.congr' e) y
lemma Screen.identify (g: put W M)(h:put W N):EqOn M N sheath:=by
 intro z p; ext1 a b
 exact (g.1 a b).beacons (h.1 a b)
   (fun s v=>congrArg (fun A':CrossRead=>A' a b) (chart_unique (g.2 _ v) (h.2 _ v))) p

include J B e
lemma Screen.nullify (q':IsOpponent P W): put W 0:=by
 refine ⟨fun a b=>Harbor.const 0,fun b hb=> ⟨fun _=>0,?_,tendsto_const_nhds⟩⟩
 have H:=(e.pose hb).paid J B


 filter_upwards [H.ward] with i d
 exact tendsto_const_nhds.congr' ((eventually_ge_atTop (c (n i))).mono fun t ht=>
     (d t ht (W t) (q' t).1 (q' t).2).2.symm)

include r
lemma Screen.score : put (P.trueScan x) (S' F U l u q t):=by
 refine ⟨score_harbors e,fun b hb=>?_⟩
 rw [spin r e hb]
 have H:=(e.pose hb).paid J B
 exact ⟨_,H.grid,H.width⟩

#print axioms Screen.nullify
#print axioms Screen.score
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
