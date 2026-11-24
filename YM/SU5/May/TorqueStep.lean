import YM.SU5.Reconstruction.Intermediate.Climate
/-! # Torque. Earlier-than-buoy high tilt estimator. Adapt MeasureLane, Climate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit

open Branch
open Preparation
namespace Harbour
open FullBill Marks Intermediate Donor
variable {Λ: Preparation} {Φ : (s:Side)→Scree.Loom s→ Prop} (Y:Course Λ Φ) (i k:ℕ)
local notation "G" => Y.voyage i
local notation "L" => Λ.R.L
local notation "B" => Λ.block
local notation "℘" => (G).CapeT
local notation "D" => Λ.δ
local notation "s₀" => Y.uv k
local notation "ν" => Y.ivory k
local notation "u" => buoy ν
local notation "N" => Λ.N0
local notation "m" => Y.ir i
local notation "M" s:max=> cell (m) B L s
local notation "𝔸" => projectA Y i k
local notation "𝐴" => (Y.voyage i).X (Y.uv k)
variable (s:ℕ) (F:Intermediate.Room s→ Corr (Λ.Ctor (Y.ir i) s))(t:Intermediate.Room s)
local notation "X" j:max => (screen Y i k s F t) j
-- schedule depends on TRUE period only; use as high borrower on the vote k. It's gigantic in general,
-- but polynomial in period so per-step fees can possibly be restored exponentially in period-power
noncomputable def warning : ℕ := (Y.ir i).val^2
abbrev turnUp : ℕ:= buoy (warning Y i)
local notation "σ₀" j:max => divisionBill (Y.meter) Λ.C Y.τ j (warning Y i) (m)
noncomputable def EnoughEarly (j:ℕ): Prop := Priced Λ.V (screen Y i k s F t j) Λ.U ((G).CapeT j) (thermalCost Λ.C Λ.R Λ.x Y.τ j) (thermalCost Λ.C Λ.R Λ.x Y.τ j + |serviceCost Y.meter j|) ∧ ∀ y,‖ratioField Λ.V ((𝐴).gram j) ((G).CapeT j) Λ.U y - ratioField Λ.V (X j) ((G).CapeT j) Λ.U y‖ ≤ σ₀ j
set_option maxHeartbeats 600000
variable {i k s F t} (e:s ≤ Y.uv k) (pF:campus Y i k s F)
include e pF in
lemma highPay (g:(Y.voyage i).kick ≤ k) (r:phaseMoney Y i k s F t) (hY:buoy (warning Y i) ≤ s) {j:ℕ} (v:j< buoy (warning Y i))(pZ:
 outage Y.meter j (warning Y i) (Y.ir i) ≤ Real.exp (-expense Λ.C Λ.R Λ.x Y.τ j*sites (cell (Y.ir i) Λ.block Λ.R.L j))/2) : EnoughEarly Y i k s F t j:= by
 obtain ⟨b,p,q,w⟩:= ((Y.voyage i).paths (Y.uv k)).issued
 have hs:= Y.each_level i k j g ((v.le.trans hY).trans e)
 rw [q] at hs; unfold EnoughEarly; rw [q]
 exact price_of Λ.P 𝔸 s F t Λ.H Λ.response (money Y i k) Λ.height e pF r b p (warning Y i) hY j v hs pZ
open Buffered
lemma paid_here (g:(Y.voyage i).kick ≤ k){j:ℕ}(p:j ≤ Y.uv k) (h:EnoughEarly Y i k s F t j)
    (w:Mark (Λ.Ctor (Y.ir i) j))(e:RG.Envelope w){c:ℝ}(x₀:∀ y,‖w y‖ ≤ c):
    ‖markedRead w ((G).CapeT j) (denZ ((𝐴).gram j) Λ.U ((G).CapeT j)) / partitionZ ((𝐴).gram j) Λ.U ((G).CapeT j) - consultancy Y (i:=i) (k:=k) (s:=s) (F:=F) t j w‖ ≤ c*σ₀ j := by
 let u' := w ∘ fun x:Orbit (cell (Y.ir i) B L j)=>(x.1,(Y.voyage i).CapeT j x)
 let X':= X j
 change ‖Marks.ratio Λ.V Λ.U ((𝐴).gram j) ((G).CapeT j) u'-Marks.ratio Λ.V Λ.U X' ((G).CapeT j) u'‖ ≤ c*σ₀ j
 have hW:Envelope u':= ⟨e.meas.comp (measurable_fst.prodMk ((Y.voyage i).ownership j).paid.bill),_,fun i=>(x₀ _)⟩
 rw [Marks.normalized,Marks.normalized]; exact Marks.read_charge _ (Marks.can_evaluate _ _ _ _ (Y.each_level i k j g p)) hW (Marks.can_evaluate _ _ _ _ h.1) (fun i=> x₀ _) h.2
lemma lura : Tendsto (fun i=> warning Y i) atTop atTop:= (tendsto_pow_atTop (by decide:(2:ℕ)≠0)).comp Y.ir_grows.tendsto_atTop
lemma turn_cone (i:ℕ) : cone Λ.b (warning Y i) (Y.ir i):=by
 let x:=(Y.ir i).val
 unfold cone trunk warning
 change x^5≤(x^2)^4+x^2+1+_
 have h:x^5≤x^(2*4):= pow_le_pow_right₀ (by exact (Y.ir i).property) (by norm_num)
 rw [pow_mul] at h; omega
lemma securities (j:ℕ)(c:ℝ)(p:0<c): ∀ᶠ i:ℕ in atTop,j < turnUp Y i ∧
 divisionBill (Y.meter) Λ.C Y.τ j (warning Y i) (Y.ir i) ≤ c ∧ ∀ k:ℕ,(Y.voyage i).kick ≤ k →∀ s:ℕ,s≤Y.uv k→ turnUp Y i ≤ s → ∀ F:(Intermediate.Room s)→ Corr (Λ.Ctor (Y.ir i) s), campus Y i k s F → ∀ t:Intermediate.Room s, phaseMoney Y i k s F t → EnoughEarly Y i k s F t j:= by
 filter_upwards [(lura Y).eventually (Intermediate.half_room (T:=Y.meter) (C:=Λ.C) (τ:=Y.τ) j Λ.b), (lura Y).eventually (profound j), (lura Y).eventually (shrinks (T:=Y.meter) (C:=Λ.C) (τ:=Y.τ) j Λ.b p)] with i h w z
 exact ⟨w,z _ (turn_cone Y i),fun _ g _ hs hy _ pq _ he=>highPay Y hs pq g he hy w (h _ (turn_cone Y i))⟩
#print axioms securities
end Harbour
end LocalLimit
end YM.CF.Py.Rate
