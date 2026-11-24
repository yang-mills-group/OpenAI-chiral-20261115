import YM.SU5.Reconstruction.Quanta.Magneto
import YM.SU5.FiniteGaugeData.Marked.Journey.Grants

/-! # Genuine detector enrollment at whichever height -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine think)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : Vestal m B L) (R : Cape m B L) (q : Chi) (d : ℝ)
variable (n : ℕ) (Q : ℕ → Haro.SpaceM)
variable (A : Steps m B L) {D J w U : ℕ} (v : Stencil.LaurentRadius j L D) (L' : 3 ≤ L.val) (T : Granted P X R q d n Q A J)
variable (t : ∀ k<n,LoomLaw (R k) w) (p : Margin L D w J U)
local notation "Ω" i:max=> cell m B L i
local notation "ρ" i=> denZ (X i) P (R i)
local notation :max "out_" i:max=>nextMark (ho:=ho) (j:=j) X R q d Q A i
variable {g₀ : Bool}
include T v P
lemma poly_num {k : ℕ} {f : Mark (cell m B L k)} (h : AtSupport g₀ univ f) (u : k<n) : markedRead f (R k) (denZ (X k) P (R k)) = markedRead ((out_ k) f) (R (k+1)) (denZ (X (k+1)) P (R (k+1))) := by
  obtain ⟨g⟩:= T.grant k u
  exact identity_step _ g _ (T.branch k u) (T.aligned k u) (Q k) ho v h (((measurePreserving_fst (μ:=prior group (More (cell m B L k))) (ν:=depot (cell m B L k))).quasiMeasurePreserving.ae ((T.noTies k u.le) _)).mono fun x h=> T.wears _ u x h)
include L' t p
lemma soot_pole (a:Axis){i:ℕ} (h:i<n)(s:ℤ){f:Mark (Ω i)}(u:AtSupport g₀ (band (Ω i) a s U) f):
    AtSupport g₀ (band (Ω (i+1)) a ((L.val:ℤ)*s) U) ((out_ i) f) ∧
    markedRead (reflMark a s f*f) (R i) (ρ i) = markedRead (reflMark a ((L.val:ℤ)*s) ((out_ i) f)*(out_ i) f) (R (i+1)) (ρ (i+1)):=by
  obtain ⟨g⟩:= T.grant i h; obtain ⟨V,b,c,Y,l⟩:= g.cap
  let K:= apt m B L i
  have we:= T.branch i h
  have vt:= surround K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y.bill we g.legal.1 g.legal.2 _ u (t _ h) (T.aligned i h)
  rw [T.radius i h] at vt
  refine ⟨vt.mono (margin_band a _ p K rfl L'),?_⟩
  have hz:= separated_mult K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y.bill we g.legal.1 g.legal.2 _ _ (u.refl a s) u (t _ h) (fun x px y py=> margin_separate a s p x y px py)
  have hs:= rising K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) a s (T.aligned i h) u we Y (g.power.symm ▸ v) g.legal.1 g.legal.2
  rw [poly_num P X R q d n Q A v T (((u.refl a s).mono (subset_univ _)).mulM (u.mono (subset_univ _))) h]; unfold nextMark; rw [hz,hs]; rfl

variable (Z:Buffered.Donor P X R n)
include Z
local notation "ζ" z:max=> gaugeShift B z
lemma polar_onward (a:Axis) (i:ℕ)(h:i≤ n)(z:ℤ)(f:Mark (Ω i))(w_:AtSupport g₀ (band (Ω i) a (ζ z) U) f):
    0 ≤ markedRead (chord g₀ • (reflMark a (ζ z) f*f)) (R i) (ρ i) := by
  let E(i:ℕ):= ∀ z:ℤ,∀ f:Mark (Ω i),AtSupport g₀ (band (Ω i) a (ζ z) U) f → 0 ≤ markedRead (chord g₀ • (reflMark a (ζ z) f*f)) (R i) (ρ i)
  have he: E n:=by
    intro s f u; obtain ⟨X',Y,w,h,V⟩:= Z.grants; obtain ⟨x,y,t,s',A_⟩:=Z.roof
    exact strata_gram P _ _ Z.pin Z.scroll _ _ Z.top h V s' A_ (T.noTies n le_rfl) a s _ (u.mono (band_anti a (ζ s) (Nat.zero_le _))) Z.warm
  have ht(i:ℕ)(h:i<n)(e:E (i+1)):E i:=by
    intro s f u; obtain ⟨r,h'⟩:= soot_pole P X R q d n Q A v L' T t p a h (ζ s) u
    rw [show (L.val:ℤ)*(ζ s)=gaugeShift B (L.val*s:ℤ) from by unfold gaugeShift; ring] at r h'
    have fz:=e (L.val*s) _ r; rw [mark_smul,h']; rwa [mark_smul] at fz
  have H(k:ℕ)(h:k≤n):E (n-k):=by
    induction k with | zero=>simpa using he | succ k ih=> exact ht (n-(k+1)) (by omega) ((show n-k=n-(k+1)+1 by omega) ▸ ih (by omega))
  exact (show E i from (show n-(n-i)=i by omega) ▸ H (n-i) (Nat.sub_le ..)) z f w_

end YM.CF.Buffered.Afterglow.Journey

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexOrder
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet Chaff Gloss Maize Tye RP RP.Str Oise
open Py Py.Rate Py.Rate.LocalLimit
open Preparation Advance Heat
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(i k:ℕ)(p:(Y.voyage i).kick ≤ k)
local notation "V"=>Y.voyage i
local notation "P"=>(Y.voyage i).X (Y.uv k)
local notation "Q"=> (Y.voyage i).Q k p
local notation "n"=> Y.uv k
local notation "T"=>Y.meter
local notation "α"=>Λ.U
local notation "L"=> Λ.R.L
local notation "B"=> Λ.block
local notation "Ms"=> Y.ir i
local notation "Ω" j:max=> Λ.Ctor (Y.ir i) j

include p
open Reflect
lemma lamp_poles {g₀: Bool} (J:ℕ)(hj:J ≤ n)(a:Axis)(z:ℤ)(f:Buffered.Mark (Ω J))(h:AtSupport g₀ (band (Ω J) a (gaugeShift B z) (reserve Λ l)) f):
    0 ≤ markedRead (chord g₀ • (reflMark a (gaugeShift B z) f*f)) ((V).CapeT J) (denZ ((Q).gram J) Λ.U ((V).CapeT J)) :=
  let s:= fullness Y i k p
  polar_onward _ _ _ _ _ _ _ _ (legal Λ) Λ.R.coarse s.warm_grant (fun k _=> tissue Y i k) (prepared Λ l) s.heat.choose a J hj z f h
end YM.CF.Buffered.Afterglow.Journey

#print axioms YM.CF.Buffered.Afterglow.Journey.lamp_poles
