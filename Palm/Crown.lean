import Palm.Hatch
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Branch
open Pitching Pitching.Focus
variable {J q h D C R0 T S ρ f i}
variable (s:Parcel J q h D C R0 T ht S ρ f k)
variable {delay:ℝ}{P:Prescription R B}(H:Service V U W J q h D C R0 P N0 delay)(t:s.Prepared P delay)
variable (G:Morn K)(Q:Diary)(sk:G.After R)(Lq:ShelfTh G Q R0 D C J q h P N0 delay)
local notation "Yc"=> (hat R.L x i)
local notation "Ar"=> G.armor
local notation "w0"=> ((Actual T ht S f k).toSpine.address i)
local notation "fϕ"=> thinAllot G.Mult R Yc
local notation "fZ"=> (3*dleaf R.L Yc)

open Tune Roots Oath Bake Neon
attribute [-instance] instDecidableEqLex
variable {I:Type}[Fintype I][LinearOrder I]{Aρ qv ε:ℝ}(CA:Καlendar R G.armor qv Aρ G.Mult ε)
local notation "Nc" j:max=> cell m B R.L j
variable (xs:Site (cell m B R.L i)) -- unused
-- ABI
local notation "Mk"=> Mew.Key (LabelΩ I)
local notation "YΩ"=> hat R.L x i
local notation "ηκ" j:max=> (allotΨ R.L (hat R.L x j))
local notation "fi" i:max=> (mesh m R.L i)
local notation "St_" i:max=> (V.L.op (k-1-i) (kint m B R.L i))
variable (Ω:I→Site (cell m B R.L i))(v:Very_Ψ (N:=mesh m R.L i) (B:=B) Ω (s.gram i).p.B)
open scoped Mew
local notation "wrk" j:max=> ((Actual T ht S f k).toSpine.address j).step V
variable (d0 top:ℕ)(Ωs:∀ j:ℕ,I→Site (cell m B R.L j))
variable (Eξ:Mew.Key (LabelΩ I) → RegBudget (cell m B R.L top))(Kϕ:Mew.Key (LabelΩ I) → ForceBudget (cell m B R.L top))

open Swell
-- no Bon assumptions earlier than f=nGuard. At every observer height, cutoff, etc.
variable (SwellDay:Q.fits R)(Hc:1≤h)(hY:Yρ G.coinP G.φ Hπ ≤ Aρ)
include CA
lemma liftsExist (hb:Very_Ψ (N:=mesh m R.L d0) (B:=B) (Ωs d0) (s.gram d0).p.B)
    (yr: ∀ i,d0 ≤ i→ i<top→Ωs (i+1)=Hove.heel (apt m B R.L i) ∘ Ωs i)
    (tB:s.Prepared P delay)(mature:∀ i≥d0,Ready_K R.L (hat R.L x i))(p:d0≤top)(pR:top≤k):
  Very_Ψ (N:=mesh m R.L top) (B:=B) (Ωs top) (s.gram top).p.B:=by
  have he (j:ℕ)(p:d0≤j)(v:j ≤ top): Very_Ψ (N:=mesh m R.L j) (B:=B) (Ωs j) (s.gram j).p.B:=by
    induction j,p using Nat.le_induction with
    | base=>exact hb
    | succ j p ih=>
      have hv0:j< top:=v
      have he:= ih hv0.le
      have hl: (s.gram (j+1)).p.B ≤2*(s.gram j).p.B:=by
        rw [gramBound ht k s tB (j+1) (v.trans pR),gramBound ht k s tB j (hv0.le.trans pR),heroΘ]
        exact (mature j p).cost _ le_rfl
      rw [yr _ p hv0]; exact balm_k R.L _ he hl rfl R.odd_side CA.side
  exact he top p le_rfl

include SwellDay Hc hY H sk Lq
/- Rail++ standalone at some x for Shelf. In particular threshold on d0 independent of
history length, m, origins & number of labels. -/
set_option maxHeartbeats 500000 in
theorem palmCrown : ∀ᶠ d0:ℕ in atTop,∀ top≥d0,∀ k≥ top,∀ (m:Side) -- B fixed by Grasp, don't vary Bk. Month T handles
  (ht':T.q ≤ m.val)(S:Cape m B R.L)(ρ f:ℕ→ℝ)(s:Parcel J q h D C R0 T ht' S ρ f k), s.Prepared P delay →
    ∀ {I:Type} [Fintype I][LinearOrder I](oS:∀ j:ℕ,I→ Site (cell m B R.L j)), Very_Ψ (N:=mesh m R.L d0) (B:=B) (oS d0) (s.gram d0).p.B → (∀ i,d0 ≤ i → i<top → oS (i+1)=Hove.heel (apt m B R.L i) ∘ oS i) →
    ∃ E Kz Cz, ClockRec (qv:=qv) (Aρ:=Aρ) ht' k s G d0 top oS (dry_C (shootX (fun i:LabelΩ I=> seedsY (P:=(s.gram top).p) (cue_Φ (allotΨ R.L (hat R.L x top)) h (tiν i)) (xΞ (oS top) i)))) 0 E Kz Cz:=by
 obtain ⟨d,E0⟩:= eventually_atTop.mp (largeEligible V G Q SwellDay CA x |>.and ((stage_slope V x).eventually (Oath.progP 2 6 100)))
 filter_upwards [eventually_ge_atTop (max 1 d)] with i t top hi k hk m hT Sy ρ F hA hT' I _ _ oS ct cv
 have pf(i':ℕ)(p:i ≤ i'):= E0 i' ((le_max_right ..).trans (t.trans p))
 let u:=pf top hi
 let hl:=liftsExist hT k hA G CA i top oS ct cv hT' (fun j v=> (pf j v).1.1) hi hk
 let hf:= plantTop hT k hA hT' G CA top oS hk ((le_max_left ..).trans (t.trans hi)) Hc hl ⟨u.1.1,u.1.2.day.1.trans_le u.1.2.day.2.1,u.2⟩ hY -- #check
 exact threadClock hT k hA H hT' G Q sk Lq CA i top oS _ 0 hf hk hi ct cv (fun j v=> (pf j v).1) Hc
#check liftsExist
#check plantTop
end Parcel
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Parcel.palmCrown
