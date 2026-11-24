import Palm.SnowDrift
import Palm.Crown
import Palm.Delivery
import Palm.Fabric
import Thin.Rail
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
variable (Ω:I→Site (cell m B R.L i)) (v:Very_Ψ (N:=mesh m R.L i) (B:=B) Ω (s.gram i).p.B)
open scoped Mew
local notation "wrk" j:max=> ((Actual T ht S f k).toSpine.address j).step V
variable (d0 top:ℕ)(Ωs:∀ j:ℕ,I→Site (cell m B R.L j))
variable (Eξ:Mew.Key (LabelΩ I) → RegBudget (cell m B R.L top)) (Kϕ:Mew.Key (LabelΩ I) → ForceBudget (cell m B R.L top))
open Buffered Buffered.Advance
open Oise Larch Mew Rive
variable (E1:∀ j:ℕ,Mew.Key (LabelΩ I)→ RegBudget (cell m B R.L j)) (A1:∀ j:ℕ,Mew.Key (LabelΩ I)→ ForceBudget (cell m B R.L j)) (C1:ℕ→ LabelΩ I→LabelΩ I→ℂ)
local notation "Xκ" j:max=> s.gram j
-- tree spelling
variable (off:LabelΩ I→ℂ)
variable (mZ:ℕ)(lA: Stencil.LaurentRadius K.j R.L mZ)(ev:1≤h)
variable (Hr:ClockRec (qv:=qv) (Aρ:=Aρ) ht k s G d0 top Ωs Eξ Kϕ E1 A1 C1)
local notation "ID"=> LabelΩ I
open Swell
variable (Fs:(j:ℕ)→Mark (cell m B R.L j))
-- law iterated all normalized tips. terminal offset f_top from any start b.
include Hr t H sk Lq ev lA CA
set_option maxHeartbeats 800000 in
lemma cook (h0:d0 ≤ i)(v:i+1 ≤ top)(l:top ≤ k)(F0:ID→ℂ)
    (hY:Function.Injective (Cube.node ∘ Ωs i)):
    ∃ F1:ID→ℂ,∀ F:Mark (cell m B R.L i),∀ Z':Support (More (cell m B R.L i)), AtSupport false Z' F → ∀ t:List ID,Roots.ψS tiβ t →
      testerZ ht k s E1 A1 F0 i F t=Roots.snow tiβ (C1 i) (testerZ ht k s E1 A1 F1 (i+1) (postTh ht k s i F)) t:=by
 obtain ⟨F,hf⟩:=consultStep ht k s H t G Q sk Lq d0 top Ωs Eξ Kϕ E1 A1 C1 mZ lA ev Hr h0 v l F0 -- check order
 exact ⟨F,fun f' z hf' l' lH=> (hf l' (psiA _ hY _ lH) f' z hf').trans (white _ hY ..)⟩
include Fs
lemma consultTower (l:top ≤ k)(hv:d0≤top)(F0:ID→ℂ)
    (hY:∀ i,d0 ≤ i→ i<top → Function.Injective (Cube.node ∘ Ωs i)) (hZ:∀ i,d0 ≤ i→ i<top → ∃ Z':Support (More (cell m B R.L i)), AtSupport false Z' (Fs i))
    (hF:∀ i,d0 ≤ i→ i<top → Fs (i+1)=postTh ht k s i (Fs i)):
    ∃ F1:ID→ℂ,∀ t:List ID,Roots.ψS tiβ t →
      testerZ ht k s E1 A1 F0 d0 (Fs d0) t= drift top C1 (testerZ ht k s E1 A1 F1 top (Fs top)) (top-d0) t:=by
 suffices H:∀ a,d0+a ≤ top → ∀ F0:ID→ℂ, ∃ F1:ID→ℂ,∀ t:List ID,Roots.ψS tiβ t →
      testerZ ht k s E1 A1 F0 (top-a) (Fs (top-a)) t= drift top C1 (testerZ ht k s E1 A1 F1 top (Fs top)) a t by
    have lz:= H (top-d0) (by omega) F0; rwa [(show top-(top-d0)=d0 by omega)] at lz
 intro a; induction a
 case zero=> exact fun v F=> ⟨F,fun t _=>rfl⟩
 case succ a ih=>
    intro u Ef
    let i:= top-(a+1); have h:d0≤ i:=by unfold i; omega
    have hu:i+1 ≤ top:=by unfold i; omega
    obtain ⟨Z',z⟩:=hZ i h hu
    obtain ⟨F',hf⟩:=cook ht k s H t G Q sk Lq CA d0 top Ωs Eξ Kϕ E1 A1 C1 mZ lA ev Hr h hu l Ef (hY i h hu)
    obtain ⟨F1,hF1⟩:= ih (by omega) F'
    refine ⟨F1,fun l' p=>?_⟩
    show testerZ ht k s E1 A1 Ef i _ _ =_
    rw [hf _ Z' z _ p,←hF _ h hu, drift]; exact Roots.rer tiβ (C1 i) _ (fun L r=> (by
      rw [(show top-a=i+1 by unfold i; omega)] at hF1
      exact hF1 L (by unfold ψS; rw [r]; exact p)))
set_option linter.unusedVariables false in
lemma driftClockBound (l:List ID)(t':List ID→ℂ)(n v':ℕ)(p:d0≤top-n)(h:n≤top)(hv:0<qv)
    (Q0:ℝ)(u:0≤ Q0)(hg:∀ t,t.map tiβ=l.map tiβ→‖t' t‖≤Q0)
    (hY:∀ i,d0 ≤ i→i<top → Function.Injective (Cube.node∘ Ωs i)):
    ‖drift top C1 t' n l‖ ≤ (((Fintype.card Ξθ:ℝ)*pass_C R.L qv)^l.length)^n*Q0:=by
 have hb:= pay_g R.L qv hv
 exact driftCost top C1 t' l n _ _ (mul_nonneg (Nat.cast_nonneg _) (by linarith [hb.2])) u hg (fun i x w t=>
    broad t (Ωs i) (hY _ (p.trans x) w) (C1 i) _ (Hr.spin i (p.trans x) w).2.1) h
#check consultStep
end Parcel
end YM.CF.Py.Rate
