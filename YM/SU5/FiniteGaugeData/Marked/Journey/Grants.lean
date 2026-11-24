import YM.SU5.FiniteGaugeData.Marked.Journey.Every
import YM.SU5.FiniteGaugeData.SameHistory1102

/-!
# Direct route on the FiniteGaugeData course. Access actual reflection data of the heat partner
(with the stored F0 and pinpoint and full gauge--CAR transfer; no replacement
of the partner Loom or Gram).
-/
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

theorem fullness: Shots Λ.V (Y.meter) Λ.J Chi.canonical (V).funds ((V).CapeT) (Y.uv k) ((P).gram) ((Q).gram) ((P).wave) ((Q).wave) ((P).pilot) ((P).fee) ((Q).tilt) Λ.h Λ.R0 Λ.δ:= by
  have ht:(Q).gram (Y.uv k)= fulvia (Q).top (Q).offset (Vale.launch Λ.V.L ((Q).gram (Y.uv k)).beta ((T).a (Y.uv k)) (Ω (Y.uv k))):= (Q).pull.boot.trans (by rw [hue_top]; rfl)
  refine ⟨Y.history i k,(Q).pull.owns,(Q).pull.wear,(Q).pull.sift,(Q).pull.shift,(Q).pull.color.trans ((Q).due.unit),fun j hj=>⟨_,_,((Q).pull.note j hj).lot⟩,⟨_,_,ht⟩,?_⟩
  have hT:Heat.Eyes Λ.U ((Q).gram (Y.uv k)) ((V).CapeT (Y.uv k)) (originalPinning _ _) (Λ.F0 _) Λ.K.top.clip ((radiusB (hat L Λ.x (Y.uv k))):ℝ) := by
    intro X h A
    rw [heat_db]
    let s:= ((V).CapeT (Y.uv k))
    have v': ((Q).gram (Y.uv k)).p = (T).a (Y.uv k):= ((Q).pull.owns _ le_rfl).width.symm
    rw [v'] at h ⊢
    refine (show inner ℂ _ _ = _ from ?_).trans ((Q).lives.eyes _ X h A)
    -- by rewrite top form
    exact congrArg (fun f=> inner ℂ (Dial.mateK (Ω (Y.uv k))) (acts A (denZ f Λ.U s X))) ht
  let D: Buffered.Donor Λ.U (Q).gram ((V).CapeT) (Y.uv k) := {
    pin:=originalPinning _ _,scroll:=Λ.F0 _,clip:=Λ.K.top.clip,
    heat:= (radiusB (hat L Λ.x (Y.uv k)):ℕ), warm:=by exact_mod_cast (Nat.zero_le _), grants:=⟨_,_,_,Λ.scale _,Λ.budget⟩
    top:=hT
    roof:=⟨_,_,_,((V).ownership _).paid,by rw [show ((Q).gram (Y.uv k)).p=(T).a (Y.uv k) from ((Q).pull.owns _ le_rfl).width.symm]; exact (Q).pole _⟩ }
  exact ⟨D,rfl,rfl⟩


-- public purchase prices for lemma `onward`
open YM.SU5.FiniteGaugeData.Audit1102
abbrev distanceLaw (l:ℕ):= lawRadius (VolumeCape.Dream.plot l).C
abbrev aliasLaw(Λ:Preparation):= (Aliases.finite_brix Λ.K.j Λ.R.L Λ.R.odd_side).choose
lemma legal (Λ:Preparation): Stencil.LaurentRadius Λ.K.j Λ.R.L (aliasLaw Λ) := (Aliases.finite_brix Λ.K.j Λ.R.L Λ.R.odd_side).choose_spec
abbrev reserve (Λ:Preparation)(l:ℕ):ℕ:=4*r₃ Λ.R.L (aliasLaw Λ) (distanceLaw l) Λ.R.J+1
lemma prepared (Λ:Preparation)(l:ℕ): Margin Λ.R.L (aliasLaw Λ) (distanceLaw l) Λ.R.J (reserve Λ l):=Nat.lt_succ_self _
lemma tissue (J:ℕ):LoomLaw ((V).CapeT J) (distanceLaw l):=by
  apply nimbusLaw l _ ((V).craft J)
  intro x; exact ((V).ownership J).paid.bill.comp (measurable_const.prodMk measurable_id)
include p
lemma throbbing (J:ℕ)(hj:J ≤ n)(a:Axis)(z:ℤ)(f:Buffered.Mark (Ω J))(h:AtSupport false (band (Ω J) a (gaugeShift B z) (reserve Λ l)) f):
    0 ≤ markedRead (reflMark a (gaugeShift B z) f*f) ((V).CapeT J) (denZ ((Q).gram J) Λ.U ((V).CapeT J)) :=
  let s:= fullness Y i k p
  onward _ _ _ _ _ _ _ _ (legal Λ) Λ.R.coarse s.warm_grant (fun k _=> tissue Y i k) (prepared Λ l) s.heat.choose a J hj z f h
end YM.CF.Buffered.Afterglow.Journey
