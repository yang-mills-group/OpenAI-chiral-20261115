import Gingham.Pommel
import SU5SatinFieldRegistrationsNovember7

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

open SatinRegistration YM.Velour SatinJets
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open _root_.YM.SatinEdge.RealSheet Boundary Probe
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "κ"=> Lead.Clan
variable (K : P.Register) (c r : ℕ→ℕ) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
    (A : ℕ→P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4→L[ℂ] (P.ManyF 3 (P.advocate 3 x 3))) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4)
local notation "Μ" => M4Tuple P K c r x R i₀ F U A n w V g h X Y Z
local notation "Λ" => P.profilesZ x V w
local notation "Jury" => Garrison P x c r A n
local notation "W" => P.soldTrumpet A c r n w
local notation "G₀" => P.gaugeTrumpet A c r n w

variable (yr: M4Tuple P K c r x R i₀ F U A n w V g h X Y Z)
         (u:Garrison P x c r A n)
abbrev Serves:= ∀ a:κ,P.CapReady x (G₀ a)
variable (p:P.CapBacked x A c r n w)(q:Serves P x c r A n w)

include yr
/-- A raw obstruction **directly** to the sold stamp paying a
pure matter bill: at each native stage it must literally have
both interactions available in its function; the prescription
does not make it a matter marginal paper. Same for pure gauge. -/
theorem lacks_matter :
   ∀ᶠ i in atTop, ∀a:Lead.Clan, ¬PureMatter P.calibration (W a i).F
          ∧ ¬PureGauge P.calibration (W a i).F :=by
   refine (P.verified_mixtures x A c r n w V g h X F U yr.lab).mono fun i j a=>?_
   have u:= (j _ le_rfl a).2
   exact ⟨fun t=>u (Or.inr (requestNative P _ _ rfl t U)),fun t=>u (Or.inl (P.prepare_pure _ _ t U))⟩

omit yr

section
variable (L:ℕ→P.Apron)(t:P.CapReady x L)
abbrev standard :Hook P x := ⟨Swatch.ordinary L,P.affine_cap x L t⟩
include t
lemma reflects :
    (standard P x L t).west P x =
       standard P x (fun i=>(L i).kiss P 3) (P.cap_partner x L t) :=by
   have e: (Swatch.ordinary L).turn 3 =
       Swatch.ordinary (fun i=>(L i).kiss P 3):=by
        unfold Swatch.turn Swatch.ordinary;dsimp; simp
   apply (show ∀a b:Hook P x,a.arms=b.arms→ a=b from ?_) _ _ e
   rintro ⟨a,t⟩ ⟨b,k⟩ h; dsimp only at h; cases h;rfl

lemma paid :
     toll P x (standard P x L t)=P.managed x L t:=
  P.affine_heat x L t

lemma onface :
     face8 P x (standard P x L t) =P.pointField x L t :=
   P.affine_field x L t
omit t
end

include yr p q u
local notation "Hⱼ" a:max=> standard P x (W a) (p a)
local notation "Hₐ" a:max=> standard P x (G₀ a) (q a)

lemma unison (a:κ):
    toll P x (Hₐ a)= toll P x (Hⱼ a):=by
  rw[paid,paid]
  exact P.same_trumpets x c r n A a (P.paidThin x K c r R i₀ F U A n w V g h X Y Z yr a)
     X (P.height_covered x K c r R i₀ F U A n w V g h X Y Z yr)
     w u.printed (.funded P x A u.aircraft) (q a) (p a)

lemma answerwise (a:κ):
    pelisse P x (Hₐ a)=pelisse P x (Hⱼ a) ∧
    pelisse P x ((Hₐ a).west P x)=pelisse P x ((Hⱼ a).west P x):=by
  have w':=unison P x K c r R i₀ F U A n w V g h X Y Z yr u p q a
  refine ⟨(collects P x _).common (collects P x _)
       (Eventually.of_forall (congrFun w')),
     (collects P x _).common (collects P x _) (Eventually.of_forall ?_)⟩
  intro d
  exact ((toll_adj P x _ d).symm.trans (congrArg star (congrFun w' d))).trans
       (toll_adj P x _ d)

omit q p u
lemma profile_one (a:κ) {t:ℝ} (ht:0<t):inner ℂ ω₁ (Λ a t)=0:=by


  have h:(𝓢).orth (Λ a t)=0:= ((yr.lab.armada.energy a).2.2 t ht).2.1
  have v:= (𝓢).emerges (Λ a t)
  rw [h] at v
  have y:= (tendsto_const_nhds (x:=ω₁ )).inner (𝕜:=ℂ) v
  simp_rw [←ContinuousLinearMap.adjoint_inner_left,(𝓢).sym, P.heaven_hot,
     inner_zero_right] at y
  exact tendsto_nhds_unique tendsto_const_nhds y

include p
lemma profile_skin (a:κ)(t:ℝ≥0)(d:0<t):
    jut ω₁ (toll P x (Hⱼ a) t) = Λ a t:=by
   rw [jut,shred,paid]
   have he:P.managed x (W a) (p a) t ω₁=Λ a t:=
       P.limit_profile_paid x A c r n w V X F U yr.lab p a t d
   rw[he,profile_one P x K c r R i₀ F U A n w V g h X Y Z yr a
            (show 0<(t:ℝ) from d), zero_smul,sub_zero]


lemma prism_time (a b:κ) (z:Vantage)(d:0<z 3/2):
   let t:=Real.toNNReal (z 3/2)
   inner ℂ (jut ω₁ (toll P x (Hⱼ a) t))
      (P.cartage 3 ξ z (jut ω₁ (toll P x (Hⱼ b) t))) =
      P.pointPrism x V w z a b:=by
   have he:=Real.toNNReal_pos.mpr d
   have ha:=Real.coe_toNNReal _ d.le
   dsimp only
   rw [profile_skin P x K c r R i₀ F U A n w V g h X Y Z yr p a _ he,
       profile_skin P x K c r R i₀ F U A n w V g h X Y Z yr p b _ he,ha]
   rfl


omit yr
lemma soldface (a:κ):
   face8 P x (Hⱼ a)= P.registeredField x A c r n w p (positiveLabel a) ∧
   face8 P x ((Hⱼ a).west P x)= P.registeredField x A c r n w p (negativeLabel a):=by
   constructor
   · exact onface P x (W a) (p a)
   rw [reflects,onface]
   rfl

-- same Y, Z
variable (t:P.OverM4 x c r F U A n w V Y Z p)

include t
lemma Y_actual (a:κ)(f:Test4):
    (pelisse P x (Hⱼ a) f Ω).val= Y a f:=by
   refine (pelisse_on_both P x _ _ _ (P.vacuumEntry x) rfl).trans ?_
   rw [(soldface P x c r A n w p a).1,t.actualField]


include yr u q
lemma Z_actual (a b:κ)(f z:Test4):
    Z a b (tieAt f z)=rcoupled 𝓢 Ω
       (pelisse P x ((Hₐ a).west P x) (bar f))
       (pelisse P x (Hⱼ b) z):=by
   rw [(answerwise P x K c r R i₀ F U A n w V g h X Y Z yr u p q a).2, t.actualDistribution]
   have b':=pelisse_on_both P x (Hⱼ b) z Ω (P.vacuumEntry x) rfl
   rw [(soldface P x c r A n w p b).1] at b'
   have a':=pelisse_on_both P x ((Hⱼ a).west P x) (bar f) _ _ b'
   rw [(soldface P x c r A n w p a).2] at a'
   exact congrArg (inner ℂ ω₁) a'.symm
omit t yr u q p

#print axioms unison
#print axioms answerwise
#print axioms Z_actual

local notation "G♯" => fun a=>Hₐ a
local notation "W♯" => fun a=>Hⱼ a

include yr p q u
lemma annulus : ∃ (y:Vantage) (t:ℝ≥0),
    (∀j, y j≠0) ∧ 0<t ∧
      ProofRank (Knife P x (G♯) (W♯) y t t)≠0:=by
 obtain ⟨l,le,r',re,_,_,_,e,_⟩:=yr.lab.keeps.centers
 have d (j:Axis):0<(r'-l) j:=by
   have f:=thin_separation l r' le re j
   change 0<r' j-l j
   linarith only [f]
 have he : ProofRank (P.pointPrism x V w (r'-l))≠0:=(rank_iff _).mpr e
 let t:= Real.toNNReal ((r'-l) (3:Axis)/2)
 refine ⟨r'-l,t,fun j=>(d j).ne',Real.toNNReal_pos.mpr (half_pos (d 3)),?_⟩
 have hz:Knife P x (G♯) (W♯) (r'-l) t t=P.pointPrism x V w (r'-l) :=by
   ext1 i j
   rw [Knife,Matrix.of_apply,unison P x K c r R i₀ F U A n w V g h X Y Z yr u p q i]
   exact prism_time P x K c r R i₀ F U A n w V g h X Y Z yr p i j _ (half_pos (d 3))
 exact hz.symm ▸ he
omit yr u p q


local notation "Gw" => fun a=>(Hₐ a).west P x
/-- Restoration on the **same** tuple. Discerns SIX registered charges
even with the same separated (spacelike also) tests in real and ordered Eu
pricing, as measured by the product-of-marginals protocol. Including margin
at prices *before* taking limits. But itself not intrinsic gauge-matter:
right charges detect gauge, pure sector stamp hypothesis unpaid. -/
structure Parent (d:Weave)(ρ:ℝ):Prop where
  preserved: CourtLedger P x (Gw) (W♯) d ρ
  gauge:∀a,clean P x true (Hₐ a)∧clean P x true ((Hₐ a).west P x)
  lacks:∀ᶠ i in atTop,∀a,¬PureMatter P.calibration (W a i).F ∧
                                ¬PureGauge P.calibration (W a i).F
  twins:∀a, toll P x (Hₐ a)=toll P x (Hⱼ a) ∧
    pelisse P x (Hₐ a)=pelisse P x (Hⱼ a) ∧
    pelisse P x ((Hₐ a).west P x)=pelisse P x ((Hⱼ a).west P x)
  recovers:∀(a:κ)(f:Test4), (pelisse P x (Hⱼ a) f Ω).val= Y a f
  speaks:∀(a b:κ)(f z:Test4), Z a b (tieAt f z)=rcoupled 𝓢 Ω
       (pelisse P x ((Hₐ a).west P x) (bar f))
       (pelisse P x (Hⱼ b) z)


#check Parent
#print axioms Parent

include yr u p q t
theorem offshoot : ∃ d ρ, Parent P x c r A n w Y Z p q d ρ:=by
 obtain ⟨y,s,v,e,h₀⟩:= annulus P x K c r R i₀ F U A n w V g h X Y Z yr u p q
 obtain ⟨d,z⟩:= stir P x (G♯) (W♯) y v e e h₀
 obtain ⟨ρ,a⟩:=abreast P x (Gw) (W♯) R z
 refine ⟨d,ρ,force_election P x (Gw) (W♯) d ρ a,
   fun i=>?_,lacks_matter P x K c r R i₀ F U A n w V g h X Y Z yr,
   fun i=>⟨unison P x K c r R i₀ F U A n w V g h X Y Z yr u p q i,
     answerwise P x K c r R i₀ F U A n w V g h X Y Z yr u p q i⟩,
    Y_actual P x c r F U A n w V Y Z p t,
    Z_actual P x K c r R i₀ F U A n w V g h X Y Z yr u p q t⟩
 have v: clean P x true (Hₐ i):= Eventually.of_forall fun k=>
       P.gaugeTrumpet_purity A c r n w i k (yr.work.choose_spec.2.1 k)
 exact ⟨v,luminous P x v⟩
#print axioms offshoot
end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
