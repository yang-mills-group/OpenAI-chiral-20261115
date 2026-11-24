import ZecaChorus
import ZecaVacant
import SU5SatinVerifiedNovember6
set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight

namespace Spine

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



structure Shell (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x) :Prop where
 scores:P.Scores K c r x R i₀ F U A n w V g h X
 silver:P.Silver x A c r n w V D reviewEarlierBox reviewLaterBox 1 F U
 separated:∀p ∈ tsupport ⇑(att F), ∀q ∈ tsupport ⇑(att U),
      q-p∈Mink.spacelike ∧ Mink.m (q-p)< -1

open Preparation.Yoke Yoke.Travel SatinNucleus Six Regis.Head Regis.Head.Brecht
open CF.Velvet CF.Pannier.Chancel

/-- Actual n-point price acquittal in any_quote.
CP18 Wick quotes with unpadded real fields; BOTH Wick and Mink profiles pay, literally same tests. -/
theorem exists_disclosed_satin_fields :
 ∃(P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x), P.Shell K c r x R i₀ F U A n w V g h X D:=by
 let Ω':Supplier:= fun _ _ _ _ _ _ _ _ _ _ _ _=>0
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A₀,a,season,c,r,h,snow,b,β,ρ⟩:=
   elected_thin_cloud (fun _ _ _ _ _ _=> 0) Ω' 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨i,_,s⟩:= ρ.exists
 obtain ⟨x,R,_,t,v,a',V_,u,Q,V,N,d,z,l,T,f⟩:= s (fun _=>True) (Eventually.of_forall (fun _=>True.intro))

 have lab:=(f reviewEarlierBox reviewLaterBox thinEarlier _ zero_lt_one (le_refl _) (le_refl _)).exists
 have ga:= (T lab.choose_spec.choose_spec.choose_spec.choose).cinema

 obtain ⟨i₀,F,U,w,D,J,M⟩:=
    (P.silverware x _ c r N V _ _ d R reviewEarlierBox reviewLaterBox K 1
       (le_refl _) (le_refl _) zero_lt_one l ga T t.setup thinEarlier).exists
 exact ⟨P,K,c,r,x,R,i₀,F,U,_,N,w,V,_,i,d,D,
     P.sing_scores K c r x R i₀ F U _ N w V _ _ d e h t.setup π₀ h0 ⟨_,_,_,_,rfl⟩ T J l,
     M,
     fun _ p _ q=>vacant _ _ (M.earlier (att_s _ p)) (M.laterProbe (att_s _ q))⟩

#print axioms exists_disclosed_satin_fields
#check @exists_disclosed_satin_fields
