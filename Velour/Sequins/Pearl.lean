import Velour.Sequins.Rounds
import Velour.Palace.Tuple
import Velour.Gathers.Day
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe


def gate1 : Doorway where
 lower j:= if j=3 then -5/4 else -2
 upper j:= if j=3 then -1 else -7/4
 clearance j:=by split <;> norm_num
def gate2 : Doorway where
 lower j:= if j=3 then 1 else 7/4
 upper j:= if j=3 then 5/4 else 2
 clearance j:=by split <;> norm_num

private lemma g1: gate1.invites ⊆ reviewEarlierBox.invites:=by
 intro w hw i _
 specialize hw i (mem_univ _)
 change (if i=3 then -5/4 else -2)<w i ∧ w i<(if i=3 then -1 else -7/4) at hw
 change -2<w i ∧ w i< -1
 split_ifs at hw <;> constructor <;> linarith
private lemma g2: gate2.invites ⊆ reviewLaterBox.invites:=by
 intro w hw i _
 specialize hw i (mem_univ _)
 change (if i=3 then 1 else 7/4)<w i ∧ w i<(if i=3 then 5/4 else 2) at hw
 change 1<w i ∧ w i<2
 split_ifs at hw <;> constructor <;> linarith
private lemma tt1 : gate1.Later gate2 thinAlongOrder 0:=by
 intro i
 simp [thinAlongOrder,gate1,gate2]; split <;> norm_num


lemma gap_reward (x y:Vantage) (f:x∈closure gate1.invites)(h:y∈ closure gate2.invites):
   |(y-x) (3:Axis)|≤5/2 ∧ ∀ j:Axis,j≠3→7/2≤ (y-x) j:=by
 rw [Doorway.doorSeal,Doorway.sealing] at f h
 refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩
 · rw [Pi.sub_apply]
   linarith only [show x 3 ≤ -1 from f.2 3,show 1 ≤y 3 from h.1 3]
 · rw [Pi.sub_apply]
   linarith only [show -5/4 ≤ x 3 from f.1 3, show y 3≤5/4 from h.2 3]
 intro j l
 have a:=f.2 j;have b:=h.1 j
 simp only [gate1,gate2,if_neg l] at a b
 rw [Pi.sub_apply]; linarith

lemma spacelike_reward (x y:E4)(f:foldSpace x∈closure gate1.invites)(h:foldSpace y∈ closure gate2.invites):
   y-x ∈ Mink.spacelike:=by
 obtain ⟨u,v⟩:=gap_reward (foldSpace x) (foldSpace y) f h
 have h₁: |time (y-x)|≤5/2:=u
 have h₂:7/2≤ spatial (y-x) 0:=v 0 (by decide)
 have n:7/2≤ ‖spatial (y-x)‖:=h₂.trans ((le_abs_self _).trans (PiLp.norm_apply_le (spatial (y-x)) 0))
 change time (y-x)^2-‖spatial (y-x)‖^2<0
 obtain ⟨l,k⟩:=abs_le.mp h₁
 nlinarith

lemma OnceHere.gate_wide {P:Spine}{x:P.Spectrum0 3}
     {V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
     {p:Lead.Clan→Prism}{s k:ℕ}{F U:SampleDose}{K:P.Register}
     (v:P.OnceHere x V p 1 s k F U K gate1 gate2):
    P.OnceHere x V p 1 s k F U K reviewEarlierBox reviewLaterBox:=by
 obtain ⟨a,f,b,h,u⟩:=v.centers
 exact ⟨v.eps,v.earlier.trans g1,v.laterProbe.trans g2,v.normalized,v.fixed,
    fun i=>⟨(v.all i).1.trans g1,(v.all i).2.trans g2⟩,v.read,a,g1 f,b,g2 h,u⟩


theorem pearlElection :
    ∃ (P:Spine) (K:P.Register) (c r:ℕ→ℕ) (x:P.Spectrum0 3) (R:P.Ellis 3 x)
    (i₀:ℕ)(F U:SampleDose)(A:ℕ→P.Apron)(n:ℕ→ℕ)(w:Lead.Clan→Prism)
    (V:∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j))
    (g h:ℕ)(X:P.HandleWith x c r A n)
    (Y: Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3))
    (Z: Lead.Clan → Lead.Clan → Boundary.Distn E4),
    M4Furnish P K c r x R i₀ F U A n w V g h X Y Z ∧ Sconces P K c r ∧ M4Velvet P x A c r n ∧ TottyCup P x A ∧
    P.FullPrismLab x A c r n w V g h X 1 F U gate1 gate2 (c i₀) (r i₀) K ∧ ReadsSix (paycheck Y F U):= by

 obtain ⟨nu,P,K,e,ro,ni,_,_,_,_,_,_,_,_,_,_,_,_,c,r,adv,y,b,p,m⟩:=
   totty_labs (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨s,_,z⟩:=m.exists
 obtain ⟨x,R,_,t,v,a,o,u,q,V,n,X,cup,tote,pow,hand,fleet,many⟩:=z (fun _=>True) (.of_forall (fun _=>True.intro))


 let g:=P.pointEra s
 let A:=P.cinema x g s v a q u

 have C: (w:Lead.Clan→Prism) → P.ThinArmada x A c r n w X V g s:=fleet
 -- Need one Prism for .cinema. no experiment here on alternative tests: just inhabitation
 have Bp:Nonempty (Lead.Clan→Prism):=by
   obtain ⟨i,f,y,w,hw⟩:=(many gate1 gate2 tt1 1 zero_lt_one (le_refl (-1)) (le_refl 1)).exists; exact ⟨w⟩
 obtain ⟨T⟩:=Bp
 have H(w)(j):=(P.prism_both_edges x A c r n w j V g s X pow (C w)).2
 obtain ⟨i₀,F,U,w,L,real₁⟩:=
    (P.spark_order x g s V 1 (C T).cinema R K gate1 gate2 tt1 (le_refl (-1)) (le_refl 1) t.setup zero_lt_one H).exists

 have labs:= P.honorLab x A c r n w V g s X (C w) R 1 F U gate1 gate2 (c i₀) (r i₀) K tt1 (le_refl (-1)) (le_refl 1) L
 have lab:= P.honorLab x A c r n w V g s X (C w) R 1 F U reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K thinEarlier (le_refl _) (le_refl _) L.gate_wide

 obtain ⟨d,l⟩:= Schedule.very_late (daylight (timeMesh P.par)) (a:=2)
 have he(i):PureGauge P.calibration (A i).F:=P.cinema_pure ..
 have h(z:Lead.Clan):= P.prism_both_edges x A c r n w z V g s X pow lab.armada
 have b:=P.real_order x A c r n w V g s X R F U _ _ K (fun t=> (h t).2) lab
 refine ⟨P,K,c,r,x,R,i₀,F,U,A,n,w,V,g,s,X,_,_,⟨P.terminalBeta K e,
      t.setup,trans6 t.setup,lab.keeps.normalized.1,lab.keeps.normalized.2,lab.keeps.earlier,
      lab.keeps.laterProbe,lab.keeps.fixed.1,lab.keeps.fixed.2,lab,
      ⟨d,P.registerMatched x A c r n w F U X V d g s _ _ K lab l.le,he,
        P.earnsSplitShadow x A c r n w F U X V g s R lab he,
        P.pulse_components x A c r n w F U X d V g s lab l.le⟩,
      pow,b,h,P.fullPrism_azure_margin x A c r n w V g s X F U lab,
      P.fullPrism_azure_limits x A c r n w V g s X F U lab,
      P.fullPrism_excludes_azure_gauge x A c r n w V g s X F U lab⟩,
      ⟨e,ro,ni,adv,y⟩,⟨cup,hand⟩,tote,labs,real₁⟩

#print axioms pearlElection
#check PiLp.norm_apply_le
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


