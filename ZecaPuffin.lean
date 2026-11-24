import ZecaSkua
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



open Preparation.Yoke Yoke.Travel SatinNucleus Six Regis.Head Regis.Head.Brecht
open CF.Velvet CF.Pannier.Chancel



def Custard (P:Spine)(A:P.Flotsam):Prop:=
 ∀ x:P.Spectrum0 3,∀ seq:ℕ→ℕ,Tendsto seq atTop atTop →
   (∀ i,Tendsto (fun j=>A.u i (seq j) x) atTop (𝓝 0)) →
    P.Umber x seq
lemma puffin (P:Spine){C:ℝ}
   (W:5∣P.par.R.L.val)
   (H:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k):
 ∃ y,P.Custard y :=by
 haveI : Nonempty Plume_LocalFieldBounds:=⟨P.startW⟩
 obtain ⟨g,s⟩:=exists_surjective_nat (ℕ × Bool × Bool × Plume_LocalFieldBounds × Plume_LocalFieldBounds)
 refine ⟨{
    u:=fun i => P.carbbendMiss (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2.1 (g i).2.2.2.2 0 0,
    c:=fun i m=>P.mistake_live 3 Yoke.witnessZ _ _ _ _ _,
    n:=fun i m x=>norm_nonneg _,
    ok:=fun i=>P.carbbending_go _ _ _ _ _ _ _ W H
 },fun x seq k e=>⟨k,?_⟩⟩
 intro f a b p q
 obtain ⟨i,r⟩:=s (f,a,b,p,q)

 have z:=e i
 change Tendsto (fun j=>P.carbbendMiss (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2.1 (g i).2.2.2.2 0 0 (seq j) x) atTop (𝓝 0) at z
 rw [r] at z
 exact z

theorem exists_satin_puffin :
 ∃(P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x), P.Shell K c r x R i₀ F U A n w V g h X D ∧  (∃ W, P.Custard W ∧ P.Froth x g h A W) :=
 whitewater Custard (fun P=>puffin P)
#print axioms exists_satin_puffin
#check @Iguana.twin
#print Iguana
variable (P:Spine) {K:P.Register} {c r:ℕ→ℕ}
 (x:P.Spectrum0 3) {R:P.Ellis 3 x} {i₀:ℕ}
 {F U:SampleDose} {Y:ℕ→P.Apron} {n:ℕ→ℕ} {w:Lead.Clan→Prism}
 {V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
 {f k:ℕ} {X:P.HandleWith x c r Y n} {D:P.Cilium x}

lemma caramel 
    {W:P.Flotsam}(white:P.Custard W)
 (T:P.Shell K c r x R i₀ F U Y n w V f k X D)
 (e:P.Froth x f k Y W)
 (B:P.Nib 3 (P.advocate 3 x 3))

 (t:P.Iguana 3 (P.advocate 3 x 3) B Y):
 ∃ seq,P.Lark x seq f k Y ∧ ∃ sc,
    P.Boom x seq Y B sc ∧ P.Ebb x B sc seq ∧
    P.Mach x (P.twinNib 3 (P.advocate 3 x 3) B) (star sc) seq ∧
    P.Ebb x (P.twinNib 3 (P.advocate 3 x 3) B) (star sc) seq:=by
 have l:=t.nib
 have i:= T.scores.incense
 have a0:P.NightCop:=i.2.2.2.2.2.2.1
 have j:=P.shoot_again x _ B (i.2.2.2.2.2.2.2.2 w).cinema l
 have b':=t.twin.bottle
 obtain ⟨seq,sky,allGo,d,K',h,v⟩:=e.wrack _ (P.totter x B j l.bottle b')
 have u:=e.kindle seq sky
 refine ⟨seq,u,?_⟩
 obtain ⟨A,C,b,y,uf,z,rfl,p⟩:=u.cinema
 obtain ⟨scale,pos,nick⟩:=P.tileLess x B uf y z l p a0 j

 have m:=mach u.meshy R sky
      (nick.loftIt l.bottle (P.inkLoss_zero A) sky.sky)
 have g:=P.mach_star x _ scale nick (P.inkLoss_zero A) u.meshy R sky
    (white x seq sky.sky allGo) b'
 obtain ⟨r,s⟩:=P.sesqui x B scale seq m g h v
 exact ⟨scale,⟨l,pos,sky.sky,m⟩,r,g,s⟩
#print axioms caramel
