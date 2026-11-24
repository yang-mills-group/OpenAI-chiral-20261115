import ZecaPear
import ZecaShell
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




variable (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x)

local notation "Y"=>P.soldTrumpet A c r n w
local notation "Z" z:max i:max=> ((Y z i).kiss P 3)

lemma can_wait (t:ℕ)(m:ℝ)(h':0< m):∃ q:ℕ,0<q∧m≤P.pen t q:=by
 obtain ⟨q,u⟩:=exists_nat_gt (m / P.macroStep t)
 refine ⟨q, by have :0<(q:ℝ):=(div_pos h' (P.macroStep_pos t)).trans u; exact_mod_cast this,?_⟩
 rw [pen,bell,Int.cast_natCast]; exact ((div_lt_iff₀ (P.macroStep_pos t)).mp u).le

def ZestCase(i:ℕ):Prop:=
 ∀ t:ℕ,c (n i) ≤ t → ∀ a b:Lead.Clan, ∀ q:ℕ,
     (d:0<q) → 3≤P.pen t q → 
       ((∀y∈tsupport F.val,P.Lunette 3 t q (-(q:ℤ)) (Z a i) y) ∧
        (∀y∈tsupport U.val,P.Lunette 3 t q 0 (Y b i) y) ∧
        P.SoftRead x t q d (P.prepared t (Z a i) F) (P.prepared t (Y b i) U))

structure Zest:Prop where
 fees:P.Lemon x
 budget:∀t,∃q:ℕ,0<q∧3≤P.pen t q

 buy_ (a:Lead.Clan)(i t:ℕ)(e:c (n i) ≤ t):P.Lull x t (Y a i) ∧ P.Lull x t (Z a i)
 consult:∀ᶠ i in atTop,P.ZestCase c r x F U A n w i

lemma zestFit (t q:ℕ)(k:3≤P.pen t q)
 (F U:SampleDose)(e:tsupport F.val ⊆ reviewEarlierBox.invites)(l:tsupport U.val⊆ reviewLaterBox.invites)
 (B E:P.Apron)(a:B.realWidth P 3<1)(b:E.realWidth P 3<1):
 (∀y∈tsupport F.val,P.Lunette 3 t q (-(q:ℤ)) B y) ∧
 (∀y∈tsupport U.val,P.Lunette 3 t q 0 E y):=by
 have u:P.pen t (-(q:ℤ))=-P.pen t q:=by rw [pen,bell,Int.cast_neg,neg_mul]; rfl
 have v:P.pen t 0=0:=by rw [pen,bell,Int.cast_zero,zero_mul]
 constructor
 · intro y r
   obtain ⟨d,f⟩:= e r 3 (Set.mem_univ _)
   change -2 < y 3 at d; change y 3 < -1 at f
   constructor <;> [rw [u]; rw [add_neg_cancel,v]] <;> linarith only [k,a,d,f]
 intro y r; obtain ⟨d,f⟩:=l r 3 (Set.mem_univ _)
 change 1 < y 3 at d; change y 3< 2 at f
 constructor <;> [rw [v];rw [add_zero]] <;> linarith only [k,b,d,f]

#check @Zest

lemma zLL
 (p:∀a i,P.Sensor (Y a i) a.2)
 (a:Lead.Clan)(i t:ℕ)(e:c (n i) ≤ t):P.Lull x t (Y a i) ∧ P.Lull x t (Z a i):=
     ⟨P.luv x t (Y a i) (p a i) e,P.luv x t (Z a i) (P.sensor_mirror a.2 3 (Y a i) (p a i)) e⟩

lemma zestFlip (a:P.Apron)(h:a.realWidth P 3<1): (a.kiss P 3).realWidth P 3<1:=h

lemma zCost(e:tsupport F.val ⊆ reviewEarlierBox.invites)(l:tsupport U.val ⊆ reviewLaterBox.invites)
 (p:∀a i,P.Sensor (Y a i) a.2)
 (o:∀a,∀ᶠ i in atTop,(Y a i).realWidth P 3<1):P.Zest c r x F U A n w:=by
 have L:=P.zLL c r x A n w p
 refine ⟨P.lemon x,fun t=>P.can_wait t 3 (by norm_num),L,?_⟩
 filter_upwards [eventually_all.mpr o] with i ha
 intro t y a b q d v
 obtain ⟨h',p'⟩:= P.zestFit t q v F U e l
    (Z a i) (Y b i) (P.zestFlip (Y a i) (ha a)) (ha b)
 exact ⟨h',p',P.softRead x t q d (P.prepared t (Z a i) F) (P.prepared t (Y b i) U) ((L a i t y).2.smears q d (-(q:ℤ)) F h')
                                     ((L b i t y).1.smears q d 0 U p')⟩

lemma zest (S:P.Shell K c r x R i₀ F U A n w V g h X D):P.Zest c r x F U A n w:=by
 have G:=S.scores.native.2.2.2.2.2.2.2.2.2.1
 have h₀:=G.armada

 exact P.zCost c r x F U A n w G.supports.1 G.supports.2 h₀.sensor 
   (fun a=>(h₀.slender a 3).eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)))
#print axioms zest
