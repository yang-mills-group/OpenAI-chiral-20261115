import Lucent.Drill
import Lucent.Fanfare
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Ballad.Twah 
open Flare Emu Onyx Kea Cache
open Lamour Lamour.Bridge
open YM.Stationary (Gaia)
variable {I:Type}

-- cell-to-wavepacket at zenith
def duals (i:Loop I):List (Stamp I) := [(i.1,i.2.2,true),(i.1,i.2.1,false)]
abbrev anatomize (L:List (Loop I)) :List (Stamp I):= L.flatMap duals
def chantSpin (f:I→Twah)(r:ℕ)(N:Side): Stamp I→FC (Single N):=ton ∘ Twah.pulse f N r
abbrev rostrum (W:I→Staff) := SitSpin.rest (seat W) (body W)
lemma chord_dual (W:I→Staff)(i:Loop I) (r:ℕ)(N:Side): rollC (chantSpin (rostrum W) r N) (duals i)= (r:ℂ)^3 • cell N (seat W i.1) (body W i.1) i.2.1 i.2.2:= by
 let V:=rostrum W i.1
 have ht: star (gain r)*gain r=(r:ℂ)^3:=by simp only [gain,Complex.star_def,Complex.conj_ofReal]; norm_cast; rw [←sq,Real.sq_sqrt (by positivity)]
 simp only [rollC,duals,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,chantSpin, Function.comp_apply,Twah.pulse,in_lo,in_hi]
 rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,ht]

 rw [show Fock.remove ((rostrum W i.1).lower N i.2.2)*create ((rostrum W i.1).upper N i.2.1) = -cell N (seat W i.1) (body W i.1) i.2.1 i.2.2 from SitSpin.cr_swap _ _ (seat W i.1) (seat W i.1) i.2.2 i.2.1,neg_smul_neg]
lemma chordAll (W:I→Staff) (r:ℕ)(N:Side) (L:List (Loop I)): rollC (chantSpin (rostrum W) r N) (anatomize L)= ((r:ℂ)^3)^L.length • spind N W L:=by
 let T:=chantSpin (rostrum W) r N
 induction L with
 | nil=>simp [rollC,anatomize,spind,weave]
 | cons i L h=>
   rw [List.length_cons,pow_succ',show rollC _ (anatomize (i::L))=rollC T (duals i)*rollC T (anatomize L) from (by simp [T,anatomize,rollC])]
   rw [show T=_ from rfl, chord_dual, h,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; unfold spind weave; rw [List.map_cons,List.prod_cons]
#check @preparedFlat
#check @flat_post
#check @noble_linear

structure Role where
 pt:Gaia
 voice: DirSpin
abbrev upstairs (V:I→Role) : I → DirSpin:= Role.voice ∘ V
abbrev outside (V:I→Role) : Cellz I→Gaia := Role.pt ∘ V ∘ Prod.fst

def germ (V:I→Role) (L:List (Loop I)) : ℂ:= runes (germRho (outside V) (upstairs V)) (anatomize L)
def aria (V:I→Role) (L:List (Loop I)) : ℂ:= (1/2:ℂ)^L.length * germ V L
variable {ss ii kk r:ℕ→ℕ}{V:I→Role}{W:ℕ→I→Staff}
local notation "ν" => (fun n=> side Y (ii n) (ss n))
open Worth.Pays
theorem pressWake
    (g:Yard ν (fun n=> (r n:ℝ)))
    (h:∀ n,Kea.Pad P.K.j (ν n))
    (t:∀ n,body (W n)=upstairs V)
    (p:Twah.riseUp (fun n=>rostrum (W n)) r (outside V))
    (q:Twah.plateau (fun n=>rostrum (W n)) (outside V))
    (L:List (Loop I)):
    Tendsto (fun n=>((r n:ℂ)^3)^L.length * press Y (ss n) (ii n) (kk n) (W n) L)
       atTop (𝓝 (germ V L)):=by

 let l:=anatomize L; let N(n):= ν n
 let w(n):= flatSea Y (ss n) (ii n) (kk n)
 let B(n):= (RootBook Y (ii n) (kk n) (ss n)).J.M
 have z:= fanfare P.K.j (fun n=>rostrum (W n)) r (outside V) (upstairs V) l p q g (by exact t) (nontrivial_spin P) B h w (fun n=>preparedFlat Y (ss n) (ii n) (kk n))
 refine z.congr fun n=> ?_; change alleyR (mateK (N n)) (w n) (rollC (chantSpin (rostrum (W n)) _ _) (anatomize L))= _; rw [chordAll, map_smul,press,noble_linear]; rfl
