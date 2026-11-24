
import Organdy.Squid
import YM.SU5.Interaction.Source
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine)(i k s m:ℕ)
variable (o: Site (age P.run i s))(z:Orbit (age P.run i s))
local notation "Λ"=>P.par
local notation "xt"=>hat (Λ).R.L (Λ).x s
local notation "N'"=> age P.run i s
local notation "KL"=> (P.run.voyage i).CapeT s
local notation "R✤"=>RootBook P.run i k s

local notation "p'" => (R✤).p
local notation "mA"=> Moire.bloom (R✤).J.P
local notation "mS"=> PresN P i k s
local notation "hue"=> hueW (Λ).R.L xt
local notation "Q'"=> pinpr (Λ).R.L xt
local notation "n'" => ((p').B/10)

local notation "imageS"=>spar (Λ).K.j (R✤).J.M (KL z)
local notation "imageT"=>(R✤).J.P.den (KL z)
local notation "W"=>windmill o m
local notation "stateQ"=>relV (Λ).U (R✤).J (KL z)
local notation "front"=> frontK mS mA m o KL

/-- Full: precisely the Z of the (125)--(127) algebra (freeDriver), here
with windmill W. As in earns_tip, acts on the **full board** before
taking the density correction or signed integral. Pin is at the *actual*
consultation even if some mask fails. -/
lemma penny :
 let h:=(projects_here P.run i k s z).1
 let L:=ballL (nursery imageS h) stateQ
 let C:=capT imageS imageT
 let D:=front z
 let E:=coinZ imageS W
 let B:=(R✤).board z
 D = StressExchange.Zcharge imageS (tickA N') C W ∧
  acts E (vacuum _)=0 ∧
  acts D stateQ=0 ∧
  (∀ u, L (acts E u)=acts D (L u))∧
  (acts D (denZ R✤ (Λ).U KL z)=
     Complex.exp ((R✤).betaL KL z) • (L (acts (E * B.val) (vacuum _)))):=by
 intro h L C D E B
 have p: D= StressExchange.Zcharge imageS (tickA N') C W:=by
    change (kerLocal imageS (tickA N') W (mA (profile (KL z))))=_
    rw [Moire.bloom_P]
    rfl
 have ht:TagG imageS C:=tag_g imageT h
 have hv:= (projects_here P.run i k s z).2
 have g:∀ u, L (acts E u)=acts D (L u):=by
   rw [p]; exact truncZ _ _ ht h _ hv
 refine ⟨p,voidCoin ..,by rw [p]; exact Zvoid _ _ ht h _ hv,g,?_⟩
 have y:acts (tank imageS B) stateQ=L (acts B.val (vacuum _)):= (loaf (nursery imageS h) stateQ _).symm
 rw [denZ,map_smul,act_mul]
 change Complex.exp _ • acts D (acts (tank imageS B) stateQ)=_
 rw [y,g]

variable {J T :Axis→SOp (age P.run i s)} {X Y:SOp (age P.run i s)} {w:ℕ} {a b a' b':ℝ}

/-- Recover (126) with the spur routing, and equality at the gate (in the open lane).
Without the gate, split into tail and mask defects for the actual physical terms;
the signed estimate is via Nest and Barrage which use BOTH. -/
lemma bronze
 (t:Tide P i k s m w a' b')
 (u:Kit P i k s o m a b J T X Y):
 let V:=puffLine KL p' o J X m
 let F:=blazePlate KL X + northLine KL o J m - barS0 N' m o
 let H:=blazePlate KL Y + northLine KL o T m
 front z=F z+H z ∧
 (houseK p' (grooveB 24 p' (node o)) V)=
 houseK p' (grooveB 24 p' (node o)) (front-H) ∧
 inward (mS (profile (KL z))) W (mA (profile (KL z)))=
  ∑ ν:Axis,
    (co_Ψ (o+gapPlus ν m) o (J ν) (profile (KL z)) - co_Ψ (o-gapPlus ν m) o (J ν) (profile (KL z)) +
    (co_Ψ (o+gapPlus ν m) o (T ν) (profile (KL z)) - co_Ψ (o-gapPlus ν m) o (T ν) (profile (KL z)))):=by

 intro V F H
 have s': (p').B+2*m ≤24*(p').B:=by have :=t.lot; omega
 refine ⟨lanternMil t.docks t.pilots u.hem u.bone z,attachLamp t.docks t.pilots u.hem u.bone s',?_⟩
 rw [inwardE t.pilots _ (t.docks.roof.paid z)]
 refine sum_congr rfl fun y _=>?_
 rw [co_Set _ _ _ _ t.pilots _ _ (u.hem y) t.docks.pos _ (t.docks.roof.paid z),
     co_Set _ _ _ _ t.pilots _ _ (u.hem y) t.docks.pos _ (t.docks.roof.paid z)]
 abel
