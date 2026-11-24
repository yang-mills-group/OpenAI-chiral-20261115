import Organdy.Marabou

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

open Hive Levier Urn


lemma trims(B:ℕ)(s:Signed):
 (mortise B).image (incX s).motion = mortise B:=by
 unfold mortise; rw [show (incX s).motion=(s.act (R:=ℤ)) from ?_, box_covariant]
 funext x
 change s.act x + 2 • (0: Cover)=_
 simp

lemma polished {n:Side}(s:Signed): Levier.ray (veer (incX s)) (incX s)=polestar n s:=by
 rw [veer_sign];change Sweep.mk s (wrap n 0) _=_;rw [map_zero];rfl

abbrev hatP {n:Side}(y:Mark n): Mark n:=feeD • ∑ s:Signed, ebony s • hmMark (incX s) y

lemma hatReads {n:Side}(K:Scree.Loom n)(p:BudgetPoint)(X:SOp n):
 hatP (Zc K p 0 X)=haloMark K p X:=by
 have h(s:Signed)(V:Fields n):
    hmMark (incX s) (Zc K p 0 X) V = chime K p (node 0) X (flashA (polestar n s) V.1) • 1:=by
    unfold hmMark voltaM
    rw [inv_inv]
    conv =>
     lhs
     arg 2
     rw [polished]
    rw [←tunnel_choice]
    change lotB (veer (incX s)) (veer (incX s)) _ (_ • _)=_
    rw [visage,map_one,Bool.xor_self];rfl
 funext V
 unfold hatP
 simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply,h, smul_smul,←Finset.sum_smul,smul_smul];rfl

def collarW {K:Calibration}(F:Buffered.Family K): Buffered.Family K:=
 feeD • ∑ s:Signed,ebony s • flick (incX s) F

variable {K:Calibration}
lemma collarVal (f:Dome K): (pauldron K f).val=collarW f.val:=by
 rw [showtime,collarW]; let r: Dome K →ₐ[ℂ] Buffered.Family K := (screenHall K).val
 change r (feeD • ∑ s:Signed,ebony s • flounce K (incX s) f)=_;rw [map_smul,map_sum];simp_rw [map_smul];rfl

variable {I:Type*}{N:I→Side}{B:ℕ}
 {n:I→Side}{e:∀i,K.c (n i)=N i}{l:Filter I}{S:Finset Cover}
 {f g:Buffered.Family K}
 {y:(i:I)→Mark (N i)} {F G:I→Buffered.Family K}
lemma Bolt.tangled (s:Signed)
 (h:Bolt l (mortise B) n e y F f):
 Bolt l (mortise B) n e (fun i=>hmMark (incX s) (y i)) (fun i=>flick (incX s) (F i)) (flick (incX s) f):=
 trims B s ▸ h.tangle (incX s)

lemma Bolt.spangled
 (h:Bolt l (mortise B) n e y F f):
 Bolt l (mortise B) n e (fun i=>hatP (y i)) (fun i=>collarW (F i)) (collarW f):=
 (Bolt.sum univ (fun s i=>ebony s • hmMark (incX s) (y i))
  (fun s i=>ebony s • flick (incX s) (F i))
  (fun s=>ebony s • flick (incX s) f) fun s=>(h.tangled s).scale _).scale feeD

-- will use also for shifted y at station∪shift
lemma Bolt.accord [l.NeBot](a:Bolt l S n e y F f)(c:Bolt l S n e y G g)
 (t:∀ᶠ i in l, Hosp S (N i)): f=g:=by
 have p:K.c ∘ n=N:=funext e
 have x:=a.sees; have z:=c.sees
 subst N
 have v:∀ᶠ i in l,F i=G i:= t.mono fun i q=>box_ext K S (a.queue.goes i) (c.queue.goes i) q ((x i).trans (z i).symm)
 exact funext fun m=>funext fun V=>tendsto_nhds_unique ((a.queue.atP m V).congr' (v.mono fun i p=>congrFun (congrFun p m) V)) (c.queue.atP ..)
