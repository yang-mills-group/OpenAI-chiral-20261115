import Bay.C.Lapel
import Bay.C.Stairs
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Lor Py.Rate.BScale Push.Uniform
open Pressure SectorNext.Remainder Nor
open Push.AbsoluteSums Trees Roots
open BPress (NPL PL lscale lscale_late lscale_one)
local notation "VΔ" => Buffered.Afterglow.Tower.VacuumSelection.Spine
open Salt SU Swell QuadClock Mew Vow.TreasuryFog
open BProof.Bide

variable {w:Berth}{a b c:ℝ}{x:Site w.side}{o:Seat w.side}{m t:ℕ}{f:w.First}

-- J prices
variable {y:phy w.side}
def capJ (P:VΔ)(a b c:ℝ):ℝ:=treeEarnings 24 (pStart P) 32 P.par.h a c*b
def quoteJ (P:VΔ)(a b c:ℝ)(x:ℝ):ℝ:=
 let z:=capJ P a b c
 z + ZxT P.par.R.L (pStart P) x z
lemma quoteP (P:VΔ)(a b c:ℝ):PL (quoteJ P a b c) :=
 (PL.const _).add (tallCostP _ _ _ (PL.const _)).pl

lemma rawJ (r:w.Rig a c m){V:SOp w.side}
 (u:w.tracePay a b x V):
 ∃ G,Nest w.P.par.U w.R w.K w.q 24 (node x) w.H (rScale w.p) (hollowDg w.K w.p x V) G
    (quoteJ w.P a b c w.x) (quoteJ w.P a b c w.x):=by
 have h:=(trimQ _ r.pulse r.full r.tonic u.pay).aft (offsetFit x x (separation_self _ ▸ Nat.zero_le _) r.shift)
 have p:w.p.order=(pStart w.P).order:=r.order.trans (w.P.run.meter.boot 0).2.2.2.2.symm
 have z: treeEarnings 24 w.p 32 w.H a c*b=capJ w.P a b c:=by
    unfold capJ treeEarnings reefCost;rw [p]
 rw [z] at h

 obtain ⟨G,t⟩:= Berth.buyRig r h
 rw [(lifeS w.L w.H a b m _ _ p _ r.sizeB (capJ w.P a b c) b).1] at t
 exact ⟨G,t⟩

lemma areaCoal (w:Berth)(g:w.Tall)(x: Site w.side):
 ∀ y∈areaMark w.p (node x),separation (node x) y ≤ 26 * w.p.B:=by
 intro y p
 obtain ⟨z,k,h⟩:=halo_spec.mp p
 rw[mem_singleton.mp k] at h -- orig direction?
 unfold Berth.Tall at g; omega

def mineJ (w:Berth)(x:Site w.side)(o:Seat w.side)
 (f:w.First)(u:Axis)(b:ℝ)(t:ℕ)(Z:Sour.Bag w.side):
 SealV w.side :=
 ⟨o,areaMark w.p (node x),meltZ t w.x*(w.Q * (2*b)),
    ((meltZ t w.x):ℂ) • w.J130 x f u,
    ((meltZ t w.x):ℂ) • ((w.Q:ℂ) • hollowDg w.K w.p x (f.J u)),Z⟩
def lamCoal (P:VΔ)(a b c:ℝ)(t:ℕ)(x:ℝ):ℝ:=
 meltZ t x * (quoteJ P a b c x)

lemma givenJ (r:w.Rig a c m)(g:w.Before a b m x f)(h:w.Tall)(u:Axis)(t:ℕ)
 (y:o∈grooveB 24 w.p (node x)):
 ∃ Z,Grant w (snowF w.P.par.R (lamCoal w.P a b c t)) (lamCoal w.P a b c t)
    (mineJ w x o f u b t Z):=by
 obtain ⟨V,W⟩:=rawJ r (g.arm u)
 let t1:=meltZ t w.x
 have ht:0<t1:=meltPos ..
 have q:=nestScale w.P.par.U w.R w.K (t1:ℂ) (nestScale w.P.par.U w.R w.K (w.Q:ℂ) W)
 have e:t1 * (w.Q * quoteJ w.P a b c w.x)=
    lamCoal w.P a b c t w.x * w.Q:=by unfold lamCoal t1;ring
 rw [Complex.norm_real, Complex.norm_real,Real.norm_eq_abs, Real.norm_eq_abs,abs_of_pos ht,abs_of_pos r.qq,e] at q
 exact ⟨_,locatedGlue _ _ (areaCoal w h x) y,
    by
     have p:=((atomDyed (Berth.clearance r) (boxSeal (g.arm u) r.pulse.hint.le)).scalar (w.Q:ℂ)).scalar (t1:ℂ)
     rw [Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ht,abs_of_pos r.qq] at p
     exact p, fun i _ k=> q.science i k, Berth.rootLodge w q.pouch y⟩

def reverseCab {n:Side}(t:Site n): Sweep n:=(taxiPlus t)⁻¹
lemma seated (r:w.Rig a c m)(g:w.Before a b m x f)
 (i:Axis)(y:Site w.side):
 move (reverseCab (y-x)) (w.J130 x f i)=w.Jpose x f i y:=by
 let s:=taxiPlus (y-x)
 have p:move s (w.Jpose x f i y)= w.J130 x f i:=by
    ext1 V
    rw [dip _ _ (rfl:s.charge=false),show detX s.s=false from det_i]
    exact (Berth.JposeTip r g i y (flashA s⁻¹ V)).trans
       (congrArg (w.J130 x f i) (by rw [lights, inv_mul_cancel,rev1]))
 have e:plainP (w.Jpose x f i y):=fun v=>by
   have z:=((((toothReceipt y (Berth.clearance r) (g.arm i) r.pulse.hint.le).scalar (w.Q:ℂ)).pay).basis.allV (v,v)).sector
   exact Chord.keys_of_chord (Chord.full z)
 rw [←p,dance _ _ e];exact (show move (s* s⁻¹) (w.Jpose x f i y)=_ by rw [mul_inv_cancel,move_e e])


lemma VelvetCab {n:Side}(y:Site n): Velvet (reverseCab y) :=by
 have h:(reverseCab y).s=(1:Signed)⁻¹:=rfl
 unfold Velvet;rw[h,inv_one];exact Glam.flat _

variable {V:Sour.Bag w.side}

lemma cabsMove {n:Side} (F:Stencil n) (y:Site n) (c:ℂ):
 move (reverseCab y) (c • F) = c • move (reverseCab y) F :=by
 let s:=reverseCab y
 have h:s.s=1:=inv_one
 ext1 z
 rw [dip _ _ (rfl:s.charge=false),Pi.smul_apply,Pi.smul_apply,dip _ _ (rfl:s.charge=false)]
 have d:detX s.s=false:=h ▸ det_i
 rw[d]
 exact twist_scalar ..

lemma seatsJ (r:w.Rig a c m)(g:w.Before a b m x f)
 (i:Axis)(y:Site w.side):
 (watch (reverseCab (y-x)) (mineJ w x o f i b t V)).shown=((meltZ t w.x):ℂ) • w.Jpose x f i y:=by
 rw [← seated r g]
 exact cabsMove (w.J130 x f i) _ _
