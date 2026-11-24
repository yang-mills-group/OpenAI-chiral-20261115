import Bay.Cheer
import Bay.C.Rosy
import YM.CF.Continuum.Winter
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


open Salt SU Swell
abbrev silk {n:Side}(s:Sweep n):=paintR s.charge (detX s.s) (socks s)
abbrev rawk {n:Side}(s:Sweep n):=Spire.tourP (socks s) s.charge (detX s.s)
abbrev clash {n:Side}(s:Sweep n)(y:phy n):phy n:=fun x=>rawk s (y (yellA s⁻¹ x))
lemma alight {n:Side}(s:Sweep n)(y:phy n)(x:Orbit n):
 clash s y (yellA s x)=rawk s (y x):=by rw [clash,unyell]
abbrev Pine {n:Side}(x:Orbit n):Prop:= Injective (priorP x.2)
lemma treeV {n:Side}(s:Sweep n){x:Orbit n}(a:Pine x):Pine (yellA s x):=a.comp ((boxA s).injective)

variable (w:Berth){a c:ℝ}{m:ℕ}
abbrev wax(V:Pane w.side):Cipher w.side:=
   exp (exponentL w.R.p w.R.F V+exponentL w.R.p w.R.slip V)
lemma poolM (u:Orbit w.side)(d:IsStarProjection (w.emblem u))
 (y:phy w.side)(v:Sour.Bag w.side):
 w.sockets u d y v ↔ turfSock (w.emblem u) d (relV w.U w.R.J (w.K u))
    ((wax w u.1).val) (∑ i,v i u) (y u):=by
 let L:=ballL (nursery _ d) (relV w.U w.R.J (w.K u))
 let H:= (wax w u.1).val
 let c:=Complex.exp (w.R.betaL w.K u)
 have p: ∀ z,w.pilot u d z=c • L (acts H z):=fun _=>rfl

 have nz:c≠0:=Complex.exp_ne_zero _
 unfold Berth.sockets
 simp_rw [p,map_smul,smul_right_inj nz]
 rfl


lemma old_wax (s:Sweep w.side)(x:Pane w.side)(h:w.s ≤ w.P.run.uv w.k):
   wax w (flashA s x)=silk s (wax w x) ∧ ∀ D J,Injective (priorP J)→
    w.R.K (moveForce s D) (flashA s x,bun s J)=silk s (w.R.K D (x,J)):=by
 let hp:= ((w.P.run.voyage w.i).X (w.P.run.uv w.k)).pull.note w.s h
 let he:=spinZ s.charge s.s
 have hx:= Window.turn_exponent s hp.buoy (by trivial) he x
 refine ⟨?_,fun D J k=>hp.nite.face s trivial _ he D x J k⟩
 letI : NormedAlgebra ℚ (Scree.Cipher w.side):= NormedAlgebra.restrictScalars ℚ ℝ _
 let e:=silk s
 have ht:w.R.slip=0:=hp.tone
 have u V:exponentL w.p w.R.slip V=0:=by rw [ht]; simp [exponentL,numbE]
 unfold wax; change exp (exponentL w.p w.R.F _+_) = e (exp _)
 rw [u,u,add_zero,add_zero,map_exp e e.toLinearMap.continuous_of_finiteDimensional]
 exact congrArg exp hx

variable {w}
lemma deck (V : Orbit w.side)
 (r:w.Rig a c m)
 (s:Sweep w.side)
 (t:Pine (V:Orbit w.side)):
 sings s.charge (socks s) (w.emblem V)= swapX (detX s.s) (w.emblem (yellA s V)) ∧
 arum (socks s) s.charge (detX s.s) (mateK w.side) (relV w.U w.R.J (w.K V)) = relV w.U w.R.J (w.K (yellA s V)):=by
 have he:w.K (yellA s V)=flashA s (w.K V):= r.pulse.roof.move _ _ _ t
 have hy:1≤w.P.par.K.j:= w.P.par.kJ.symm ▸ (by decide : 1 ≤ 4)
 have hv:=r.pulse.roof.paid V
 constructor
 · unfold Berth.emblem; rw [he]
   have d:=w.U.needed.trans r.deep
   have st:= w.P.par.V.note
   exact funde_f (castX s) (xtra s.charge) _ (spinZ ..) _ _ hy _ _
    (st.fields_one _ d) (hv.shrink w.U.gem)
 rw [he]
 have t:= (w.slew r.high.le).staff
 exact Hive.birds s.charge w.P.par.W.pearl w.P.par.V.note r.deep hy
    (castX s) _ (spinZ ..) _ t.leanJ.1 t.ready _ hv

abbrev Grass (w:Berth)(y:phy w.side)(v:Sour.Bag w.side):=
 ∀ x,Pine x → ∀ d,w.sockets x d y v
lemma tug {y:phy w.side}{v:Sour.Bag w.side}(r:w.Rig a c m)
 (s:Sweep w.side)(j:Grass w y v):
 Grass w (clash s y) (quiver s v):=by
 intro z
 obtain ⟨x,rfl⟩:=surRaise s z
 intro p d
 have p0:Pine x:= unyell s x ▸ treeV s⁻¹ p
 have h:= w.emblem_pure r x
 obtain ⟨he,hv⟩:=deck x r s p0
 have b:=(poolM w x h y v).mp (j _ p0 _)
 have e:= turfU h d _ _ _ he (mateK _) _ _ _ _ b
 apply (poolM ..).mpr
 have q:(yellA s x).1=flashA s x.1:=rfl
 rw [alight,←hv,q,(old_wax w s x.1 r.high.le).1,←Equiv.sum_comp (moldA s)]
 simp_rw [salute]
 let A:=lotY s.charge (detX s.s) (socks s)
 change turfSock _ _ _ _ (∑ i,A (v i x)) _
 rw [←map_sum]
 exact e
lemma earnedP(n:Side):∀ᵐ x∂city n,Pine x:=
 (measurePreserving_snd (μ:=prior SU.group (More n)) (ν:=depot n)).quasiMeasurePreserving.ae sepT
