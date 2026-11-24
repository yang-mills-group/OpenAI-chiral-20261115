import GaugeFieldConstruction.BudgetFromElection
import GaugeFieldConstruction.FreeSocietyNX
/-!
# Retain budgets so one can elect in a set of nonzero weight

Adapted from FreeSocietyNX and purchases in `Ochre, Swirls, Coral, Accomplished, Pachilla3`. No
new preparation of any calendar estimates here. Prove a-e attainment of the LedgerMatch to permit even
positive-measure restrictions when selecting the vacuum.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
variable (P:Spine)(x:P.Spectrum0 3)
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath Papal AUbard
variable (C:Clip→ℝ)(O:PinRack→Badge)
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
lemma budgetHeight (NLeaf:ℕ)(q':TintDemand)(θ:BandS→ℕ) (t:ℝ)(w:8 ≤ t) (E:Crest_Pay (HourJ C t) t (WorkCharm O (HourJ C t)) P NLeaf (yarrow q')) (hR:P.Roster):
 WayΘJ C t O (yarrow q') P NLeaf ∧∀ v:ℕ,∀ᶠ g:ℕ in atTop, ∃ H:RosterJ P θ t g,v ≤ H.count∧0<H.u∧SocietyNX P H:=by
 let Q:=HourJ C t; let q:=yarrow q'
 obtain ⟨h,V⟩:=parcel_from_review P Q O q NLeaf t w (fun i=> zero_le_one.trans ((le_max_left ..).trans (le_max_right ..)))  E hR
 refine ⟨⟨E,h,V⟩,fun m=>?_⟩
 let Y:=P.run; let R:=P.par
 have he: fustianJ.choose ≤ R.R.L.val:=by
    obtain ⟨Pay,kC,Γ,Tξ,hX,hKc,hΓ,Dg,Pv,P1,P2,P3,T,F,I,mo,A,C',v,V₃,D,c,hD,w,h,e,p,u,Z,J'⟩:=E.store
    exact le_trans ((le_max_right (q' R.K R.L Pay kC Γ Tξ) _).trans (le_max_left ..)) Pv -- tune metavars
 obtain ⟨D,P0,tF⟩:= FlorianNX Q t O P q NLeaf E h V
 obtain ⟨u,H₂,H₃,F,fX,T₀,hT⟩:= ((eventually_gt_atTop (0:ℝ)).and (tF (ωWcap θ+m))).exists -- tune
 filter_upwards [eventually_forall_ge_atTop.mpr (fustianJ.choose_spec R he),hT,Maribus P.run] with g pv p0 hz
 let A:= Q R.K.top.clip
 refine ⟨{ u:=u,K0:=A,Aζ:=_,gates:=D,payOne:=_,count:=_,ν:=H₂.le,wage:=Nat.le_add_right (ωWcap θ) m,θgu:=P0,θholy:=T₀,money:=?_,star:=fun k0 h=>(pv k0 h).1,price:=fun i h=>(pv i h).2,tempo:=hz,Z:= fun i k g v=> (p0 i k g v g).choose },?_⟩ -- syntax Lean struct fields separated by , no spaces tune
 · unfold A Q HourJ; exact (le_max_right ..).trans (le_max_right ..)
 refine ⟨by simp,H₂,fun d=>?_⟩
 obtain ⟨c,hM⟩:=h -- Arm? h is Armature
 obtain ⟨P',p,F',U,Tξ,U0,V,u',v',w',fX',L,Q,J,f',t,X',m'⟩:= hM
 have z:=X'.2.2.1.2
 obtain ⟨a,b,c,D',K,q,H,g',l,ℓ,v,V⟩:=z
 obtain ⟨ζ,hζ,Δ,hD,Y⟩ := SurveyZ_NX P.run (ωWcap θ+m) V d fX.2 fX.1 u H₂
 refine ⟨ζ,hζ,D',K,q,H,Δ,hD,?_⟩
 filter_upwards [Y] with s t i k g0 l0 z wζ
 obtain ⟨E',J',χ⟩:=t i k wζ.le
 have he':=((p0 i k g0 l0 g0).choose_spec s z wζ)
 refine ⟨E',J',?_⟩; rw [he']; exact χ

#print axioms cohorts_meet
#print axioms budgetHeight
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
