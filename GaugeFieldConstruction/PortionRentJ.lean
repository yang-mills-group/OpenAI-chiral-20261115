import GaugeFieldConstruction.CunardJ
import GaugeFieldConstruction.SakhaJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
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
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.
variable {m i k f:ℕ}
local notation "ΤΓ"=> P.run
local notation "ΓΥ"=> P.run.uv k
variable (w:f0 ≤ P.run.uv k)(h:(P.run.voyage i).kick≤ k)
local notation "Qi"=> p.Z i k w h
#check ProbeθJ
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (Ω:BoonsθJ p B0 M i k w h)(x:P.VMark)(R:Signed × Bool)(u:BandS)
variable {s t r:ℕ} {n:ℕ}
local notation "Ξu"=> Fin (θ u)
local notation "Φ"=> (ΓPrimary P.run i k θ)
local notation "η"=> FrameK (Fin (θ u))
variable (pu:Adept_T θ B0 M G)
-- Flexible anchor representation. stores assertion on arbitrary Movement Words.May align proofs of R3 via composition. KeyScope.S.
variable (L:finsJ)
local notation "Υs"=> ScaleμJ P.par u.val
include p
lemma ShapeR_B (pf:f0≤ f)(c:f≤ s)(ps:s ≤ P.run.uv k)(g: f0 ≤ r)(Y:FrameK (Fin (θ u))) : 0≤ FlavorRateJ P u f r s (LoomK Y)∧0≤ FarePQ P f r u (LoomK Y):=by
 let t:= p.price f0 le_rfl u (P.run.uv k); have hP:0 ≤ ScaleμJ P.par u.val:=t.small; have hQ: 0≤ stepRateJ P.par u.val:=zero_le_one.trans t.bound; have he:= noLoom Y; have ht:= t.θpay; have hb:0≤ RStepJ P.par u.val:= (mul_nonneg (by norm_num) hQ).trans ht; have hz':0≤ RankQJ P.par f:=(p.tempo f pf).1.le; have hk:0 ≤ RankQJ P.par r:=(p.tempo r g).1.le
 constructor
 · unfold FlavorRateJ; positivity -- tune
 unfold FarePQ; split <;> positivity
abbrev RBuk (d:ℕ)(b:BoardDate X)(j:finsJ)(x:X)(D:BandS):Prop:=∀ t,f≤t→ t<P.run.uv k → (b t (x,D)=j.succ ↔ t=d)
-- envelope leaf tracked at s. ghost loan uses scalar weights known.Anchor can vary r even >s (for v≡0 etc)
structure GrappleJ (R:Signed × Bool)(s:ℕ)(t:s≤P.run.uv k)(l:ℕ)(l0:finsJ)(u:BandS)(r:ℕ)(y:FrameK (Fin (θ u)))(K:Family P.calibration)(v:ℝ) : Prop where
  run : f ≤ s
  rise : ShelterJ P x f K s i
  cost : 0 ≤ v
  grip(X:Type)[Fintype X][LinearOrder X](vL:X→LaurelJ)(lX:X→P.VMark)(lR:X→ Signed × Bool)(b:BoardDate X)(B:SailκJ X θ→Waves)(Z:PlumberJ P.run i k X θ)(p': SalaryJ p B0 M i k w h lX vL lR b B f Z)(ξ:X)(t':lX ξ=x)(v':lR ξ=R)(k0:RBuk (P:=P) (k:=k) (f:=f) l b l0 ξ u) (ξB:∀ i',B (Bootκ θ (ξ,u) i' l0.succ)=0):
    Circζ P.run i k θ Z f ξ (linkT_J P f s (vL ξ) K i k t- SunLO (d0:=ξ) (f:=f) p w h B0 M Ω x R u Z (fun s=>wayZJ P.par f s (vL ξ)) false r y) v
#check GrappleJ
variable (pk:f0 ≤ f)
include pk
lemma PlotGripJ (c:f ≤ s)(t:s<P.run.uv k)(g:f0≤ r)(e:r ≤ s)(y:FrameK (Fin (θ u)))(m:ℕ)(pH:i=P.gatePeriod m)(pL:k=P.gateCut m) : GrappleJ (f:=f) p w h B0 M Ω x R s t.le s L u r y (LMarkBJ p w h B0 M Ω x R u L (g.trans e) t.le r e y) (FlavorRateJ P u f r s (LoomK y)):=by
 subst i k
 refine ⟨c,HideRoomJ P x f s u c (fun s a=>p.tempo s (pk.trans a)) B0 R _ t.le _, (ShapeR_B p u pk c t.le g y).1,?_⟩
 intro X _ _ vX lX lR b B Z p' ξ d0 e0 t0 ξB; exact SpokePJ p w h B0 M Ω x R u vX L lR lX b B Z p' ξ e0.symm d0 ξB (fun j h t=>(t0 j h t).trans (eq_comm)) c t e g m rfl rfl y -- tune
variable (tP:s≤ P.run.uv k) {l:ℕ}(Y:FrameK (Fin (θ u)))(F D:Family P.calibration) {U0:ℝ}
variable (H: GrappleJ (f:=f) p w h B0 M Ω x R s tP l L u r Y F U0)
omit pk
include H
lemma GrappleJ.advance_X (u':s≤ t)(e:t≤P.run.uv k)(d:Tapestry.exhibit P.run P.large t i D= convoy P.run i k u' (Tapestry.exhibit P.run P.large s i F)) : GrappleJ p w h B0 M Ω x R t (f:=f) e l L u r Y D U0:=by
 refine ⟨H.run.trans u',ShelterJ.advance _ _ t u' H.run _ _ h e H.rise d,H.cost,?_⟩; intro X _ _ V k' R₀ b B Z w' ξ pX t' k₀ ψ; rw [LinkAdvance h x V ξ u' e H.run H.rise d]; exact H.grip X V k' R₀ b B Z w' ξ pX t' k₀ ψ
#check ShapeR_B
open ProbeθJ
-- mode α.Layout selection distinct.Mark cost.
abbrev claimB (u:BandS)(s:ℕ)(j:finsJ): ℕ→BandS→ Fin 6:=fun i p=> if i=s∧p=u then j.succ else 0
variable (et:3*f ≤ P.run.uv k)
include et pu pk
lemma GrappleJ.applyS (g:f0≤ r)(u':r ≤ P.run.uv k): CiriciJ P f s i k x F (ΦWallet p*(U0+ FarePQ P f r u (LoomK Y))) tP:=by
 let B:= claimB u l L
 refine CirCase x f p B0 M pu i k w h pk et F s tP (U0+FarePQ ..) (add_nonneg H.cost (ShapeR_B p u pk H.run tP g Y).2) R B ?_
 intro n V pV Z q
 let W: Fin n→P.VMark:=fun _=>x; let J:Fin n→Signed × Bool:=fun _=>R; let T:BoardDate (Fin n):= fun s x=> B s x.2; let N:= Fin n
 intro ν
 have hB:RBuk (P:=P) (k:=k) (f:=f) l T L ν u:=by
    intro t a w; change (B t u=L.succ ↔ t=l); unfold B claimB; by_cases t':t=l <;> simp [t',Ne.symm (Fin.succ_ne_zero L)]
 have hc:= H.grip N V W J T 0 Z q ν rfl rfl hB (fun i=> rfl)
 have he:=hc.add (FarePoolJ p w h B0 M Ω x R u V J W T _ Z q ν rfl rfl g u' Y); rw [sub_add_cancel] at he; exact he
#print axioms GrappleJ.applyS
#print axioms PlotGripJ
lemma GrappleJ.seasonZJ (l':ℕ)(hZ:l'≠l)(L0:finsJ)(p0:L0≠L) (T':ℝ)(g:GrappleJ (f:=f) p w h B0 M Ω x R s tP l' L0 u r Y D T') : CiriciJ P f s i k x (F-D) (ΦWallet p*(U0+ T')) tP:=by
 let A:ℕ→BandS→ Fin 6:=fun s d=> if s=l∧d=u then L.succ else claimB u l' L0 s d
 refine CirCase x f p B0 M pu i k w h pk et _ s tP _ (add_nonneg H.cost g.cost) R A ?_
 intro n V q Z v i'; let y': Fin n→P.VMark:=fun _=>x; let kP:Fin n→Signed × Bool:=fun _=>R; let b:BoardDate (Fin n):=fun i j=> A i j.2
 have hn:(L0.succ:Fin 6)≠ L.succ:= fun q=> p0 (Fin.succ_inj.mp q)
 have hu: RBuk (P:=P) (k:=k) (f:=f) l b L i' u:=by intro s a v'; change (A s u=L.succ ↔ s=l); by_cases h:s=l <;> by_cases p:s=l' <;> simp [A,h,p,claimB,Ne.symm (Fin.succ_ne_zero L),hZ,hZ.symm,hn]
 have he: RBuk (P:=P) (k:=k) (f:=f) l' b L0 i' u:=by
    intro s a v'; change (A s u=L0.succ ↔ s=l'); by_cases h:s=l
    · subst s; simp [A,hn.symm,hZ.symm]
    by_cases p:s=l'
    · subst s; simp [A,h,claimB]
    simp [A,h,p,claimB,Ne.symm (Fin.succ_ne_zero L0)]
 let t:= H.grip (Fin n) V y' kP b 0 Z v i' rfl rfl hu (fun _=>rfl); have hh:=t.minus (g.grip (Fin n) V y' kP b 0 Z v i' rfl rfl he (fun _=>rfl)); rw[LinkCutJ h x tP _ H.rise g.rise]; rw [sub_sub_sub_cancel_right] at hh; exact hh
#print axioms GrappleJ.seasonZJ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
