import GaugeFieldConstruction.ZucatoJ
import GaugeFieldConstruction.KronenJ
import GaugeFieldConstruction.MapicoJ
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
open JetCurry JetCurry.TrekJ Frugal
variable (r:BoonsθJ p B0 M i k w h)
variable (x:P.VMark)(R:Signed × Bool)(u:BandS)
variable {W: Pathsθ X}{d0:X}{B: SailκJ X θ→ Waves}{J:X→Signed × Bool}{T:BoardDate X}
variable (Z:PlumberJ P.run i k X θ)(pv:p.PlateZ w h T W (incA θ J B0) (incG θ M) B Z f)
variable (U:ℕ→ Shape)(v:Bool)(s0:ℕ)(ph: PanB (i:=i) (k:=k) (W:=W) x R d0 v U s0 J)(n:s0 ≤P.run.uv k) (a:f≤ s0)
local notation "jχ" => pointlet d0
local notation "jκ"=> OrbitSailJ θ jχ
local notation "Ζw" s:max=>Levier.ray (N:=Papal.count P.run s i) v (U s)
local notation "℘"=> ((),u)
local notation "Zg"=> P.Ptherm
-- choose mask of all PC, optionally activate one Lane even after v; requires tailU 0 on relevant.
open TableF.Lenten
#check sheen_a
variable {m s t l:ℕ}
open ProbeθJ Preparation Yoke
local notation "Tω"=> StampCK p w h B0 M r x R u
local notation "Vω" a:max v:max=> Glowζ p w h B0 M r x R u a v
local notation "RankΓ" s:max=> RankQJ P.par s
local notation "μ0"=> ScaleμJ P.par u.val
local notation "Xκ"=> Fin (θ u)
local notation "ΙΠ_"=> P.par
local notation "Tη"=> ΓFoil P.run i k P.large θ T W (incA θ J B0) (incG θ M) B Z (d0,u)
local notation "Pς"=> ΓPrimary P.run i k θ Z (d0,u)
local notation "TL" L:max=> ΓSig P.run i k P.large θ T W (incA θ J B0) (incG θ M) B Z (d0,u) L
local notation "Sυ"=> ΟGlow (U f) v P.par
local notation "ΚΩ" => hoodAJ (ΟGlow (U f) v P.par)
-- Ghost P_s target in layout, for s potentially earlier.
def OrbitLO (p0:s ≤ m) (y:FrameK (Fin (θ u))) : Mark (side P.run i (P.run.uv k)) := (ΓPrimary P.run i k θ Z (d0,u)) m (hoodAJ (ΟGlow (U f) v P.par) ((PlcJ m s (StampCK p w h B0 M r x R u) p0) y))- (ΟGlow (U f) v P.par) ((AcJ (StampCK p w h B0 M r x R u) m s p0) y) • 1
-- use f implicit w/ notation.Reli.
local notation "ΩΠ" => OrbitLO
abbrev SunLO (s:ℕ)(y:FrameK (Fin (θ u))) := OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v (le_max_left s f) y -- at m=max
variable (ϑ:PanB (i:=i) (k:=k) (W:=W) x R d0 v U f J)
include pv ϑ
lemma PSΧ (m m':ℕ)(p0:s ≤ m)(p1:m ≤ m')(s1:f≤ m)(q:m'≤ P.run.uv k)(y: FrameK (Fin (θ u))) : OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v p0 y=OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v (p0.trans p1) y:=by
 let C:= Tω; let D:= Tη; let H:= hoodAJ (E:=Fin (θ u)) Sυ; let v0:= PlcJ m s C p0 y
 have a:= IntersectΦ C p0 p1 y; let b':= Prism_J p w h B0 M r x R u Z pv U v f ϑ le_rfl; have t:=billΦ Sυ C D b' m m' s1 p1 q
 -- after Path
 have gg:JiveJ Sυ (PlcJ m' m C p1) (PlcJ m' m D p1):= by have hh:= t.1; rw [DownL,DownL] at hh; exact hh -- rcases dotted expanded trouble
 let Q':= ProbeθJ.Art P.run i k f f0 _ _ _ _ _ _ _ P.large θ _ _ _ _ _ _ _ (d0,u) pv
 change (Pς) m (H v0)- Sυ (AcJ C m s p0 y) • 1= (Pς) m' (H _) - Sυ (AcJ C m' s (p0.trans p1) y) • 1; rw[a.1,a.2,map_add, add_smul, show H _ = _ from gg v0, PathJ _ D f m' m _ (Pς) Q' s1 p1 q _]; change _= _ - (Sυ (AcJ C m s p0 y) • 1+Sυ (AcJ C m' m p1 v0) • 1); rw [show Sυ (AcJ C m' m p1 v0) = _ from t.2 v0]; unfold AcJ; abel
local notation "Υθ"=> p.price
-- checker charges.Cφ on layout at f. Geometric broad.
lemma outΦt (z:s≤ f)(a:f0≤ s)(v0:FrameK (Fin (θ u))): Circζ P.run i k θ Z f d0 (SunLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v s v0) (2*RankQJ P.par s*(RStepJ P.par u.val)^(f-s)*LoomK v0):=by
 have t:= p.price f0 le_rfl u (ΓΥ); let H:= hoodAJ (E:=Fin (θ u)) Sυ; have eqY (q:ℕ)(v':s ≤ q)(p0:q=f): OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v v' v0=OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v z v0:=by subst q; rfl
 unfold SunLO; rw [eqY _ _ (max_eq_right z)]
 let A:=PlcJ f s (Tω) z v0; let C:=AcJ (Tω) f s z v0
 have hC:= primAJ P.run i k f θ Z (d0,u) (H A)
 have ht:= ChargedJ.one (x:=d0) (c:= RankQJ P.par f) (M:=Z.Mark f) (F:=TolHouseJ θ) -- tune namespace
 refine ((hC.minus (ht.smul ((Sυ) C))).lift ?_)
 change LoomK ((hoodAJ _ A):FrameK (Fin (θ u)))*RankQJ P.par f + ‖ΟGlow (U f) v P.par C‖*1 ≤ _; rw[J_costH,(Οinvo _ _ _ C).2,mul_one]
 let R':=RStepJ P.par u.val; let S₀:=stepRateJ P.par u.val; let k':= LoomK v0; let y:= RankQJ P.par s; let n:= f-s; have Ht:= ζAccum _ (Tω) f0 f s _ (StripeH p w h B0 M r x R u) t a z pv.qk; let B:=y*R'^n*k'; have hw:‖C‖≤B:=Ht.2.2.2.2 v0 -- tune count projections
 have he:LoomK A*RankQJ P.par f ≤ B:=by
   have hb: 0≤ S₀:=zero_le_one.trans t.bound; refine ((mul_le_mul_of_nonneg_left Ht.2.2.2.1 (noLoom A)).trans ((mul_le_mul_of_nonneg_right (Ht.1 v0) (mul_nonneg (pow_nonneg (by norm_num) _) (t.hot a (z.trans pv.qk)).le)).trans ?_)) -- positivity y t?
   have hy:0≤ y:=(t.hot a (z.trans pv.qk)).le; have hm:0≤ k':=noLoom v0; unfold B; change S₀^n * k' * (2^n * y) ≤ y*R'^n*k'
   have he:= pow_le_pow_left₀ (show 0≤2*S₀ from mul_nonneg (by norm_num) hb) t.θpay n; rw[mul_pow] at he; rw [show S₀^n*k'*(2^n*y)=y*(2^n*S₀^n)*k' by ring]; apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hy) hm
 refine (add_le_add he hw).trans_eq ?_; unfold B y R' n k'; ring
lemma outΦs (z:f≤ s)(a:s≤ P.run.uv k)(v0:FrameK (Fin (θ u))): Circζ P.run i k θ Z f d0 (SunLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v s v0) (LoomK v0*RankQJ P.par s):=by
 let H:= hoodAJ (E:=Fin (θ u)) Sυ
 suffices hE: SunLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v s v0= (Pς) s (H v0) by
    rw[hE]; have hK:= qRoadJ (W:=(d0,u)) s pv (p.price _ pv.io u _) z a (hoodAJ (ΟGlow (U f) v P.par) v0); rwa [J_costH] at hK
 have eqY (q:ℕ)(v':s ≤ q)(p0:q=s): OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v v' v0=OrbitLO (d0:=d0) (f:=f) p w h B0 M r x R u Z U v (show s ≤ s from le_rfl) v0:=by subst q; rfl
 unfold SunLO; rw [eqY _ _ (max_eq_left z)]; unfold OrbitLO; rw [Plc_self,Ac_self,LinearMap.zero_apply,map_zero,LinearMap.id_apply,zero_smul,sub_zero]
#check PSΧ
#print axioms PSΧ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
