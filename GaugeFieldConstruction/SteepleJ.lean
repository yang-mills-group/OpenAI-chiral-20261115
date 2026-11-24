import GaugeFieldConstruction.MovingH
import GaugeFieldConstruction.ZagoraJ
import GaugeFieldConstruction.VirenneJ
import GaugeFieldConstruction.TrollopJ
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
variable (L:finsJ) {q:ℕ} (pT:f0 ≤ q) (uT:q≤ P.run.uv k)
local notation "Γ_ν"=> Sunγ p w h B0 M r x R u L q
local notation "K_"=> incA θ J B0
local notation "OΛ"=> (hoodAJ (ΟGlow (U f) v P.par))
open Buffered.Afterglow
lemma JuMark (s m:ℕ)(Z:Cover)(w:Waves): P.Araw s Z m ((RankQJ P.par s:ℂ) • w)= Justin P.run (P.gatePeriod m) (P.gateCut m) s Z w P.large:=rfl -- p par via P infer auto.G
lemma ΤCostJ (P:Preparation)(z:ℂ)(v:LaurelJ)(d:ProngJ): let X (s:LaurelJ):ℂ→+*ℂ:= ΟGlow (wayZJ P f f s) false P; X (d::v) z= Star.star (X v z):=by
 intro X; unfold X ΟGlow; rw [inkPay,inkPay]; let R:= wayZJ P f f v
 change cSignX (false ^^ detX (R.s*Signed.mirror d.1)) z= Star.star (cSignX (false ^^ detX R.s) z); rw [det_p,det_t]; cases detX R.s <;> simp [cSignX]
#check inkPay
#check payZ
lemma VivaSub(P:Preparation)(j i:ℕ)(v:LaurelJ)(k:Calibration)(F G:Buffered.Family k): VivaJ P j i k v (F-G)= VivaJ P j i k v F-VivaJ P j i k v G:=by
 induction v with
 | nil=>rfl
 | cons a l ih=> change mirror k _ _ (VivaJ P j i k l (F-G))= mirror k _ _ _ - mirror k _ _ _; rw [ih]; simp only[sub_eq_add_neg]; nth_rw 1 [← neg_one_smul ℂ (VivaJ P j i k l G)]; rw [mirror_plus,mirror_scale]; simp
lemma VivaSum (P:Preparation)(j i:ℕ)(v:LaurelJ)(k:Calibration){E:Type}(l:Finset E)(F:E→Buffered.Family k): VivaJ P j i k v (∑ x∈l,F x)= ∑ x∈l,VivaJ P j i k v (F x):=by
 have H(r:Finset E)(m:Axis)(z:ℤ)(F:E→Family k): mirror k m z (∑ x∈r,F x)= ∑ x∈r,mirror k m z (F x):=by
    induction r using Finset.induction_on with
    | empty=>rw [sum_empty,sum_empty]; have ht:=mirror_scale k m z (F:=1) 0; simpa using ht
    | insert s r q ih=> rw [sum_insert q,sum_insert q,mirror_plus,ih]
 induction v with
 | nil=>rfl
 | cons a l' ih=>change mirror k _ _ (VivaJ P j i k _ _)=_; rw [ih]; exact H ..
lemma VivaScale(P:Preparation)(j i:ℕ)(v:LaurelJ)(k:Calibration)(F:Buffered.Family k)(a:ℂ): VivaJ P j i k v (a • F)=(ΟGlow (wayZJ P j j v) false P a) • VivaJ P j i k v F:=by
 induction v with
 | nil=>
   change a • F = (ΟGlow (incX 1) false P a) • F -- tune
   unfold ΟGlow; rw [inkPay]; change a • F = cSignX (false ^^ detX 1) a • F
   rw [det_i]; rfl
 | cons x v ih=>change mirror k x.1 _ (VivaJ P j i k v (a • F))=_; rw [ih,mirror_scale]; exact congrArg (fun z:ℂ => z • (VivaJ P j i k (x::v) F)) (ΤCostJ (f:=j) P a v x).symm -- Tune
lemma VivaOne(P:Preparation)(j i:ℕ)(v:LaurelJ)(k:Calibration): VivaJ P j i k v (1:Family k)=1:=by
 induction v with
 | nil=>rfl
 | cons a l ih=> change mirror k _ _ (VivaJ P j i k l 1)=_; rw[ih,mirror_unit]
variable (v:LaurelJ) -- v Bool above duplicated shadow
local notation "Γd" s:max=>forgeιJ P.par f s v
open Jubilee
-- align precomputed rotated slot types themselves. reflect true.
abbrev KnitBJ (P:Preparation)(f:ℕ)(z:LaurelJ)(u:Signed × Bool):Signed × Bool:= (u.1*(wayZJ P f f z).s,u.2)
abbrev ThreadΨ (M:SωJ θ)(u:BandS)(Z: Signed × Bool):Fin (θ u)→ Waves:= (incA θ (fun _:Unit=>Z) M 0 ((),u))
variable {x0:Cover}
lemma Lady_Th (d:ProngJ)(A:Shape)(j:Fin (θ u)) : ThreadΨ B0 u (KnitBJ P.par f (d::v) R) j = sheen (Signed.mirror d.1) false (ThreadΨ B0 u (KnitBJ P.par f v R) j):=by
 unfold ThreadΨ KnitBJ incA; rw [sheen_a]; change sheen (R.1*((wayZJ P.par f f v).s*Signed.mirror _)) R.2 _ = sheen ((R.1*_)*_) (R.2 ^^ false) _; rw [mul_assoc]; simp -- flip z
local notation "ΚΨ"=> ThreadΨ
lemma VeraRoof (s m:ℕ)(i':Fin (θ u)): VivaJ P.par f s P.calibration v (Justin P.run (P.gatePeriod m) (P.gateCut m) s x0 (ThreadΨ B0 u R i') P.large)= Justin P.run (P.gatePeriod m) (P.gateCut m) s ((forgeιJ P.par f s v).motion x0) (ThreadΨ B0 u (KnitBJ P.par f v R) i') P.large:=by
 induction v with
 | nil=>simp [VivaJ,KnitBJ,forgeιJ,wayZJ,Shape.motion,incX]
 | cons a l ih=>
    let F:=forgeιJ P.par f s l; let W:=(ThreadΨ B0 u (KnitBJ P.par f l R) i'); let y:= F.motion x0; let d:=globeJ P.par f s a; let U:= plane a.1 d; have he: (forgeιJ P.par f s (a::l)).motion x0=U.motion y:= palm ..
    have hz:U.motion (U.motion y)=y:=by rw [← palm,show joinX U U=incX 1 from gaugeSquare a.1 d]; simp [incX,Shape.motion]
    change mirror P.calibration a.1 d (VivaJ P.par f s P.calibration l _)= _
    rw [ih,←JuMark (P:=P),he, ← JuMark (P:=P) s m (U.motion y), Lady_Th B0 R u l a U i']
    let o:=RankQJ P.par s; let W':=(o:ℂ) • W
    rw[P.rawMirror a.1 d s m (U.motion y) y hz]
    unfold cargoν Fren.Mason; change (P.Araw ..) (sheen (Signed.mirror a.1) false W')= _ -- tune
    unfold W'; rw [sheen_p,det_t,show cSignX (false ^^ true) (o:ℂ)=(o:ℂ) from (by simp [cSignX])]
#check Lady_Th
lemma vivaRoof_T (s m:ℕ)(Z: FrameK (Fin (θ u))): VivaJ P.par f s P.calibration v (PaperPanelJ P.run P.large x0 (ThreadΨ B0 u R) s (P.gatePeriod m) (P.gateCut m) Z)= PaperPanelJ P.run P.large ((forgeιJ P.par f s v).motion x0) (ThreadΨ B0 u (KnitBJ P.par f v R)) s (P.gatePeriod m) (P.gateCut m) (hoodAJ (ΟGlow (wayZJ P.par f f v) false P.par) Z):=by
 change VivaJ P.par f s P.calibration v (∑ i':Fin (θ u), Z i' • _) = (_: Family _); rw [VivaSum]; unfold PaperPanelJ; refine Finset.sum_congr rfl fun j _=>?_ ; rw [VivaScale,VeraRoof]
lemma StepΩJ (s m:ℕ)(Z: FrameK (Fin (θ u)))(b:ℂ): VivaJ P.par f s P.calibration v (PasteJ P.run (P.gatePeriod m) (P.gateCut m) P.large (r:=s) x0 (ThreadΨ B0 u R) Z b)= PasteJ P.run (P.gatePeriod m) (P.gateCut m) P.large (r:=s) ((forgeιJ P.par f s v).motion x0) (ThreadΨ B0 u (KnitBJ P.par f v R)) (hoodAJ (ΟGlow (wayZJ P.par f f v) false P.par) Z) ((ΟGlow (wayZJ P.par f f v) false P.par) b):=by rw [PasteJ,VivaSub,vivaRoof_T,VivaScale,VivaOne]
#print axioms StepΩJ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
