import GaugeFieldConstruction.LevPlotS
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
variable {P:Spine}
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.

local notation "ΤΓ"=> P.run
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (x:P.VMark)(R:Signed × Bool)(u:BandS)
local notation "Ξu"=> Fin (θ u)
local notation "η"=> FrameK (Fin (θ u))
variable (pu:Adept_T θ B0 M G)
-- Flexible anchor representation. stores assertion on arbitrary Movement Words.May align proofs of R3 via composition. KeyScope.S.
variable (L:finsJ)
local notation "Υs"=> ScaleμJ P.par u.val
-- CASH in force p P through procurement. preservation under Delayed (single.U)
local notation "ΚΡ"=> CalendarJ p B0 M
variable (A: CalendarJ p B0 M)
-- price limits of approximants.Any other heights at same point even with multiple gaps.N.Helper loan.
variable (T:LampHouseJ (θ:=θ) u) (D:P.Heritor)(V:LampΤJ p B0 M x R u A T D.path)
local notation "Zγ"=> FrameK (Fin (θ u))
local notation "ι" i:max=> D.path.subSeq i
local notation "gp" i:max=> P.gatePeriod (D.path.subSeq i)
local notation "gq" i:max=> P.gateCut (D.path.subSeq i)
local notation "βζ"=> FlavorRateJ P u
local notation "Κg"=> ΦWallet p
variable {f s l:ℕ}(g:f0≤ f)(s0:f0 ≤ s)
-- Portrait in all Habitat pads at Slabs.Location.Mar.K.Kernel.
local notation "νP" => RankQJ P.par
local notation "Kρ"=> p.price
local notation "gR" => RStepJ P.par
local notation "βρ" => stepRateJ P.par u.val
variable (σ τ:PermWallJ P) (i:Axis)(v:FrameK (Fin (θ u)))
open BoonsθJ Gleam BProof BProof.PricePort Gleam.Guide Gleam.clocks
open Fock.Flux
variable {d m:ℕ}
-- convergence along Rescale. Hom movement & spin. Mach anti.S. two/trio into Rank.P.R.
open CF.XGarden.MastTin.ArtCart.BluffV.Lave BluffV BluffV.Fables
open CF.Levier CF.Spire
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open GaugeFieldConstruction GaugeFieldConstruction.Phys Calibration Calibration.Floor
open SpaΘ
variable (Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u': TintDemand)(H: LicensedHeight (tagged_B Q) t u' P.par)
variable (m:ℕ){L:ℕ→ℕ}{a b:Genre}{d d':GaugeFieldConstruction.Calibration.Floor}{X Y:Waves}
local notation "kτ" f:max=> mount ((Richm_R P m f)⁻¹)
open Heritor Gap Raster
variable (pL:Tendsto L atTop atTop)
open SelectionAnalysis
namespace SignetS
open InterR Shower
variable {n:ℕ}
open Classical MeasureTheory
lemma stanceOrbit_R {I:Type}{x:DiagramR I}(p:x∈ MasksR I): x∈ CardsR I:=Set.mem_iUnion.mpr ⟨0,p 0⟩
lemma Pplot_dS (n:ℕ) : Dense (MasksR (Fin n)):=by
 have he:P_Esc n=generic n:=rfl
 have h': Dense (P_Esc n):=Measure.dense_of_ae (P_Efull n) -- tune
 rw[dense_iff_closure_eq] at h' ⊢
 apply top_unique; intro x e; change x∈ closure _; let y:=points (fun i=> WithLp.toLp 2 (x i)); have hv : y∈ closure (P_Esc n):=by rw [h']; exact Set.mem_univ _
 have hp:= _root_.image_closure_subset_closure_image (s:=P_Esc n) (ΦlegR n) (show x∈ ΦplanR n '' closure (P_Esc n) from ⟨y,hv,rfl⟩)
 exact closure_mono (Set.image_preimage_subset ..) hp
lemma masks_denseκ (P:Spine)(n:ℕ) : Dense (MasksR (Fin n) ∩ Set.range (AskR (I:=Fin n) P)):= (Pplot_dS n).inter_of_isOpen_left (SelectionAnalysis.Repertoire.clear_dense) (ply_openR _) -- tune
lemma MeshPhoto_S (P:Spine)(x:DiagramR (Fin n))(u:Set (DiagramR (Fin n)))(e:IsOpen u)(g:x∈u):∃ A:ℕ→Fin n→P.VMark, Tendsto (fun i=>AskR P (A i)) atTop (𝓝 x) ∧ ∀ i, AskR P (A i)∈ u ∩ MasksR (Fin n):=by
 let T:= u ∩ (MasksR (Fin n) ∩ Set.range (AskR (I:=Fin n) P)); have hp:x∈ closure T:=by
    apply _root_.mem_closure_iff.mpr; intro v t z; obtain ⟨y,h,w⟩:= (masks_denseκ P n).inter_open_nonempty (u∩v) (e.inter t) ⟨x,g,z⟩ -- order tune
    exact ⟨y,h.2,h.1,w⟩
 obtain ⟨y,v,d⟩:=mem_closure_iff_seq_limit.mp hp
 choose p h using (fun i=>(v i).2.2)
 exact ⟨p,d.congr fun i=>(h i).symm,fun i=>(h i).symm ▸ (And.intro (v i).1 (v i).2.1)⟩ -- tune
lemma AlongMesh_S {x:DiagramR (Fin n)} {M:Type*}[TopologicalSpace M][T2Space M] (F G: DiagramR (Fin n)→M)(P:Spine)(e:ContinuousOn F (CardsR (Fin n)))(h:ContinuousOn G (CardsR (Fin n)))(p:x∈ CardsR (Fin n))(u:∀ A:Fin n→ P.VMark, AskR P A∈ MasksR (Fin n)→F (AskR P A)=G (AskR P A)): F x=G x:=by
 obtain ⟨a,v,g⟩:= MeshPhoto_S P x _ (prosc_R (Fin n)) p
 let X:=fun i=> AskR P (a i); have ht:Tendsto X atTop (𝓝[(CardsR (Fin n))] x):=tendsto_nhdsWithin_iff.mpr ⟨v,Eventually.of_forall (fun i=>(g i).1)⟩
 exact tendsto_nhds_unique_of_eventuallyEq ((e x p).tendsto.comp ht) ((h x p).tendsto.comp ht) (Eventually.of_forall fun i=> u _ (g i).2)
-- price multilinearity now all Kernel Real. set Bart.Move.Up // all characters and mean.
section ensemble
variable (C:CoinsR P)
local notation "F" => SπR C.porch
abbrev EarlyAll_S (Z:Submodule ℂ (ScreensJ P)):Prop:=∀ A:Z, AttainedR 0 A.val
lemma SπTankS (i:Axis)(A B:P.Slabs i)(z:ℂ) : VirtueJ C.porch i (z • A+B)=z*VirtueJ C.porch i A+VirtueJ C.porch i B:= Vfoot i _ z A B
lemma SπZeroS (i:Axis): VirtueJ C.porch i 0=0:=by unfold VirtueJ; rw [map_zero]; simp
private lemma tuvloanS(i:Axis)(x:P.VMark)(A B:P.Slabs i)(z:ℂ) :P.ambientTurn i x (z • A+B)=z • P.ambientTurn i x A+ P.ambientTurn i x B:=by unfold ambientTurn; rw [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
set_option synthInstance.maxHeartbeats 160000
variable (Z:Submodule ℂ (ScreensJ P))(eA:EarlyAll_S Z)
abbrev SumBill_S (x:DiagramR (Fin n))(A:Fin n→Z) :ℂ:= SπR C.porch (fun i=>(A i).val) x
section work
local notation "Kx"=> SumBill_S C Z
-- on Sweeps before comps.
private lemma bagR_S (L:List (Fin n))(A B:Fin n→P.Slabs i)(h:∀ j∈L,A j=B j)(x:Fin n→ P.VMark)(σ:Fin n→PermWallJ P)(r:Option ℝ): SweepR i σ x L r A= SweepR i σ x L r B:=by
 induction L generalizing r with
 | nil=>rw[SweepR,SweepR]
 | cons k l ih=> rw[SweepR,h k (List.mem_cons_self ..),ih (fun j t=>h j (List.mem_cons_of_mem _ t)),SweepR]; rfl
private lemma SweepSκ (i:Axis)(L:List (Fin n))(A B C:Fin n→P.Slabs i)(x:Fin n→ P.VMark)(σ:Fin n→ PermWallJ P)(r:Option ℝ)(j:Fin n)(z:ℂ)(h:A j=z • B j+C j)(t:∀ k:Fin n,j≠k→ A k=B k∧B k=C k)(p:L.Nodup)(u:j∈L) : SweepR i σ x L r A=z •SweepR i σ x L r B+SweepR i σ x L r C:=by
 induction L generalizing r with
 | nil=> simp at u
 | cons k l ih=>
   obtain ⟨v,w⟩:=List.nodup_cons.mp p; let X:=StageR σ (P.publicH i) A; let r':= some (X.endline (AskR P x k) k); let T:= P.Eucl i (X.sep r k (AskR P x k)); let W:= SweepR i σ x l r'; change T * A k * W A=z • (T*B k* W B)+T*C k* W C
   rcases List.mem_cons.mp u with u|u
   · subst j; have ht(y:Fin n)(x:y∈l):k≠ y:=fun i=> v (i.symm ▸ x); rw [h, show W A=W B from bagR_S i l A B (fun i a=> (t _ (ht _ a)).1) x σ r',show W C=W B from bagR_S i l C B (fun i a=>(t _ (ht _ a)).2.symm) x σ r']; rw[mul_add,add_mul, mul_smul_comm,smul_mul_assoc] -- arguments needed
   have he:j≠k:= fun p=>v (p ▸ u); rw [(t k he).1, show C k=B k from (t k he).2.symm,show W A=z •W B+ W C from ih r' w u,mul_add,mul_smul_comm]
local instance modR_S: Module ℂ (↥Z):= Submodule.module Z
local instance addR_S: AddCommGroup (↥Z):= Submodule.addCommGroup Z

include eA
lemma ΚPlusS (x:DiagramR (Fin n))(A:Fin n→Z)(i:Fin n)(a b:Z)(w:ℂ): SumBill_S C Z x (Function.update A i (w • a+b))=w*SumBill_S C Z x (Function.update A i a)+SumBill_S C Z x (Function.update A i b):=by
 by_cases e:x∈ CardsR (Fin n); swap; · unfold SumBill_S; rw [perim_R _ _ e,perim_R _ _ e,perim_R _ _ e,mul_zero,zero_add]
 let G (a:Z)(l:DiagramR (Fin n)):= SumBill_S C Z l (Function.update A i a)
 have hz(a:Z):ContinuousOn (G a) (CardsR (Fin n)):= groundPlotR C.porch _ (fun _=> eA _)
 apply AlongMesh_S (G (w • a+b)) (fun x=>w*G a x+G b x) P (hz _) ((continuousOn_const.mul (hz a)).add (hz b)) e
 intro x h; let Y:=AskR P x; obtain ⟨L,σ,T,K⟩:=OpenTollR P (h 3); let J(a:Z):=legR 3 x (BodyΘ P (fun j=>(Function.update A i a j).val) 3 σ); let U:=SweepR 3 σ x L none
 have hx(a:Z):G a Y=VirtueJ C.porch 3 (U (J a)):= S_rawMeshR C.porch 3 σ x L _ (fun i=>eA _) T K h -- fill
 rw [show (G _ (AskR P x))=_ from hx (w • a+b), show G a _= _ from hx a, show G b _=_ from hx b]
 have he: U (J (w • a+b))=w • U (J a)+U (J b):=by
    apply SweepSκ 3 L _ _ _ x σ none i w _ _ T.1 (T.2 i)
    · unfold J legR BodyΘ; simp only [Function.update_self,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply]; rw [tuvloanS ..]
    intro k p; unfold J legR BodyΘ; simp_rw [Function.update_of_ne (Ne.symm p)]; tauto -- tune Update classical instance mismatch
 rw[he,SπTankS C]
#print axioms ΚPlusS
end work
end ensemble
end SignetS
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
