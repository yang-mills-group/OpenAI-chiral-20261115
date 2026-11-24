import GaugeFieldConstruction.SpritaFe
import GaugeFieldConstruction.GarnishFe
import GaugeFieldConstruction.Emerick
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
open Housing Flot
set_option maxRecDepth 3000
open scoped YM.CF.Mew
open BrentFe
open YM.GaugeFieldConstruction.Flavor
variable (v:BigFe)
lemma seedFe (x y:Site n)(A:Pal): seed_k x y (ageFe v A)=twist (FieldFe n v) (seed_k x y A):=by
 apply matInj; intro a b; simp_rw [mastFe,star_P]; split_ifs <;> simp
variable (o)
lemma modelFe(x y:Site n)(A:Pal)(h:ℝ):modelK o x y h (ageFe v A)= twist (FieldFe n v) (modelK o x y h A):=by unfold modelK; rw[←twist_scalar, seedFe]
lemma tower_fe(f:yardLot) : notesK o (ageFe v ∘ f) h=twist (FieldFe n v) (notesK o f h):=by simp only [notesK, Function.comp_apply,modelFe,map_sum]
variable (M:Tulip.Male)
lemma corn_fe (P:yardLot): mkD o M (ageFe v ∘ P)=ΦFeP v (mkD o M P):=by
 rw [←billMore o M (ageFe v ∘ P) (h:=1) one_ne_zero,←billMore o M P (h:=1) one_ne_zero, tower_fe,imageJFe]
private lemma fermi_part (X:Pal)(i:lotV) : ηZ (ageFe v X) i=ageFe v∘ ηZ X i:=by
 funext j; by_cases p:i=j <;> simp [ηZ,p,Pi.single_apply,p,Ne.symm]; -- tune
private lemma servo_fe (V W:PalOne):oSub (ΦFeP v V) (ΦFeP v W)=ΦFeP v (oSub V W):= by
 apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun i=>?_) (dual_uni _ _ fun i=>?_)); · exact (map_sub (ageFe v) V.1 W.1).symm
 · exact (map_sub (ageFe v) (V.2.1 _) (W.2.1 _)).symm
 exact (map_sub (ageFe v) (V.2.2.val _ _) (W.2.2.val _ _)).symm
lemma fieldFe (P:PalOne):fieldX M o (ΦFeP v P)=ageFe v ∘ (fieldX M o P):=by
 have hV(T:PalOne):Ωlane (ΦFeP v T)=ageFe v ∘ Ωlane T:=fermi_part ..
 have hY(T:PalOne):Ωleg (ΦFeP v T)=ageFe v ∘ Ωleg T:=by
    funext i; unfold Ωleg; rw [Function.comp_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j _; change pinD _ ((-Complex.I) • ageFe v _) _= _; unfold pinD; rw [←twist_scalar]; simp only [fermi_part,Pi.sub_apply,map_sub]; try rfl
 have he(T:PalOne):grainD (M:=M) o (ΦFeP v T)=ΦFeP v (grainD (M:=M) o T):=by unfold grainD; rw[hV,corn_fe, servo_fe]
 have hx:gainT (M:=M) o (ΦFeP v P)=ΦFeP v (gainT (M:=M) o P):=by unfold gainT; rw [he,hY,corn_fe,servo_fe]
 have hQ(T:PalOne): Ωray (ΦFeP v T)=ageFe v∘Ωray T:=by
    funext i; unfold Ωray; rw [Function.comp_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j _; change spinD _ _ ((-1/2:ℂ) • ageFe v _) _= _; unfold spinD; rw [←twist_scalar]; simp only [fermi_part,Pi.sub_apply,map_sub]; try rfl
 unfold fieldX; rw [hx,he,hY,hV,hQ]; ext1 i; simp only [Pi.add_apply,Function.comp_apply,map_add]
lemma beamFe (k:lotV)(A:Pane n→Pal)(V:Pane n): beamer o k (ageFe v ∘ A) h V=twist (FieldFe n v) (beamer o k A h V):=by unfold beamer carryU; rw [←modelFe]; simp only [LedgeK,Function.comp_apply,map_mul,map_star,spot_F]
lemma αPureFe (F:Waves): αPureX o M p (SpinFe v F)=ageFe v ∘ αPureX o M p F:=fieldFe ..
lemma GuideFe(t:20<n.val)(u:0<h)(x:p.power≤3)(l:p.order ≤6)(V:Waves) : αGuide o M p (SpinFe v V) h=(τoneFe v).comp (αGuide o M p V h):=by
 let Y:=SpinFe v V; let Z:=αPure o M p Y h; let L:=αPure o M p V h
 have hζ(U: Pane n): orbitPH (Z U)=twist (FieldFe n v) (orbitPH (L U)):=by
    have ht(K:Waves):αPure o M p K h U=∑ i: lotV, viewW o i (fun _=>αPureX o M p K i) h U:=by unfold αPure blurred; rw [Finset.sum_apply]
    unfold Z L; rw [ht,ht,Sour.Glyph.ps_k,Sour.Glyph.ps_k,map_sum]; apply sum_congr rfl; intro i _; rw [ph_caps,ph_caps,show αPureX o M p Y= _ from αPureFe ..]; exact beamFe ..
 have hx: landA M o Z p h=(τoneFe v).comp (landA M o L p h):=by
    apply ContinuousLinearMap.ext; intro i; let U(t:ℝ):=increment 1 (t • gateC o p.threshold i)
    apply HasDerivAt.unique (landR (o:=o) M (suit_P o M u Y x l t) i)
    let P:= (τoneFe v).hasFDerivAt.comp_hasDerivAt 0 (landR (o:=o) M (suit_P o M u V x l t) i); exact P.congr_of_eventuallyEq (Eventually.of_forall fun j=>by change sectorJ (orbitPH (Z _)) _ _ _= _; rw [hζ]; exact congrArg Prod.fst (imageJFe ..))
 apply ContinuousLinearMap.ext; intro i; unfold αGuide; rw [SpinFe_m,show landA _ _ _ _ _= _ from hx]; exact (map_sub (ageFe v) ((bm5 V).val i) (landA M o L p h i)).symm
lemma malletFe(k:GateI)(T:ComG→L[ℝ]Pal):mallet o ((τoneFe v).comp T) p k=ageFe v ∘ mallet o T p k:= rfl
end Layout
end Lenten
end YM.CF.TableF
end
