import GaugeFieldConstruction.AndrosJ
import GaugeFieldConstruction.AsimovJ
import GaugeFieldConstruction.DresdenJ
import GaugeFieldConstruction.FrayTideJ
import GaugeFieldConstruction.SteepleJ
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
variable (P:Spine) {X:Type}[Fintype X][LinearOrder X]
open ProbeθJ Preparation Yoke
-- Pose. Film any from Advent plus f mirrors. only valid Stamps.S.
local notation "KΑ"=>P.calibration
local notation "Kγ"=>P.par
local notation "Lγ"=> P.par.R.L
local notation "ℓν"=>P.par.R.L.val
local notation "HΥ"=> inkΛJ
variable (x:P.VMark) (f s:ℕ) (j:Axis)
open Etch
local notation "zA" s:max=> GrowJ P f s
local notation "κs"=> (GrowJ P f s:ℤ)
local notation "W_η"=> WorkWJ P f
local notation "ws"=> GrowJ P f s* WorkWJ P f
local notation "Zγ"=>Mapnest P f x
local notation "ΚΩ"=> XûJ P.par P.width f
local notation "Θζ"=> HearthJ P f s x j
local notation "Vg"=> fShiftJ P f j x
local notation "ΕΦ"=> ruler (KΑ).B
local notation "ZΩ" => pet (Mapnest P f x) j 0
local notation "ℓχ" => P.par.R.L.val
open SlabMark
local notation "qv"=> slideN P.run s (GrowJ P f s*WorkWJ P f)
local notation "Δs"=>HaloShip P x f s
local notation "α_"=> GrowJ P f s
local notation "Vq"=> (GrowJ P f s:ℤ)*fShiftJ P f j x
local notation "Vμ"=> GrowJ P f s*WorkWJ P f
variable (F:Finset Cover)(p:f≤ s)(Q:Holdκ P s f x F)
include p Q
lemma ΓHouseJ : House P.calibration ((GrowJ P f s*WorkWJ P f:ℕ):ℤ) (HearthJ P f s x j) 0 (plow P.calibration j ((GrowJ P f s:ℤ)*fShiftJ P f j x) F):=by
 let c:=Q; let R':= Vμ; let A:= HearthJ P f s x j
 have H'(i:Axis): Between P.calibration i (ruler P.calibration.B*((GrowJ P f s:ℤ)*Mapnest P f x i)) (ruler P.calibration.B*((GrowJ P f s:ℤ)*Mapnest P f x i+Vμ)) F:=by
    apply (Marrow.at_size (P:=P) (j:=i) (s:=s) (a:=(GrowJ P f s:ℤ)*Mapnest P f x i) (b:=(GrowJ P f s:ℤ)*Mapnest P f x i+Vμ) F).1
    rw[HeightGlove _ f s p,show κs * Mapnest P f x i + Vμ=κs*(Mapnest P f x i+WorkWJ P f) from (by norm_cast; push_cast; ring),HeightGlove _ f s p] -- cast ambiguity Vμ has prec
    intro a v; exact ⟨(IglooCaps P x f i).1.trans ((Q i a v).1), ((Q i a v).2).trans (IglooCaps P x f i).2⟩
 intro i; simp only [runnel,Pi.zero_apply,mul_zero,zero_add,add_zero,mul_one, HearthJ]; by_cases a:i=j
 · subst i; rw [pet_i]; have h:= Between.relocate _ j (H' j) (Vq); rw [mul_zero,mul_zero,zero_add]; unfold fShiftJ at *; convert h using 1 <;> push_cast <;> ring
 simp only [pet_j _ a,Nat.cast_mul]; intro k v; obtain ⟨z,t,rfl⟩:= plow_stays _ _ _ _ v; rw [SlabMark.moves,if_neg a]; exact H' i z t
omit p Q
lemma WarmOut_J :0< GrowJ P f s*WorkWJ P f:=mul_pos (pow_pos P.par.R.L.property _) (mul_pos (by norm_num :0<(100:ℕ)) (Nat.lt_of_lt_of_le (by decide:0<10) (NumberRK P _))) -- tune
abbrev CirrusJ (P:Spine)(f s:ℕ)(x:P.VMark)(F: ℕ→Family P.calibration)(v:ℝ)(a:ℕ→ℕ):Prop:= ∀ u:ℝ,v<u→∀ᶠ n in atTop, ShelterJ P x f (F n) s (P.gatePeriod (a n)) ∧ ∀ e:s≤ P.run.uv (P.gateCut (a n)), CiriciJ P f s (P.gatePeriod (a n)) (P.gateCut (a n)) x (F n) u e
-- sold gives slot. take slack whenever reps differ.
variable (A:ℕ→Family P.calibration)(a:ℕ→ℕ)(ht:StrictMono a)(M:P.Test)(pl:P.LongQueue F A M){v:ℝ}(h:0≤ v)(r:CirrusJ P f s x A v a)
include p Q ht pl h r
lemma ΧBoxEarnJ : ‖P.meanBox j s (GrowJ P f s*WorkWJ P f) (P.shifts j ((GrowJ P f s:ℤ)*fShiftJ P f j x) M)‖ ≤ v:=by
 refine le_of_forall_gt_imp_ge_of_dense ?_; intro u t
 let K:=P.Coheresγ a ht; have he:= ΓHouseJ P x f s j F p Q; let X:=WarmOut_J P f s
 apply P.deckProof (a:=a) (σ:=HearthJ P f s x j) (by simp [HearthJ]) pl X (h.trans t.le) he ht
 filter_upwards [K.finance s,proscenium_at P.run P.large P.law s K X,r u t] with i h p' g
 exact ΓBillJ P x f s j _ _ p h.depth g.1 h.enters p' (g.2 _) -- order check
local notation "αΟ" => P.HabBox j s (GrowJ P f s*WorkWJ P f) (P.shifts j ((GrowJ P f s:ℤ)*fShiftJ P f j x) M)
abbrev PortWJ (P:Spine)(f s:ℕ)(x:P.VMark)(j:Axis)(F:P.Test) : P.Slabs j:= P.HabBox j s (GrowJ P f s*WorkWJ P f) (P.shifts j ((GrowJ P f s:ℤ)*fShiftJ P f j x) F)
local notation "αh"=> PortWJ P f s x j M
lemma OporθJ : ‖PortWJ P f s x j M‖≤ v:=by
 have ht':= ΓHouseJ P x f s j F p Q; have hk:= P.PositionedPrice (j:=j) (by simp [HearthJ]) ht' pl.bayΛ (WarmOut_J P f s)
 change ‖(αh).val‖ ≤_; change ‖(αΟ).val‖ ≤_; rw[heard_box s hk]; exact ΧBoxEarnJ P x f s j F p Q A a ht M pl h r
lemma PointMentJ :P.Habitable j M s (P.stampPin f (Mapnest P f x j)) (P.stampPin f (Mapnest P f x j+WorkWJ P f)) (PortWJ P f s x j M):=by
 let V:=(GrowJ P f s*WorkWJ P f); let K:= (GrowJ P f s:ℤ)*Mapnest P f x j
 have ht: (GrowJ P f s:ℤ)*fShiftJ P f j x= -K:=by unfold fShiftJ; rw [mul_neg]
 unfold PortWJ; have hk:= P.PositionedPrice (j:=j) (by simp [HearthJ]) (ΓHouseJ P x f s j F p Q) pl.bayΛ (WarmOut_J P f s); rw [ht] at hk ⊢
 have hm:= Habitable.direct hk s; have he:P.stampPin s K=P.stampPin f (Mapnest P f x j):=HeightGlove P f s p _; have hq:P.stampPin s (K+V)=P.stampPin f (Mapnest P f x j+WorkWJ P f):=by rw [← HeightGlove _ f s p, mul_add]; unfold V; push_cast; rfl
 rw [←he, ←hq]; exact hm
omit ht pl h r p Q
abbrev PlethoraJ (P:Spine)(f:ℕ):ℝ:= P.stampPin f (WorkWJ P f)
lemma PadEraJ (u:Axis):P.Marrow u f ((x u:ℝ)- PlethoraJ P f) ((x u:ℝ)+ PlethoraJ P f) ∅ ∧ (x u:ℝ)- PlethoraJ P f ≤ (P.stampPin f (Mapnest P f x u):ℝ) ∧ (P.stampPin f (Mapnest P f x u+WorkWJ P f):ℝ) ≤ (x u:ℝ)+PlethoraJ P f:=by
 obtain ⟨v,z⟩:=IglooCaps P x f u; rw [P.minted_val_add] at z ⊢; unfold PlethoraJ; have he:=mul_nonneg (P.mellow_good f).le (Nat.cast_nonneg (XûJ P.par P.width f):(0:ℝ) ≤ XûJ P.par P.width f) -- tune
 refine ⟨?_, ?_,?_⟩
 · intro i h; simp at h
 all_goals linarith
#check moves
#check PositionedPrice
#print axioms ΧBoxEarnJ
#print axioms PointMentJ
#print axioms PadEraJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
