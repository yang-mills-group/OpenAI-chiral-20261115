import GaugeFieldConstruction.LyricBeltNX
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
-- actual Coalition: one spine/view/archive, one registration, one path, and APPROVED solicitation of orientation frame and dynamics. Predicate open Badge to allow further needs while preserving same purchases.
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune
namespace Glaze
variable {P:Spine}{i:Axis}{s t w:ℕ}
local notation "Ζp" => ruler P.par.block
local notation "χ"=>P.stampPin t
local notation "Nt"=> timeMesh P.par
-- not split before reaching Belt!
variable {A D:P.Glaze}(p:A.w≤w)(q:D.w≤w)
local notation "o₀"=> pinOut w
local notation "m₀"=> pinPay w
local notation "N"=> (χ (m₀:ℤ):ℝ)
local notation "M"=> (χ (w:ℤ):ℝ)
local notation "Mτ"=> (χ ((w:ℤ)+1):ℝ)
local notation "X" => belt p q
local notation "uP"=>pinDiagonal w
local notation "θP"=>P.vtile t uP
local notation "ψ"=> P.grantGapNX i t
lemma civicBeltNX : ψ (X).w (X).F N N= ψ A.w A.F N Mτ * P.ambientTurn i θP (ψ D.w D.F M M):=by
   have he:= A.ownsTokenNX (l:=m₀) (r:=(w:ℤ)+1) (by unfold pinPay; omega) (by omega) (i:=i) (t:=t)
   have ht:= habit_tokenS (P:=P) i (D.ownsTokenNX (l:=w) (r:=w) (by omega) (by omega) (t:=t)) uP
   have ha: -χ (w:ℤ) + θP i=χ ((w:ℤ)+1):=by change -notch Nt t (w:ℤ)+ notch Nt t _= _; rw [show uP i=(w:ℤ)+(w+1:ℤ) from by unfold pinDiagonal pinOut; omega,notch_add]; abel
   have hx: χ (w:ℤ) + θP i =χ (m₀:ℤ):=by rw[show χ _ + θP i= notch Nt t (w:ℤ)+ notch Nt t o₀ from rfl,←notch_add]; unfold stampPin; congr 1; unfold pinPay; omega
   have hk:= (X).ownsTokenNX (l:=m₀) (r:=m₀) le_rfl le_rfl (i:=i) (t:=t)
   apply hk.twins; refine HabitPairNX he (show P.HabitLevel i (P.chartAll uP D.F) t _ _ _ _ from (?_ : P.HabitLevel i _ t (χ ((w:ℤ)+1)) (χ (m₀:ℤ)) _ t)); rw [←ha,←hx]; exact ht
lemma ambient_hearthNX(v:P.VMark)(l:ℝ):P.ambientTurn i v (P.hearthNX i l)=P.hearthNX i l:=by unfold hearthNX ambientTurn; rw[transit_share,mul_assoc,←transit_plus,add_neg_cancel,transit_zero,mul_one]
lemma BeltMothersNX(A:P.Glaze){a b c d:ℝ}(p:P.tock t A.w ≤ a)(q:a≤b)(h:P.tock t A.w ≤ c)(v:c≤d): ‖ψ A.w A.F b d‖ ≤ ‖ψ A.w A.F a c‖:=by
    rw [grantStretchNX i t A.w A.F p h q v]; exact (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans (mul_le_mul (P.hearthBudgetNX ..) le_rfl (norm_nonneg _) zero_le_one)) (P.hearthBudgetNX ..) (norm_nonneg _) (by positivity)).trans_eq (by ring)) -- tune
lemma BudgetBeltNX(l r:ℝ)(b:N ≤ l)(e:N ≤r): ‖ψ (X).w (X).F l r - ψ A.w A.F l r‖ ≤ ‖ψ A.w A.F M M‖*‖ψ D.w D.F M M-P.hearthNX i (M+M)‖:=by
    have he:P.tock t A.w ≤ M:= (minted_le _ _ _ _).mpr (by omega); have ht: M≤ N:= (minted_le _ _ _ _).mpr (by unfold pinPay; omega)
    have hx:Mτ ≤ N := (minted_le _ _ _ _).mpr (by unfold pinPay pinOut; omega); have hv: M ≤ Mτ:=(minted_le _ _ _ _).mpr (by omega)
    have hZ:N-Mτ=M+M:=by rw [show (pinPay w:ℤ)=(w:ℤ)+1+(w+w:ℤ) by unfold pinPay pinOut; omega,P.minted_val_add,P.minted_val_add t (w:ℤ) (w:ℤ)]; abel
    have hL:P.hearthNX i 0=1:=Subtype.ext ((P.publicH i).Time.wax_zero) -- tune
    have hp': ψ A.w A.F N N= ψ A.w A.F N Mτ * P.ambientTurn i θP (P.hearthNX i (M+M)):=by
       rw [grantStretchNX i t A.w A.F (a:=N) (b:=Mτ) (he.trans ht) (he.trans hv) le_rfl hx, ambient_hearthNX,sub_self,hL,one_mul,hZ]
    have hX:P.tock t (X).w ≤ N:=le_rfl; rw[grantStretchNX i t (X).w (X).F hX hX b e,grantStretchNX i t A.w A.F (he.trans ht) (he.trans ht) b e,←_root_.sub_mul,←mul_sub]; refine le_trans (norm_pads_mul _ _ _ (P.hearthBudgetNX ..) (P.hearthBudgetNX ..)) ?_ -- tune glimpse
    rw [civicBeltNX p q,hp',←mul_sub]; refine (norm_mul_le ..).trans ?_; rw [show P.ambientTurn i θP (ψ D.w D.F M M)- P.ambientTurn i θP (P.hearthNX i (M+M)) = P.ambientTurn i θP _ from (by unfold ambientTurn; rw[mul_sub,_root_.sub_mul])]; rw [ambient_norm]; exact mul_le_mul_of_nonneg_right (BeltMothersNX A he ht he hv) (norm_nonneg _)
#print axioms BudgetBeltNX
end Glaze
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
