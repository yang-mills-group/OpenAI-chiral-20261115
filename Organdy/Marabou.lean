import Organdy.Lunette

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

open Hive Levier Urn

open BProof.Bide

abbrev whirl(K:Calibration)(T:Shape):Buffered.Family K→ₗ[ℂ]Buffered.Family K where
 toFun:=flick T
 map_add' _ _:=suede_add ..
 map_smul' a _:=flick_scale T a
abbrev flounce(K:Calibration)(T:Shape): Dome K→ₗ[ℂ] Dome K where
 toFun f:=⟨flick T f.val,by obtain ⟨_,p⟩:=(show TestFamily K true _ from f.property).paid; exact broadCompile _ _ (flick_holds T p)⟩
 map_add' _ _:=Subtype.ext (suede_add ..)
 map_smul' a _:=Subtype.ext (flick_scale T a)

variable {K:Calibration}
lemma turner (f:Dome K)(T G:Shape) :
 flounce K G (flounce K T f)= flounce K (joinX G T) f:=by
 apply Subtype.ext
 obtain ⟨S,x⟩:=(show TestFamily K true _ from f.property).paid
 apply funext;intro n
 change flick G (flick T f.val) n=flick (joinX G T) f.val n
 rw [paidFlick G (flick_holds T x),paidFlick T x,paidFlick _ x,hmMark,hmMark,hmMark,
      chain _ _ _ (fun z=>Chord.keys_of_chord (Chord.full ((x.support n).allV z).sector)),
    veer_sign,veer_sign,veer_sign,
    show detX (joinX G T).s= _ from det_p G.s T.s, ←ray_join,_root_.mul_inv_rev]

lemma joinInc(s t:Signed): joinX (incX t) (incX s)=incX (t*s):=by
  change Shape.mk (t*s) (t.act 0+0)=_
  rw [Signed.act_zero, add_zero];rfl

abbrev feeD:ℂ:=(Fintype.card Signed:ℂ)⁻¹
def pauldron (K:Calibration):Dome K→ₗ[ℂ] Dome K :=
 feeD • ∑ s:Signed,ebony s • flounce K (incX s)
lemma showtime (f:Dome K):pauldron K f=feeD • ∑ s:Signed,ebony s • flounce K (incX s) f:=by
 rw [pauldron,LinearMap.smul_apply,LinearMap.sum_apply]
 rfl
lemma ebonyHue(t s:Signed):ebony (t*s)=ebony t*ebony s:=by
 unfold ebony; rw [det_p];cases detX t<;>cases detX s<;>norm_num
lemma leftBand (f:Dome K)(t:Signed):
 flounce K (incX t) (pauldron K f)=ebony t • pauldron K f:=by
 rw [showtime,map_smul,map_sum,smul_comm (ebony t)]
 conv_rhs =>
    arg 2
    rw [smul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft t)]
 refine congrArg (fun z:Dome K=>feeD • z) (sum_congr rfl ?_)
 intro s _
 rw [map_smul,turner,joinInc,show (Equiv.mulLeft t) s=t*s from rfl,smul_smul,ebonyHue,←mul_assoc,ebony_sq,one_mul]

lemma buttoned(f:Dome K): pauldron K (pauldron K f)=pauldron K f:=by
 conv_lhs =>
   rw [showtime]
   arg 2
   enter [2,t]
   rw [leftBand,smul_smul,ebony_sq,one_smul]
 rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Finset.card_univ,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
