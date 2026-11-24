import GaugeFieldConstruction.Merise
import GaugeFieldConstruction.TrickΛ
import GaugeFieldConstruction.BowsFe
set_option autoImplicit false
set_option maxHeartbeats 25000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 17000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
open BluffV BluffV.Fables
namespace LaveFe
open Cauchy
-- plen capital: anchor unweighted.White v
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance : Module ℂ Gκ:= PackH.S.toModule
open BrentFe Flavor
abbrev feeB0(v:BigFe): ↥P03→ₗ[ℂ]P03 where
 toFun X:= ⟨_,SheetQ.Fe v _ X.property⟩
 map_add' x y:=Subtype.ext (map_add (ageFe v) x.val y.val)
 map_smul' z x:=Subtype.ext (twist_scalar _ x.val z)
abbrev feeB1(v:BigFe):↥P14→ₗ[ℂ] P14 where
 toFun X:= ⟨(τoneFe v).comp X.val,fun i=> SheetQ.Fe v _ (X.property i)⟩
 map_add' x y:=Subtype.ext (ContinuousLinearMap.ext fun i=>map_add (ageFe v) (x.val i) (y.val i))
 map_smul' z x:=Subtype.ext (ContinuousLinearMap.ext fun i=> twist_scalar (palFe v) (x.val i) z)
private def ξv (V:P25): Waves:= (0,(0,0),0,V,0)
def feeB2(v: BigFe): ↥P25→ₗ[ℂ] P25 where
 toFun X:= bV2 (SpinFe v (ξv X))
 map_add' x y:=Subtype.ext (ContinuousLinearMap.ext fun i=>ContinuousLinearMap.ext fun j=> map_add (ageFe v) (x.val i j) (y.val i j))
 map_smul' z x:=Subtype.ext (ContinuousLinearMap.ext fun i=>ContinuousLinearMap.ext fun j=> twist_scalar (palFe v) (x.val i j) z)
abbrev feeEX(v:BigFe): ↥G15→ₗ[ℂ] G15 where
 toFun X:=⟨(τoneFe v).comp X.val, ViewsM.Fe_ v _ X.property⟩
 map_add' x y:=Subtype.ext (ContinuousLinearMap.ext fun i=>map_add (ageFe v) (x.val i) (y.val i))
 map_smul' z x:=Subtype.ext (ContinuousLinearMap.ext fun i=> twist_scalar (palFe v) (x.val i) z)
variable (g : Flavor)
lemma χfe_one: chipUFe 1=1:=by funext i; apply Subtype.ext; ext j k; change chipFe (1:proper3) j k=(1:Op _) j k; rw[chipFe_v, Flavor.leg_one]; simp [Flavor.mark_one,Matrix.one_apply,eq_comm]
lemma raceFe (j k:Matter.Slot)(A: Op Matter.Slot): twist (δΔFe g) A (sensor g j) (sensor g k)=pay ((sensation g j).xor (sensation g k)) (A j k):=by
 let p:= δΔFe g; let θ:= sensation g j; let τ:= sensation g k; let F:= sensor g; have hp: Injective (sensor g):= (clanPerm g).injective
 rw [twist_formula,Matrix.mul_apply, sum_eq_single k]; swap
 · intro v u h; rw [Matrix.star_apply,clanInk,if_neg (hp.ne h),star_zero,mul_zero]
 swap; · simp
 rw [Matrix.star_apply,clanInk,if_pos rfl,Matrix.mul_apply,sum_eq_single j,clanInk,if_pos rfl]; swap
 · intro z v h; rw [clanInk,if_neg (hp.ne h),zero_mul]
 swap; · simp
 change pay θ _ * _ * star (pay τ _)=pay (θ.xor τ) _; cases θ<;>cases τ<;> simp
lemma impact_fe (z:Matter.FlavorIndex)(h:Matter.FlavorIndex): h=z ↔ Flavor.reprice g h=Flavor.reprice g z:=by refine ⟨fun p=> p ▸ rfl,fun h=>?_⟩; exact (reverses ..).symm.trans ((congrArg (g⁻¹.reprice) h).trans (reverses ..)) -- parser tune
lemma gripWFe(z:Matter.FlavorIndex):hues (M:=ℂ) g (Pi.single z 1)=pay (bit g z) (Pi.single (reprice g z) (1:ℂ)):=by -- inst
 ext i; let j:=Flavor.reprice g⁻¹ i; have hp:i=reprice g j:=by unfold j; rw [←rises,mul_inv_cancel]; exact (Flavor.rise1 i).symm
 rw [hp, Calibration.plate]; by_cases h:j=z; · rw [h,Pi.single_eq_same]; cases bit g z<;> simp
 simp only [Pi.single_apply, if_neg h]; cases bit g z <;> simp only [pay_true,pay_false,Pi.neg_apply, Pi.single_apply,(impact_fe g z j).not.mp h,ite_false,neg_zero,not_false_eq_true,↓reduceIte]
 all_goals cases bit g j<;>simp
lemma rayξFe (k:Matter.FlavorIndex): twist (δΔFe g) (BluffV.spectral k)=pay (bit g k) (BluffV.spectral (reprice g k)):=by
 let y:Fragment ℂ:= Pi.single k 1; let Y:= hues g y
 have ht:twist (δΔFe g) (Matter.coeffs y)=Matter.coeffs Y:=by
    apply Matrix.ext; intro i j; obtain ⟨c,rfl⟩:=(clanPerm g).surjective i; obtain ⟨d,rfl⟩:=(clanPerm g).surjective j
    exact (raceFe g c d _).trans (Flavor.case_coeff g (p:=y) (q:=Y) (Calibration.plate y g) _ _|>.symm)
 change twist _ (Matter.coeffs y)= _; rw [ht]; change Matter.jordan Y=pay _ (Matter.jordan _); rw [show Y= _ from gripWFe g k]; cases bit g k<;> simp
lemma PolarisFe (k:Matter.FlavorIndex)(x:SU.group.Color): twist (δΔFe g) (Λshade k x)=pay (bit g k) (Λshade (reprice g k) x):=by
 let y:Fragment ℂ:= Pi.single k 1; let Y:= hues g y
 have ht:twist (δΔFe g) (Matter.costing y x)=Matter.costing Y x:=by
    apply Matrix.ext; intro i j; obtain ⟨c,rfl⟩:=(clanPerm g).surjective i; obtain ⟨d,rfl⟩:=(clanPerm g).surjective j; exact (raceFe g c d _).trans (Flavor.case_cost g (p:=y) (q:=Y) (Calibration.plate y g) _ _ _|>.symm)
 change twist _ (Matter.costing y x)= _; rw [ht]; change Matter.forge Y x=pay _ (Matter.forge _ x); rw [show Y= _ from gripWFe g k]; cases bit g k<;> simp
lemma Drum_Fe(i:Axis)(Z:Op Matter.Slot):ageFe (chipUFe g) (DrumV i Z)=DrumV i (twist (δΔFe g) Z):=by
 unfold DrumV; simp only[map_mul, standBFe]; congr 2
 rw [show ageFe _ _=(TkFe SpinIdx (δΔFe g).val) * (gammaOp i ⊗ₖ Z) * star (TkFe SpinIdx (δΔFe g).val) from rfl]; unfold TkFe; rw [op_kron_mul,op_star_kron,op_kron_mul, one_mul,star_one,mul_one,twist_formula]
lemma fee_aFe(x:Axis)(i:Matter.FlavorIndex):feeB0 (chipUFe g) (alloy x i)=pay (bit g i) (alloy x (reprice g i)):=by
 apply Subtype.ext; change ageFe _ (alloy x i).val= _; rw [alloyB, Drum_Fe,rayξFe]; cases bit g i; · exact (alloyB ..).symm
 rw [pay_true,seatV,← alloyB]; rfl
lemma fee_bFe(x:Axis)(i:Matter.FlavorIndex)(k:FactIx):feeB1 (chipUFe g) (spikeV k (alloy x i))=pay (bit g i) (spikeV k (alloy x (reprice g i))):=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro j; change ageFe _ ((spikeV _ _).val j)=_; rw [tips_pay, twist_scalar]; change _ • (feeB0 _ _).val= _; rw [fee_aFe]; cases bit g i; · exact (tips_pay ..).symm
 change _ • (-_)= -_; rw [smul_neg]; exact congrArg Neg.neg ((tips_pay k (alloy x (reprice g i)) j).symm) -- tune
set_option maxHeartbeats 90000 in
lemma fee_cFe(x:Axis)(i:Matter.FlavorIndex)(p q:FactIx):feeB2 (chipUFe g) (peakV p q (alloy x i))=pay (bit g i) (peakV p q (alloy x (reprice g i))):=by
 let U:=chipUFe g; let X:=alloy x i; let Y:=alloy x (reprice g i); let b:=bit g i
 have hp(k l:FactIx)(a c:Views) : ageFe U ((peakV k l X).val a c)=pay b ((peakV k l Y).val a c):=by
    rw [slowκ,map_add, twist_scalar, twist_scalar];
    have he(z:FactIx)(t:Views):ageFe U ((spikeV z X).val t)=pay b ((spikeV z Y).val t):=by
       have h:feeB1 U (spikeV z X)=pay b (spikeV z Y):=fee_bFe g x i z
       change (feeB1 U (spikeV z X)).val _= _; rw [h]; cases b<;>rfl
    rw[he,he,slowκ]; cases b<;>simp; exact _root_.add_comm ..
 let Z:=peakV p q X; let V:=peakV p q Y
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro a; apply ContinuousLinearMap.ext; intro c
 calc
   _ = ageFe U (Z.val a c) := rfl
   _ = pay b (V.val a c):= hp p q a c
   _ = (pay b V).val a c:=by cases b <;> rfl
lemma fee_exFe(x:Axis)(i:Matter.FlavorIndex)(a:Wed):feeEX (chipUFe g) (affK i a x)=pay (bit g i) (affK (reprice g i) a x):=by
 apply grip_H; intro b v; apply congrArg (skim_L false true); change ageFe (chipUFe g) ((affK i a x).val _)= _; rw [coinH, Drum_Fe, PolarisFe]; cases bit g i; · exact (coinH ..).symm
 rw [pay_true,seatV,←coinH]; rfl
lemma Hues_live {E:Type*}[AddCommGroup E][Module ℂ E](i:Matter.FlavorIndex)(a:E): hues (M:=E) g (Pi.single i a)=pay (bit g i) (Pi.single (reprice g i) a):=by
 ext1 j; let k:= Flavor.reprice g⁻¹ j; have hp:j=reprice g k:=by unfold k; rw [← rises,mul_inv_cancel]; exact (Flavor.rise1 _).symm
 rw [hp,Calibration.plate]; by_cases v:k=i
 · rw [v,Pi.single_eq_same]; cases bit g i<;>simp
 have he:reprice g k≠reprice g i:=(impact_fe g i k).not.mp v
 cases bit g i <;> simp [Pi.single_apply,v,he]; -- tune
private lemma linear_onFE {E F:Type*} [AddCommGroup E][AddCommGroup F][Module ℂ E][Module ℂ F](A B:E→ₗ[ℂ]F){I:Type}(W:I→E)(h:∀ i,A (W i)=B (W i))(x:E)(p:x∈ Submodule.span ℂ (Set.range W)): A x=B x:=by
 apply Submodule.span_induction (p:=fun x _=> A x=B x) ?_ ?_ ?_ ?_ p
 · rintro y ⟨i,rfl⟩; exact h _
 · simp
 · intro x y p v k l; rw [map_add,map_add,k,l]
 intro t x p v; rw [map_smul,map_smul,v]
set_option maxHeartbeats 70000 in
lemma Hues_0Fe(A:↥P03):symf3 (feeB0 (chipUFe g) A) = hues g (symf3 A):=by
 apply linear_onFE (symf3.comp (feeB0 (chipUFe g))) ((hues g).comp symf3) (Function.uncurry alloy) ?_ A (crests A)
 rintro ⟨x,y⟩; change symf3 (feeB0 (chipUFe g) (alloy x y))= hues g (symf3 (alloy x y)); rw [fee_aFe,payM,TΦ,TΦ]; exact (Hues_live g y (Row.B x)).symm
set_option maxHeartbeats 70000 in
lemma Hues_1Fe(A:↥P14):symf4 (feeB1 (chipUFe g) A) = hues g (symf4 A):=by
 apply linear_onFE (symf4.comp (feeB1 (chipUFe g))) ((hues g).comp symf4) (rayone) ?_ A (revAir A)
 rintro ⟨x,y,z⟩; change symf4 (feeB1 (chipUFe g) (spikeV x (alloy y z)))= hues g (symf4 (spikeV x (alloy y z))); rw [fee_bFe,payM,TΦs,TΦs]; exact (Hues_live g z (figV x (Row.B y))).symm
set_option maxHeartbeats 70000 in
lemma Hues_2Fe(A:↥P25):symf5 (feeB2 (chipUFe g) A) = hues g (symf5 A):=by
 apply linear_onFE (symf5.comp (feeB2 (chipUFe g))) ((hues g).comp symf5) (raytwo) ?_ A (reverb A)
 rintro ⟨x,y,z,v⟩; change symf5 (feeB2 (chipUFe g) (peakV x y (alloy z v)))= hues g (symf5 (peakV x y (alloy z v))); rw [fee_cFe,payM,TΦp,TΦp]; exact (Hues_live g v (figV x (figV y (Row.B z)))).symm
set_option maxHeartbeats 70000 in
lemma Hues_3Fe(A:↥G15):task_M (feeEX (chipUFe g) A) = hues g (task_M A):=by
 apply linear_onFE (task_M.comp (feeEX (chipUFe g))) ((hues g).comp task_M) (tallyΧ) ?_ A (σshelfV A)
 rintro ⟨x,y,z⟩; change task_M (feeEX (chipUFe g) (affK x y z))= hues g (task_M (affK x y z)); rw [fee_exFe,payM,Tearn_X,Tearn_X]; exact (Hues_live g x (evalX (z,y))).symm
set_option maxHeartbeats 200000 in
lemma Flavor_paidFe (V:Waves)(d:Floor)(x:UV d)(h: SpineM V=shells d x): SpineM (SpinFe (chipUFe g) V)=shells d (flavors d g x):=by
 let v:=chipUFe g; let Y:=SpinFe v V
 apply Prod.ext
 · change (SpineM Y).1=(shells d (flavors d g x)).1; rw [EffortK]; change (0:ℂ)=x.1; rw [EffortK] at h; exact congrArg (fun s:Shell=>s.1) h
 apply Prod.ext
 · change (SpineM Y).2.1=x.2.1.val; rw [show x.2.1.val= _ from (congrArg (fun s:Shell=> s.2.1) h).symm,level_x,level_x]; rfl
 apply Prod.ext
 · have he:hues g ((SpineM V).2.2.1)=(SpineM Y).2.2.1:=by
      rw [EffortK V,EffortK Y]
      change hues g (symf3 (bV0 V)+(symf4 (bV1 V)+symf5 (bV2 V))) = symf3 (bV0 Y)+(symf4 (bV1 Y)+symf5 (bV2 Y)); rw [map_add,map_add]; apply congrArg₂ _ (show hues g _ = symf3 (bV0 Y) from (Hues_0Fe g (bV0 V)).symm); exact congrArg₂ (·+·) (show hues g _ = symf4 (bV1 Y) from (Hues_1Fe g (bV1 V)).symm) (show hues g _=symf5 (bV2 Y) from (Hues_2Fe g (bV2 V)).symm)
   change (SpineM Y).2.2.1= _; rw [←he,h]; exact (hue_frame (M:=UF d) (Q:=J Row.f) (SF d).subtype g x.2.2.1).symm
 · have ht: hues g ((SpineM V).2.2.2)=(SpineM Y).2.2.2:=by
      rw [EffortK V,EffortK Y]; change hues g (task_M (bm5 V))=task_M (bm5 Y); exact (Hues_3Fe g (bm5 V)).symm
   change (SpineM Y).2.2.2= _; rw [←ht,h]; exact (hue_frame (M:=UX d) (Q:=J Row.x) (SX d).subtype g x.2.2.2).symm
#print axioms Hues_2Fe
#print axioms Flavor_paidFe
end LaveFe
end YM.CF.XGarden.MastTin.ArtCart
end
