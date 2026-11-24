import GaugeFieldConstruction.PartyD
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
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
variable (x:Cover)(w:300<n.val)
namespace BluffV
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
namespace Fables
open Conj
variable (R: Signed)(b:Bool)
abbrev WingL:= ℳPAL R⁻¹ b
lemma stepperX {p:Pal}(z:ℂ) : WingL R b (z • p)=cashA R b z • WingL R b p:=by
 rw [← rimX]; change Thera.jazz (detX R⁻¹) (sings b _ (z • _))= _ • (Thera.jazz (detX R⁻¹) _); unfold Thera.jazz; rw [singT,win_c,twist_scalar]; cases h:detX R⁻¹; simp [singT]
 simp only [ite_true,star_smul]; cases b <;> simp [singT,cSignX]
-- Alphabet spin transports. Color blocks.
abbrev DrumV (p:Axis)(X:Op SU.Slot): Pal:= Loden.high*(gammaOp p ⊗ₖ X)*Loden.low
lemma full_band (p:Axis)(X:Op SU.Slot): skim_L false true (DrumV p X)=cliff p ⊗ₖ X:= (ships_g _).trans (by rw [leaf,gamma_price])
lemma alloyB (x:Axis)(k:FlavorIndex): (alloy x k).val=DrumV x (spectral k):= swan (sendV _) (ship_K _) (by rw [full_band,alloy,plug_v])
lemma coinH (k:FlavorIndex)(v:Wed)(A:ComG)(p:Axis): (affK k v p).val A=DrumV p (Λshade k (A.val v.toBlade.val.1 v.toBlade.val.2)):= swan ((bladeV _).binned _) (ship_K _) (by rw [full_band,affK,growX]) -- tune
abbrev χRev (b:Bool)(X:Op SU.Slot):Op SU.Slot:= if b then star X else X
lemma span_mult (x y:Pal): sings b (twoU (spinU b R) b) (x*y)=sings b (twoU (spinU b R) b) x*sings b (twoU (spinU b R) b) y:=by rw [singT,win_m,map_mul]; try rfl
lemma shift_C (x:Axis)(X:Op SU.Slot): WingL R b (DrumV x X)=pay ((signBit R).xor (R.flip x)) (DrumV (R.perm x) (χRev (signBit R) (windX b X))):=by
 let T:=R⁻¹; let q:=T; let V:= spinU b T; let Q:= V; let p':=detX T; have hp:p'=signBit R:= (met_stamp _).trans (signBit_inv _); let U: Pal→ Pal:= sings b (twoU V b);
 have he:sings b V (gammaOp x)=hush (R.flip x) (gammaOp (R.perm x)):=by
    have hv:= (spinZ b T).cliff (R.perm x); unfold T at hv; rw [perm_for,show R⁻¹.flip (R.perm x)=R.flip x by simp] at hv; exact hv -- tune
 have hx: U (gammaOp x⊗ₖ X)= hush (R.flip x) (gammaOp (R.perm x) ⊗ₖ (windX b X)):=by
    unfold U; rw [Scroll.wingK,he]; change hush _ _ ⊗ₖ twist 1 _= _; rw [Fock.one_des]; cases R.flip x<;> simp [op_kron_neg]
 have hu(k:Bool): U (baseF k)=baseF (p'.xor k):= QuadClock.step_Base (spinZ b T) k -- tune
 let y:= R.perm x; let Z:= windX b X;
 change Thera.jazz p' (sings b (twoU V b) (baseF false*(gammaOp x⊗ₖ X)*baseF true))= _
 have hv: star Loden.high=Loden.high:= (bladeSeal false).2
 have hh: star Loden.low=Loden.low:= (bladeSeal true).2
 rw [show sings b _ (baseF false * _ * baseF true)=_ from span_mult T b (baseF false*(gammaOp x⊗ₖ X)) (baseF true), show sings b _ (baseF false*_) =_ from span_mult T b (baseF false) (gammaOp x⊗ₖ X)] -- tune
 change Thera.jazz p' (U (baseF false)* U (gammaOp x ⊗ₖ X)* U (baseF true))= _; rw [hu,hx,hu, hp]; cases v:signBit R
 · cases R.flip x<;> simp only [Thera.jazz,Bool.false_xor,Bool.false_eq_true, ↓reduceIte,pay_false,pay_true,hush_true,hush_false,mul_neg,neg_mul] <;> rfl
 cases R.flip x
 · change -star (Loden.low*(gammaOp y ⊗ₖ Z)* Loden.high) = -(DrumV _ (star Z)); unfold DrumV; rw [star_mul,star_mul,hv,hh,op_star_kron,(gammaAdj y).star_eq,←mul_assoc]
 change -star (Loden.low*(-(gammaOp y ⊗ₖ Z))* Loden.high)=DrumV _ (star Z); unfold DrumV; rw [mul_neg,neg_mul, star_neg,neg_neg,star_mul,star_mul,hv,hh,op_star_kron,(gammaAdj y).star_eq,←mul_assoc]
-- flavor reversal. cc handled
private lemma flip_unit (k:FlavorIndex)(h:signBit R=true): Matter.flip (Pi.single k 1)= Pi.single (rev R k) (1:ℂ):=by
 ext1 ⟨i,t,j⟩; rcases k with ⟨q,x,y⟩; simp [Matter.flip,Pi.single_apply,rev,h,and_comm]
private lemma lumaC (k:FlavorIndex): star ∘ Pi.single k (1:ℂ)=Pi.single k 1:= by ext1 i; simp only [Function.comp_apply,Pi.single_apply]; split<;>simp
open Matrix
lemma WindD (i: FlavorIndex): windX b (spectral i)=spectral i:=by
 cases b; rfl; change cc (Matter.coeffs _)=Matter.coeffs _; rw [Matter.conjugate_neut,lumaC]
lemma billTap(i: Axis)(k:FlavorIndex): WingL R b (alloy i k).val=(pay (f3Act.cost R i) (alloy (R.perm i) (rev R k))).val:=by
 let p:=signBit R; rw [alloyB,shift_C,WindD]; have he:χRev (signBit R) (spectral k)=spectral (rev R k):=by
    cases v:signBit R; · rw [rev,if_neg (by simp [v])]; rfl
    have hp:cc (spectral k)= spectral k:= WindD true k; change star (spectral k)= _; have hv: star (spectral k)=(cc (spectral k)).transpose:=by rw [cc,transpose_transpose]; try rfl
    rw [hv,hp]; change (Matter.coeffs _).transpose= Matter.coeffs _; rw [Matter.neutral_transpose,flip_unit _ _ v] -- tune cc
 rw [he, ←alloyB (R.perm i)]; change pay (p.xor (R.flip i)) _=_; let F:=f3Act.cost R i; change pay F _=(pay F (alloy (R.perm i) (rev R k))).val; cases F <;> rfl
lemma shiftH (k:FlavorIndex)(x:SU.group.Color) : windX b (Λshade k (dyeX b x))=Λshade k x:=by
 cases b; rfl
 change cc (Λshade k (dyeX true x))= _; rw [show dyeX true x=Matter.cc_color x from rfl] -- tune
 change cc (Matter.costing _ (Matter.cc_color _))=Matter.costing _ x; rw [Matter.conjugate_tint,lumaC]
lemma shiftF (k:FlavorIndex)(x:SU.group.Color)(e:signBit R=true): star (Λshade k x)= -(Λshade (rev R k) x):=by
 let D:= Λshade k; have hp:cc (D (dyeX true x))=D x:= shiftH true k x; have he(F: Op SU.Slot): (cc F).transpose=star F:=by rw [cc,transpose_transpose]; try rfl
 rw [←hp,←he,cc_cc]; change (Matter.costing _ (Matter.cc_color x)).transpose= -(Matter.costing _ x); rw [Matter.cost_transpose, flip_unit _ k e] -- tune hp D
lemma seatV (z:Axis)(p: Op SU.Slot): DrumV z (-p)= -(DrumV z p):=by
 have he:gammaOp z⊗ₖ (-p)= -(gammaOp z⊗ₖ p):=by ext x y; rcases x with ⟨x,v⟩; rcases y with ⟨y,u⟩; simp
 unfold DrumV; rw [he,mul_neg,neg_mul]
lemma walk_A (k:FlavorIndex)(a: Wed)(x:Gem)(p:Axis)(i:SU.group.Color):
 WingL R b ((affK k a p).val (hem (gird R x) (dyeX b i)))= (pay ((R.flip p).xor (Wb R a)) (affK (rev R k) (Waℓ R a) (R.perm p))).val (hem x i) :=by
 let Q:=Waℓ R a; let V:= rev R k; let U:SU.group.Color:= blueL Q x • i; let b':= Wb R a; rw [coinH]; change WingL R b (DrumV _ (Λshade k (blueL a (gird R x) • (dyeX b i))))= _; rw [blue_A]; have he(c:Bool): pay c (blueL Q x) • (dyeX b i)= dyeX b (pay c U):=by unfold U; cases c <;> simp
 rw [he, shift_C, shiftH]; let u:= signBit R; let c:= R.flip p; let I:= R.perm p;
 have hX(b:Bool): (pay b (affK V Q I)).val (hem x i)=pay b (DrumV I (Λshade V U)):=by rw [show DrumV I (Λshade V U)= _ from (coinH V Q (hem x i) I).symm]; cases b<;>rfl
 rw [hX]; change pay (u.xor c) (DrumV I (χRev u (Λshade k (pay b' U))))=pay (c.xor b') (DrumV I _); cases v:u
 · rw [show V=k from (by unfold V rev; rw [if_neg]; exact Bool.not_eq_true _|>.mpr v)] -- tune
   cases c<;> cases b' <;> simp [χRev,seatV]
 rw [show χRev true (Λshade k _)= _ from shiftF R k (pay b' U) v]; cases c <;> cases b'<;>simp [V,seatV] -- tune
lemma wind_V (W:Waves)(x:Gem)(y: SU.group.Color): (bm5 (pressA R b W)).val (hem x y)=WingL R b ((bm5 W).val (hem (gird R x) (dyeX b y))):=by
 have hp:= (sheen_v R⁻¹ b W).limb (gird R x) (dyeX b y); rw [gird_flip,dyeF] at hp; exact hp
lemma in_norm (w:Waves)(a: Axis)(p: Wed)(k:FlavorIndex)(e:bm5 w= affK k p a):bm5 (pressA R b w)=pay (x5Act.cost R (a,p)) (affK (rev R k) (Waℓ R p) (R.perm a)):=by apply grip_H; intro i j; rw [wind_V,e,walk_A]; try rfl
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
