import GaugeFieldConstruction.Persel
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
variable (R:Signed)(b:Bool)
abbrev kΦs(v:FactIx):= R.flip v.2
abbrev pΦs(v:FactIx):FactIx:= ((signBit R).xor v.1,R.perm v.2)
lemma haul_ix (k:FactIx)(V:Views) : tipK k (moveP R⁻¹ b V) =pay (b.xor (kΦs R k)) (tipK (pΦs R k) V):=by
 let X:= R⁻¹; have ht(p: TableF.Lenten.Plane)(i:Axis): κcad X b p i=pay (b.xor (R.flip i)) (p (R.perm i)):=by -- namespace tune
    change (night b • X.act p) _= _; have hp:X.act p i=pay (R.flip i) (p (R.perm i)):=by
       have hx:= X.act_at p (R.perm i); rw [show X.perm (R.perm i)=i from perm_for ..,show X.flip (R.perm i)=R.flip i by simp [X]] at hx; exact hx
    change night b * X.act p i= _; rw [hp]; cases b<;>cases R.flip i<;>simp [night] -- tune
 unfold pΦs kΦs moveP; rw [met_stamp,signBit_inv]; rcases k with ⟨a,i⟩; cases signBit R<;>cases a
 · exact ht V.1 i
 · exact ht V.2 i
 · exact ht V.2 i
 exact ht V.1 i
lemma anch_A (k:FactIx)(V: Views):
 cashA R b ((tipK k (moveP R⁻¹ b V):ℂ)*(heelC k)⁻¹)= pay (kΦs R k) ((tipK (pΦs R k) V:ℂ)*(heelC (pΦs R k))⁻¹):=by
 rw [haul_ix]; let u:ℝ:= tipK (pΦs R k) V; let t:= kΦs R k; change cashA R b ((↑(pay (b.xor t) u):ℂ)* (axisCost k.1)⁻¹)= pay t ((u:ℂ)*(axisCost ((signBit R).xor k.1))⁻¹); unfold cashA; rw [met_stamp]; cases k.1 <;> cases b <;> cases t<;>cases signBit R<;>simp [tivCost,cSignX,mul_comm, star_mul] <;> ring
lemma anchor_m (p:Pal)(q:FactIx)(w:Views): WingL R b (((tipK q (moveP R⁻¹ b w):ℂ)*(heelC q)⁻¹) • p)=pay (kΦs R q) (( (tipK (pΦs R q) w:ℂ)*(heelC (pΦs R q))⁻¹) • WingL R b p):=by rw [stepperX,anch_A]; cases kΦs R q<;> simp
lemma anchor1 (p p':P03)(a:Bool)(h:WingL R b p.val = pay a p'.val)(q:FactIx)(v:Views): WingL R b ((spikeV q p).val (moveP R⁻¹ b v))=pay ((kΦs R q).xor a) ((spikeV (pΦs R q) p').val v):=by
 rw [tips_pay,tips_pay,anchor_m, h]; cases kΦs R q<;> cases a<;> simp
lemma anchor2 (p p':P03)(a:Bool)(h:WingL R b p.val=pay a p'.val)(q k:FactIx)(x y:Views): WingL R b ((peakV q k p).val (moveP R⁻¹ b x) (moveP R⁻¹ b y))=pay ((kΦs R q).xor ((kΦs R k).xor a)) ((peakV (pΦs R q) (pΦs R k) p').val x y):=by
 rw [slowκ,slowκ,map_add,anchor_m,anchor_m,anchor1 R b p p' a h,anchor1 R b p p' a h]; cases ((kΦs R k).xor a)<;>cases kΦs R q<;>simp only [Bool.false_xor,Bool.true_xor,Bool.xor_false,Bool.xor_true,Bool.not_true,Bool.not_false,pay_true,pay_false, smul_neg,neg_neg] <;> first| rw [neg_add]|abel -- tune
lemma κ0 (v: Waves) : (bV0 (pressA R b v)).val=WingL R b (bV0 v).val:=congrArg Prod.fst (sheen_v ..).part -- meta infer?
lemma κ1 (v:Waves)(p:Views): (bV1 (pressA R b v)).val p=WingL R b ((bV1 v).val (moveP R⁻¹ b p)):=by
 have ht:=congrArg (fun i:PalOne=>i.2.1 p) (sheen_v R⁻¹ b v).part; exact ht
lemma κ2(v:Waves)(p q : Views): (bV2 (pressA R b v)).val p q=WingL R b ((bV2 v).val (moveP R⁻¹ b p) (moveP R⁻¹ b q)):=by
 have he:=congrArg (fun i:PalOne=> i.2.2.val p q) (sheen_v R⁻¹ b v).part; exact he
-- BRR pure strokes align; comparison along ph Reading h.cr etc
private abbrev Ph:= Row.ferm true
lemma conta_s (u : J Row.f) (p:Axis): let T:=P_f p u; let L':=L p u; let Z:=figV (false,p) u; let M:=figV (true,p) u; Z=(1/2:ℂ) • (T-L') ∧ M=(1/2:ℂ) • (T+L'):=by
 intro T L' Z M; have ht:T=Z+M:=(LinearMap.congr_fun (fig_s _) _).symm; have he:L'= -Z+M:=(LinearMap.congr_fun (fig_r _) _).symm; rw [ht,he]; constructor<;>module
private abbrev mix_Λ(P Q:ℂ)(b:Bool):=(1/2:ℂ) * (P+pay (!b) Q)
lemma mix_s (u:Weyl false× Weyl true)(a:J Row.f)(v:FactIx): Ph.tester u (figV v a)=mix_Λ (Ph.tester u (P_f v.2 a)) (Ph.tester u (L v.2 a)) v.1:=by
 rcases v with ⟨b,x⟩; cases b
 · rw [(conta_s a x).1,map_smul,map_sub]; change _ • (_-_) = _; rw [sub_eq_add_neg]; rfl
 rw [(conta_s a x).2,map_smul,map_add]; try rfl
private lemma mix_a(x y:ℂ)(a b c f:Bool): mix_Λ (pay (a.xor b) x) (pay (a.xor (c.xor b)) y) f=pay (b.xor a) (mix_Λ x y (c.xor f)):=by cases a<;>cases b<;>cases c<;>cases f<;>simp [mix_Λ, mul_add,add_comm]
lemma ache_R (w u: Weyl false × Weyl true)(p:Ph.poses R w u) (a c:J Row.f) (g:Bool) (h:Ph.tester u a=pay g (Ph.tester w c))(v:FactIx) :
 Ph.tester u (figV v a)=pay ((kΦs R v).xor g) (Ph.tester w (figV (pΦs R v) c)):=by
 rcases v with ⟨q,i⟩; have ht:Ph.tester u (P_f i a)=pay (g.xor (R.flip i)) (Ph.tester w (P_f (R.perm i) c)):=Ph.atP i a c R w u p g h; have hp:Ph.tester u (L i a)=pay (g.xor ((signBit R).xor (R.flip i))) (Ph.tester w (L (R.perm i) c)):= Row.atL R w u p _ _ g i h
 rw [mix_s,mix_s]; dsimp only; rw [ht,hp]; exact mix_a _ _ _ _ _ _
lemma trans_Δ (i:FactIx)(p:J Row.f)(h:cF p=p): cF (figV i p)=figV i p:=by
 rcases i with ⟨b,x⟩; have ht(A:Axis):bar (1/2:ℂ)=1/2:=by rw [map_div₀, map_ofNat,map_one]; -- tune name
 cases b; · rw [(conta_s ..).1, LinearMap.map_smulₛₗ,map_sub,f_tr,cL,h,ht x] -- ambiguous ht takes A unused auto eliminated explicit?
 rw [(conta_s ..).2,LinearMap.map_smulₛₗ,map_add,f_tr,cL,h,ht x]
lemma pot_B (a:Axis)(k: FlavorIndex):WingL R b (alloy a k).val= pay (f3Act.cost R a) (alloy (R.perm a) (rev R k)).val:=by rw [billTap]; cases f3Act.cost R a<;> rfl
lemma allot0(v:Waves)(a:Axis)(i:FlavorIndex)(h:bV0 v= alloy a i): bV0 (pressA R b v)=pay (f3Act.cost R a) (alloy (R.perm a) (rev R i)):=by apply Subtype.ext; rw [κ0,h,billTap]
lemma allot1(v: Waves)(x:FactIx)(a: Axis)(i:FlavorIndex)(h:bV1 v=spikeV x (alloy a i)): bV1 (pressA R b v)=pay ((kΦs R x).xor (f3Act.cost R a)) (spikeV (pΦs R x) (alloy (R.perm a) (rev R i))):=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro j; rw [κ1,h,anchor1 R b _ _ (f3Act.cost R a) (pot_B R b a i)]; cases ((kΦs R x).xor (f3Act.cost R a)) <;> rfl
lemma allot2 (v: Waves)(x y:FactIx)(a:Axis)(i:FlavorIndex)(h:bV2 v= peakV x y (alloy a i)): bV2 (pressA R b v)=pay ((kΦs R x).xor ((kΦs R y).xor (f3Act.cost R a))) (peakV (pΦs R x) (pΦs R y) (alloy (R.perm a) (rev R i))):=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro u; apply ContinuousLinearMap.ext; intro w; rw [κ2,h,anchor2 R b _ _ (f3Act.cost R a) (pot_B R b a i)]; cases ((kΦs R x).xor ((kΦs R y).xor (f3Act.cost R a))) <;> rfl
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
