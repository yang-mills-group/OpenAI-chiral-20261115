import GaugeFieldConstruction.MeterΛ
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
abbrev rim : Bool:= b.xor (detX R) -- careful b R infer
abbrev pressA (v:Waves) := sheen R⁻¹ b v
abbrev cashA := cSignX (b.xor (detX R))
lemma rimX(a:ℂ): cSignX (b.xor (detX R⁻¹)) a=cashA R b a:=by rw [met_stamp,signBit_inv,← met_stamp]
lemma press_a(x y:Waves): pressA R b (x+y)=pressA R b x+pressA R b y:= sheen_plus ..
lemma press_c(x: Waves)(c:ℂ):pressA R b (c • x)=cashA R b c • pressA R b x:=by unfold pressA; rw [sheen_p,rimX]
-- Orientation relation
variable {X Y:Type}{W:Submodule ℂ (J X)}{H:Row.Record X Y}{B:Conj.Flip X}
abbrev pineU (f:J X):J X:= if (b.xor (detX R)) then B f else f
def Align (K:Calibration.Grade H B W)(x y:J X):Prop:=∀ w u (v:H.poses R w u), H.tester w y= H.tester u (pineU R b (B:=B) x)
variable {K:Grade H B W}
lemma align_add{x y t w:J X}(p:Align R b K x y)(h:Align R b K t w): Align R b K (x+t) (y+w):=by intro i j g; rw [map_add,p i j g,h i j g]; unfold pineU; split <;> simp -- tune
lemma align_s(x y:J X)(u: Align R b K x y)(t:ℂ): Align R b K (t • x) (cashA R b t • y):=by
 intro i j p; rw [map_smul,u i j p]; unfold pineU; unfold cashA; cases b.xor (detX R)<;>simp only [Bool.false_eq_true,not_false_eq_true, ↓reduceIte,map_smul]; -- tune
 · rfl
 rw [LinearMap.map_smulₛₗ, map_smul]; rfl
lemma align_bot : Align R b K 0 0:= fun w u h=> by simp only [pineU,map_zero,ite_self]
lemma align_v (x:↥W)(y:J X)(v:Align R b K x.val y): let U:↥W:= if (b.xor (detX R)) then flipT K x else x; (K.moves R U).val = y:=by
 intro U; apply Cauchy.ext_jet H.faith; intro k; obtain ⟨m,p⟩:=H.permit R k; rw [← K.transit p]; have he:U.val=pineU R b (B:=B) x.val:=by unfold pineU U; split<;>rfl -- ambiguity K
 rw [he]; exact (v k m p).symm
lemma align_γ (x y:J X)(a:Bool)(h:B x=x)(p: ∀ w u,H.poses R w u → H.tester u x=pay a (H.tester w y)) : Align R b K x (pay a y):= fun w u g=> by have he:=p w u g; cases a <;> simp only [pineU,h,ite_self,pay_false,pay_true, map_neg] <;> exact he.symm
-- linear generic. SemiAB pack.Mar.path
variable {E F:Type}[AddCommGroup E] [Module ℂ E][AddCommGroup F][Module ℂ F]
lemma moment (f:E→ₗ[ℂ]J X)(q:E→J X)(h:∀ x y,q (x+y)=q x+q y)(s:∀ a:E,∀ t:ℂ,q (t • a)= cashA R b t • q a){I:Type*}(κ:I→ E)(u:∀ i, Align R b K (f (κ i)) (q (κ i)))(x:E)(p:x∈Submodule.span ℂ (Set.range κ)): Align R b K (f x) (q x):=by
 apply Submodule.span_induction (p:=fun x _=>Align R b K (f x) (q x)) ?_ ?_ ?_ ?_ p
 · rintro i ⟨w,rfl⟩; exact u _
 · rw [map_zero]; have hp:= h 0 0; rw [add_zero] at hp; have hz:q 0=0:=add_left_cancel (show q 0+q 0=q 0+0 by rw [add_zero]; exact hp.symm); rw [hz]; exact align_bot R b -- tune
 · intro a c p v g w; rw [map_add,h]; exact align_add _ _ g w -- syntax
 intro t x p v; rw [map_smul,s]; exact align_s _ _ _ _ v _
-- transfer Athens
abbrev Wb (z:Wed):Bool:= wedAct.cost R z
abbrev Waℓ(z:Wed): Wed:= wedAct.move R z
lemma lat_G (f:Gem)(i j:Axis): (gird R f).val i j=pay ((R.flip i).xor (R.flip j)) (f.val (R.perm i) (R.perm j)):=by
 cases x:R.flip i <;> cases y:R.flip j<;>simp [Fren.gird,Fren.amt,x,y]
lemma blue_A (f:Gem)(v:Wed): blueL v (gird R f)= pay (Wb R v) (blueL (Waℓ R v) f):=by
 let i:=v.toBlade.val.1; let j:= v.toBlade.val.2; let I:=R.perm i; let J:=R.perm j; let e:= (R.flip i).xor (R.flip j); have he:I≠J:= (R.perm.injective.ne v.toBlade.property.ne)
 change (gird R f).val i j=pay ((Labels.reverseBit I J).xor e) (f.val (GaugeFieldConstruction.blade I J he).val.1 (GaugeFieldConstruction.blade I J he).val.2)
 rw [lat_G]; by_cases h:J<I
 · have he:=f.property I J; change pay e _= _; cases e <;> simp [Labels.reverseBit,h,GaugeFieldConstruction.blade] <;> change _ + _=0 at he <;> dsimp only [I,J] at he ⊢ <;> linarith
 change pay e (f.val I J)= _
 simp [Labels.reverseBit,h,GaugeFieldConstruction.blade]
lemma lat_U (f:Sut)(i j k:Axis): (girdS R f).val i j k = pay ((R.flip i).xor ((R.flip j).xor (R.flip k))) (f.val (R.perm i) (R.perm j) (R.perm k)):=by cases x:R.flip i<;> cases y:R.flip j<;>cases t:R.flip k<;>simp [Fren.girdS,Fren.amt,x,y,t]
abbrev Wδ(v: PairD):Bool:=(R.flip v.1).xor (Wb R v.2)
abbrev Aδ(v: PairD): PairD:=(R.perm v.1,Waℓ R v.2)
lemma blue_H (f:Sut)(v:PairD):blueP v (girdS R f)=pay (Wδ R v) (blueP (Aδ R v) f):=by
 let i:= v.2.toBlade.val.1; let j:=v.2.toBlade.val.2; let I:=R.perm i; let J:=R.perm j; let p:= (R.flip i).xor (R.flip j); let K:=R.perm v.1; let a:=R.flip v.1; have hp:I≠J:= R.perm.injective.ne v.2.toBlade.property.ne
 change (girdS R f).val v.1 i j=pay (a.xor ((Labels.reverseBit I J).xor p)) (f.val K (GaugeFieldConstruction.blade I J hp).val.1 (GaugeFieldConstruction.blade I J hp).val.2)
 rw [lat_U]; change pay (a.xor p) (f.val K I J)= _; cases a<;> cases p<;> by_cases h:J<I
 all_goals simp [Labels.reverseBit,GaugeFieldConstruction.blade,h]
 all_goals have he:=f.property.1 K I J; dsimp only [I,J,K] at he ⊢; linarith
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
