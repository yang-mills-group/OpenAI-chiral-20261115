import GaugeFieldConstruction.AmberGaugeVU
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
local instance QuartzGammaUniqueVU38Indigo : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance QuartzGammaUniqueVU39Indigo : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance QuartzGammaUniqueVU40Indigo : Module ℂ ↥P14:= PackP.S.toModule
local instance QuartzGammaUniqueVU41Indigo : Module ℂ ↥P25:= PackM.S.toModule
local instance QuartzGammaUniqueVU42Indigo : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance QuartzGammaUniqueVU43Indigo : Module ℂ ↥G15:= PackS.S.toModule
local instance QuartzGammaUniqueVU44Indigo : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance QuartzGammaUniqueVU45Indigo : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance QuartzGammaUniqueVU49Indigo : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance QuartzGammaUniqueVU50Indigo : Module ℂ Gκ:= PackH.S.toModule
namespace Fables
open Conj
variable (R:Signed)(b:Bool)(d:Floor)

-- PROPER FRAME average to seek the clover. Off-shell generator steering exact at every Height
open Classical
-- avoid horrible simp expansion. SIGN diag. on all fields in two white sectors. proofs.Syntax
section
variable {W:Type}[AddCommGroup W][Module ℂ W]
noncomputable abbrev NixFeatVU (f:JetVU→Module.End ℂ W):= (1+f Hf2VU)*(1+f Hf1VU)*(1+f Hf0VU)
noncomputable abbrev NukeFeatVU (f:JetVU→Module.End ℂ W):= (1+f Hm1VU)*(1+f Hm0VU)
lemma ClauseFeatVU(f:JetVU→Module.End ℂ W)(x): FeatGaugeVU f x=(1-f HlVU) (NukeFeatVU f (NixFeatVU f x)):=by rw [←Module.End.mul_apply, ←Module.End.mul_apply]; unfold FeatGaugeVU NukeFeatVU NixFeatVU; simp only [mul_assoc]
lemma RadixVU (f g h:Module.End ℂ W)(x)(p q r:Bool)(y:f x=GaugeFieldConstruction.pay p x)(z:g x=GaugeFieldConstruction.pay q x)(u:h x=GaugeFieldConstruction.pay r x): ((1+h)*(1+g)*(1+f)) x= if p||q||r then 0 else 8 • x:=by cases p<;>cases q<;>cases r<;>simp only [Module.End.mul_apply, Module.End.one_apply,LinearMap.add_apply,map_add,y,z,u,pay_true,pay_false,Bool.or_false,Bool.or_true,map_neg, Bool.false_eq_true,↓reduceIte] <;> abel
-- certify the K4 & third payment on i array loops compactly
abbrev ActionSaneVU (f: Axis→ W)(u:JetVU)(H:Module.End ℂ W): Prop:=∀ i,H (f i)=f (u.val.perm i)
lemma OrbitK4VU (f:Axis→W)(F:JetVU→Module.End ℂ W)(x:Axis)(p:ActionSaneVU f Hm0VU (F Hm0VU))(q:ActionSaneVU f Hm1VU (F Hm1VU)) : NukeFeatVU F (f x)= f 0 + f 1 + f 2 + f 3 :=by
 unfold NukeFeatVU; simp only [Module.End.mul_apply,Module.End.one_apply,LinearMap.add_apply,p,map_add,q]; fin_cases x
 · change f 0+f 2+ (f 1+f 3)=_; abel
 · change f 1+f 3+ (f 0+f 2)=_; abel
 · change f 2+f 0+ (f 3+f 1)=_; abel
 · change f 3+f 1+ (f 2+f 0)=_; abel
lemma MercyK4VU(f:Axis→W)(F:JetVU→Module.End ℂ W)(p:ActionSaneVU f HlVU (F HlVU)): (1-F HlVU) (f 0+ f 1+f 2+f 3)=0:=by
 simp only [LinearMap.sub_apply,Module.End.one_apply,map_add,p]; change f 0-f 0+(f 1-f 2)+(f 2-f 1)+(f 3-f 3)=0; abel
end
lemma ΦAu3VU(a:Axis)(i:Matter.FlavorIndex):NixFeatVU ΩP3uVU (alloy a i)=0:=by
 obtain e:=RadixVU (ΩP3uVU Hf0VU) (ΩP3uVU Hf1VU) (ΩP3uVU Hf2VU) _ _ _ _ (Γcost3VU Hf0VU a i) (Γcost3VU Hf1VU a i) (Γcost3VU Hf2VU a i); rw[if_pos (show _ from ?_)] at e; exact e; fin_cases a<;>decide
lemma ΦAu4VU(k a:Axis)(b:Bool)(i:Matter.FlavorIndex): FeatGaugeVU ΩP4uVU (spikeV (b,k) (alloy a i))=0:=by
 rw [ClauseFeatVU]; obtain e:= RadixVU (ΩP4uVU Hf0VU) (ΩP4uVU Hf1VU) (ΩP4uVU Hf2VU) _ _ _ _ (Γcost4VU Hf0VU b k a i) (Γcost4VU Hf1VU b k a i) (Γcost4VU Hf2VU b k a i); unfold NixFeatVU; rw[e]; by_cases p:k=a
 · subst k; let f:Axis → ↥P14 := fun x=>spikeV (b,x) (alloy x i) -- tune type
   simp only [Bool.xor_self,Bool.or_self, Bool.false_eq_true,↓reduceIte,map_nsmul] -- tune xor self
   have hv(u:JetVU): ActionSaneVU f u (ΩP4uVU u):=by intro t; unfold f; simp [Γcost4VU] -- tune
   change 8 • ((1-ΩP4uVU HlVU) (NukeFeatVU ΩP4uVU (f a)))=0; rw[OrbitK4VU f ΩP4uVU _ (hv _) (hv _), MercyK4VU f ΩP4uVU (hv _),smul_zero]
 rw[if_pos, map_zero, map_zero]; revert p; intro p; exact (show ∀ k a:Axis,k≠a→ Bool.or (Bool.or ((Hf0ΓVU.flip k).xor (Hf0ΓVU.flip a)) ((Hf1ΓVU.flip k).xor (Hf1ΓVU.flip a))) ((Hf2ΓVU.flip k).xor (Hf2ΓVU.flip a))=true from (by decide)) k a p -- tune assoc
lemma LiveG3VU(v:Waves): bV0 (CarryΓVU v)=0:=by
 change ΓVoy3VU (CarryΓVU v)=_; rw [CarryΓVU,MeetFeatVU _ _ _ SpotΓ3VU]; let k:=FeatGaugeVU ΩP3uVU
 have h: Submodule.span ℂ (Set.range (Function.uncurry alloy))≤ LinearMap.ker k:=by
    refine Submodule.span_le.mpr ?_; rintro a ⟨⟨z,w⟩,rfl⟩; change k (alloy z w)=0; unfold k; rw [ClauseFeatVU,ΦAu3VU,map_zero,map_zero]
 exact h (crests _)
lemma LiveG4VU(v:Waves): bV1 (CarryΓVU v)=0:=by
 change ΓVoy4VU (CarryΓVU v)=_; rw [CarryΓVU,MeetFeatVU _ _ _ SpotΓ4VU]; let k:= FeatGaugeVU ΩP4uVU
 have h:Submodule.span ℂ (Set.range rayone)≤LinearMap.ker k:=by refine Submodule.span_le.mpr ?_; rintro a ⟨⟨p,z,w⟩,rfl⟩; exact ΦAu4VU p.2 z p.1 w
 exact h (revAir _)
#print axioms LiveG3VU
#print axioms LiveG4VU
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
