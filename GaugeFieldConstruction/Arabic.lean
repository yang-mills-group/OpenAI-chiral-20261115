import GaugeFieldConstruction.Frango
import GaugeFieldConstruction.Vilify
set_option autoImplicit false
set_option maxHeartbeats 48000
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
-- Gauge×fermion. SU neutral.All representations.
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
open Phys
open Matter (FlavorIndex)
open Raw
abbrev bladeV (X:G15):ViewsM X.val:= X.property
lemma buck_L (X:G15) (x:Gem)(p:Spin×Spin) : let V:= fun u:SU.group.Color=>spinRead p.1 p.2 (skim_L false true (X.val (coneC x u))); ∃ a: FlavorIndex→ℂ,∀ u,V u=Matter.costing a u:=by
 intro V; let F:= LinearMap.comp ((spinRead p.1 p.2).restrictScalars ℝ) (LinearMap.comp ((skim_L false true).restrictScalars ℝ) (X.val.toLinearMap.comp (coneC x)))
 have he(X': ComG): salvo false true (X.val X'):= (bladeV X).binned X'
 have ht:Matter.neutral_c F:=by
    intro g y; have hx:= (bladeV X).main g x y; change _*spinRead p.1 p.2 _= spinRead p.1 p.2 _*_; rw [← offer_N,← offer_S]; exact congrArg (spinRead p.1 p.2) ((show skim_L _ _ _*keyR _=keyR _*skim_L _ _ (X.val (coneC x y)) from ((sym_R (he _) (he _) g).1 hx)).symm) -- tune
 obtain ⟨a,h⟩:= (Matter.species_c _|>.mp ht).exists; exact ⟨a,fun u=>LinearMap.congr_fun h u⟩
def sendP_ : δN→ₗ[ℂ]Pal where
 toFun A:=send_L false true A
 map_add' a b:=by apply θU; intro i j; rw [map_add,sendX,sendX,sendX]; split_ifs <;> simp
 map_smul' r a:=by apply θU; intro i j; rw [map_smul,sendX,sendX]; split_ifs <;> simp
abbrev Λshade (k:FlavorIndex): SU.group.Color→ₗ[ℝ] Op SU.Slot:= Matter.forge (Pi.single k 1)
private def σV (f:Wed): ComG→ₗ[ℝ] SU.group.Color where
 toFun D:= D.val f.toBlade.val.1 f.toBlade.val.2
 map_add' _ _:=rfl; map_smul' _ _:=rfl
def KronD (b:M2):Op SU.Slot→ₗ[ℂ]δN where
 toFun X:=b⊗ₖ X
 map_add' :=fun i j=> Matrix.kronecker_add ..
 map_smul' a f:=by ext i j; rcases i with ⟨x,p⟩; rcases j with ⟨y,q⟩; rw [Matrix.kronecker_apply,Matrix.smul_apply,Matrix.smul_apply,Matrix.kronecker_apply]; change _* (a*_) = a* (_*_); ring
private def μCross(k:FlavorIndex)(f:Wed)(T:M2):ComG →ₗ[ℝ] Pal:= (sendP_.restrictScalars ℝ).comp (( (KronD T).restrictScalars ℝ).comp ((Λshade k).comp (σV f)))
def gripV(k:FlavorIndex)(f:Wed)(T:M2):G15:=by
 let p:=LinearMap.toContinuousLinearMap (μCross k f T); let Y(y:ComG):=σV f y; have he(V:ComG):salvo false true (p V):=sendV (T ⊗ₖ Λshade k (Y V))
 refine ⟨p,⟨fun A=>he A, fun g a u=> (sym_R (he _) (he _) g).2 ?_⟩⟩; let X(x):= hem a x; let U:=SU.group.adjoint g; have ht:Y (X (U u))= U (Y (X u)):=by
    change a.val _ _ • (U u) = U (a.val f.toBlade.val.1 f.toBlade.val.2 • u); rw [map_smul]
 have hv(V): skim_L false true (p V)=T⊗ₖ Λshade k (Y V):=blank_A ..; simp_rw [hv]; apply (neutralX g T _ _ ?_).2; rw [show Y (coneC a _)=U (Y (X u)) from ht]; exact (Matter.cost_ok _ g (Y (X u))).symm -- tune
abbrev affK (k:FlavorIndex)(f:Wed)(a:Axis): G15:= gripV k f (cliff a)
lemma growX(k f T A): skim_L false true ((gripV k f T).val A)= T ⊗ₖ Λshade k (A.val f.toBlade.val.1 f.toBlade.val.2):=blank_A ..
lemma grip_H (F G:G15)(v:∀ x:Gem,∀ k:SU.group.Color, skim_L false true (F.val (hem x k))=skim_L false true (G.val (hem x k))): F=G:=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; rw [trade_Z i,map_sum,map_sum]; apply sum_congr rfl; intro j _; exact swan ((bladeV _).binned _) ((bladeV _).binned _) (v _ _)
lemma starsV (k:FlavorIndex)(f:Wed)(m:M2):gripV k f m=∑ i:Axis,chord m i • affK k f i:=by
 apply grip_H; intro x y; rw [growX]; simp_rw [Submodule.coe_sum, ContinuousLinearMap.sum_apply,map_sum, Submodule.coe_smul, ContinuousLinearMap.smul_apply, map_smul,affK,growX]; conv_lhs=>rw [chord_v m]
 ext ⟨a,b⟩ ⟨i,j⟩; rw [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.sum_apply, sum_mul]; apply sum_congr rfl; intro t _; rw [Matrix.smul_apply,Matrix.smul_apply,Matrix.kronecker_apply,smul_mul_assoc]
private lemma slotsC_G :∃ b:Wed→Gem,∀ x:Gem,x= ∑ j:Wed,blueL j x • b j:=by
 let u:= LinearMap.pi blueL; have hv: LinearMap.ker u=⊥:= le_antisymm (fun x p=>blue_s x (fun i=>congrFun (show u x=0 from p) i)) bot_le
 obtain ⟨c,h⟩:=u.exists_leftInverse_of_injective hv; refine ⟨fun i=> c (Pi.single i 1),fun x=>?_⟩
 simp_rw [← map_smul c]; rw [← map_sum, show ∑ i: Wed, blueL i x • Pi.single i (1:ℝ)=u x from (by ext1 i; rw [Finset.sum_apply]; simp [Pi.single_apply,u])]; exact (LinearMap.congr_fun h x).symm
lemma rain_X (F:G15) :∃ f:Wed→Spin×Spin→FlavorIndex→ℂ,F=∑ i,∑ t,∑ j,f i t j • gripV j i (motif t):=by
 obtain ⟨Z,H⟩:=slotsC_G; choose L h using (fun i t=>buck_L F (Z i) t)
 have he(x: Gem)(k:SU.group.Color): F.val (hem x k)=∑ i:Wed,F.val (hem (Z i) (blueL i x • k)):=by
    change F.val (grayC k x)= _; conv_lhs=> rw [H x,map_sum,map_sum];
    apply sum_congr rfl; intro i _; rw [map_smul]; congr 1; exact (map_smul (coneC (Z i)) (blueL i x) k).symm
 refine ⟨L,?_⟩; apply grip_H; intro x k; rw [he]; simp_rw [Submodule.coe_sum, ContinuousLinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro i _; ext ⟨s,v⟩ ⟨t,z⟩; -- compute one
 rw [Matrix.sum_apply, sum_eq_single (s,t)]; swap; · intro u _ w; rw [Matrix.sum_apply]; apply sum_eq_zero; intro j _; rw [Submodule.coe_smul,ContinuousLinearMap.smul_apply,map_smul,growX,Matrix.smul_apply, Matrix.kronecker_apply, show motif u s t=0 from (by unfold motif; rw [Matrix.single_apply]; exact if_neg fun p=> w (Prod.ext p.1 p.2)), zero_mul,smul_zero]
 swap; · simp
 let y:= blueL i x • k; let P:= L i (s,t); have hp:spinRead s t (skim_L false true (F.val (hem (Z i) y)))= Matter.forge P y:= h i (s,t) y
 rw [show (skim_L false true) (F.val (hem (Z i) _)) (s,v) (t,z)=_ from Matrix.ext_iff.mpr hp v z] -- tune rw
 rw [← Phys.diagonals P, map_sum, LinearMap.sum_apply]; simp_rw [Matrix.sum_apply]; apply sum_congr rfl; intro j _; rw [map_smul Matter.forge,LinearMap.smul_apply,Submodule.coe_smul, ContinuousLinearMap.smul_apply, map_smul (skim_L false true),Matrix.smul_apply,Matrix.smul_apply,growX, Matrix.kronecker_apply, show motif (s,t) s t=1 from (by simp [motif]),one_mul]; rfl -- tune
abbrev tallyΧ(p:FlavorIndex×Wed×Axis):= affK p.1 p.2.1 p.2.2
lemma σshelfV (F:G15): F∈Submodule.span ℂ (Set.range tallyΧ):=by
 obtain ⟨f,h⟩:=rain_X F; let K:=Submodule.span ℂ (Set.range tallyΧ); rw [h]; apply Submodule.sum_mem K; intro j _; apply Submodule.sum_mem; intro t _; apply Submodule.sum_mem; intro p _; apply Submodule.smul_mem; rw [starsV]; apply Submodule.sum_mem; intro i _; apply Submodule.smul_mem; exact Submodule.subset_span ⟨(p,j,i),rfl⟩ -- tune
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
