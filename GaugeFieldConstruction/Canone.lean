import GaugeFieldConstruction.Solvent
import GaugeFieldConstruction.SingingT
import GaugeFieldConstruction.Trebuchet
import GaugeFieldConstruction.VerdeArc
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
lemma CarriS (W:Waves) : ∃ X Y Z:Waves,Genre.gauge.Room X ∧ Genre.pure.Room Y ∧ Genre.mixed.Room Z∧ W=X+Y+Z:=by
 rcases W with ⟨a,⟨b,c⟩,r,u,v⟩; let X:Waves:= (0,(b,0),r,0,0); let Y:Waves:=(a,(0,c),0,u,0); let Z:Waves:= (0,(0,0),0,0,v)
 refine ⟨X,Y,Z,?_,?_,?_,?_⟩
 · exact ⟨rfl,rfl⟩
 · exact ⟨rfl,rfl,rfl⟩
 · exact ⟨rfl,rfl,rfl⟩
 unfold X Y Z; change _= (0+a+0, (b+0+0,0+c+0),r+0+0,0+u+0,0+0+v); simp

lemma kyφ (x:Cover)(K:Calibration)(F G:Psu x d)(v:ℝ) : John (F+G) K v=John F K v+John G K v:=by
 unfold John; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; rw [←add_mul]; congr 1; funext m U; unfold scalar glorified; by_cases h:pingV x d v (onC (K.c m) U.1) <;> simp [h,add_smul,Pi.add_apply]
lemma kyM (x:Cover)(K:Calibration)(F:Psu x d)(v:ℝ)(z:ℂ): John (z•F) K v=z • John F K v:=by
 unfold John; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [←Algebra.smul_mul_assoc]; congr 1; funext m V; unfold scalar glorified; by_cases h:pingV x d v (onC (K.c m) V.1) <;> simp [h, smul_smul]
abbrev verdχ(x:Cover): Paper Reifier→ₗ[ℝ] Psu x 24 where
 toFun:= Pvi Reifier x 24
 map_add' i j:= funext fun a=> funext fun F=>by unfold Pvi; simp [mul_add]
 map_smul' z i:= funext fun a=> funext fun F=>by unfold Pvi; simp only [Pi.smul_apply,RingHom.id_apply,Complex.real_smul]; ring
variable (x)
lemma Od_Β (W:Waves)(h:ℝ)(p:BudgetPoint)(s:0<h)(t:p.power≤3)(e:p.order≤6):
 Odious (Set.range (fun M:Male=>BushRoot M p h x W)):=by
 let K(i:Waves):= Set.range (fun M:Male=>BushRoot M p h x i)
 have u(i j:Waves)(p':Odious (K i))(t':Odious (K j)):Odious (K (i+j)):=by
    apply Od_a _ p' t'; rintro _ ⟨M,rfl⟩; exact ⟨_,Set.mem_range_self M,_,Set.mem_range_self M,map_add (bush_ℓ M x s t e) i j⟩ -- tune
 have H(i:Genre)(j:Waves)(p':i.Room j): Odious (K j):=by
    let z:= i.coinB p h; have hv:0<z:=Genre.coin_Bu i p s
    let g:=Glamor (Θk Reifier x) i ‖j‖; refine Od_L (z⁻¹ • verdχ x) ?_ (Glamor_f (Θk Reifier x) i ‖j‖ liquid)
    rintro _ ⟨M,rfl⟩; refine ⟨_,⟨M,p,j,h,t,e,p',s,le_rfl,(show z • _= _ from rfl)⟩,?_⟩
    rw [LinearMap.smul_apply,(show (verdχ x) (_•_)= _ from map_smul (verdχ x) z _), inv_smul_smul₀ hv.ne']; rfl
 obtain ⟨X,Y,Z,p₁,p₂,p₃,k⟩:= CarriS W; rw[k]; exact u _ _ (u _ _ (H _ _ p₁) (H _ _ p₂)) (H _ _ p₃)
def Johnℓ (K:Calibration)(q:ℝ): Psu x d →ₗ[ℂ] Buffered.Family K where
 toFun F:= John F K q
 map_add' f g:=kyφ x K f g q
 map_smul' i g:=kyM x K g q i
lemma Od_RawΩ (K:Calibration)(W:Waves)(h:ℝ)(p:BudgetPoint)(s:0<h)(t:p.power≤3)(e:p.order≤6):
 Odious (Set.range (fun M:Male=> John (BushRoot M p h x W) K p.threshold)):=by
 refine Od_L ((Johnℓ (d:=24) x K p.threshold).restrictScalars ℝ) ?_ (Od_Β x W h p s t e); rintro _ ⟨M,rfl⟩; exact ⟨_, Set.mem_range_self M,rfl⟩
#print axioms Od_RawΩ
end ArtCart
end MastTin
end YM.CF.XGarden
end
