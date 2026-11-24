import Anomaly.Ship.Ped
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Swell Bake Rive Leaf QuadClock Prism
local notation "Φχ"=> Seat n
local notation "Υ"=> hill I
local notation "Δp" => P.supportExponent
local notation "bυ"=> ((P.B:ℝ)⁻¹)
variable {M:I→ Bag n}
variable {a b c d s t v w z : ℝ}
variable {D:Finset I}{X:Key I→Pax n}{Y:Key I→Cusp n}{G:Key I→RegBudget n}{K:Key I→ForceBudget n}{A:Key I→I→Bag n}{H':I→Support (More n)}{σ:I→Seat n}{r:Key I→ℂ}
-- hypothesis checks derived from Holds
abbrev alure (P: BudgetPoint)(U:Key I→Pax n)(W:Key I→Cusp n)(M:I→Bag n)(z:Key I)(i:I): Bag n:= weaveOut (M i) (grainT P (U z) (W z))
variable (U:Diesel P σ h d c X Y G r)(wV:∀ z∈hill I,∀ i:I, Barrage P q (H' i) h (alure P X Y M z i) (P.supportExponent+8/(P.B:ℝ)) a b) (hS:∀ i,σ i∈ H' i)
variable {p: ℝ} -- κ
variable {m:ℕ}
variable (T:ThresholdPool P.B ((P.B:ℝ)⁻¹) (inkScatter m P.B |a|) s (inkScatter m P.B |b|) t)
local notation "ϰ"=> (gearOcc (b:=P) p T)
local notation "Yx"=> alure P X Y M
local notation "SX" X:max => grooveB 24 P X
variable {Ω:Occlus P}
structure BudK (K:Key I→ForceBudget n)(σ:I→Seat n) :Prop where
   quiet :∀ i:Force n,Hush σ i.val.1.val.2 fun z=>K z i
   toll :∀ (i:Force n)(V:Orbit n),River fun z:Key I=> K z i V
structure Crews (D:Finset I)(K:Key I→ForceBudget n)(σ:I→Seat n)(Ω:Occlus P)(A:Key I→I→Bag n){y b: Key I→I→Aura n→ℝ}(H:∀ z∈hill I,∀ (i:I)(X:Aura n),Flight P q X h (A z i X) (y z i X) (b z i X)):Prop where
   compass : BudK K σ
   silent: Dorm D K
   noise: Dorm D A
   zeroV (i:I)(u:i∉D) (z:Key I)(v:z∈hill I): A z i=0
   rears : Rears σ (fun z=>pinSeries (A z) z)
   wing: ∀ z∈hill I, ∃ a b r, OrbitRack Ω σ q (K z) h (presse H z) a b r (fun w x Y=>pinSeries (A z) w Y x)
variable (V0: BudK K σ)
private lemma tag_wide {X:ForceBudget n}{u:ℝ}(q:FlagWidth P X m)(v:SanB X (giftK P (Δp+1/2)) P h (fun _=>u))(p':1≤ p)(v':0≤ h): ∃ r:Cadre.Tape (A:=Seat n),(∀ X',∀ D⊆ (X':Aura n).val,Fray P h m X' D (settleK X X' D) (r X' D))∧∀ o:Seat n,tallB (Cadre.roofL r p) P.B (Δp+1/2) o≤ p * (chi_f P.order * u):=by
 obtain ⟨r,z,v,t⟩:= rent_old _ _ _ u X m q v v'
 refine ⟨r,z,?_⟩; intro i; have he:= t i
 rw [age_t,show Sour.urnL r=0 from funext v,show tallB (0:Aura n→ℝ) _ _ _=0 from by simp [tallB],zero_add,one_mul] at he
 rw [age_t,show urnL r=0 from funext v,show tallB (0:Aura n→ℝ) _ _ _=0 from by simp [tallB],zero_add]; exact mul_le_mul_of_nonneg_left he (zero_le_one.trans p') -- underscore might parse
include T U wV hS V0
lemma Crews.pack (e:∀ z∈ hill I,FlagWidth P (K z) (cipherK q))(hK:∀ z∈hill I,SanB (K z) (giftK P (P.supportExponent+1/2)) P h (fun _=>w)) (x:∀ i∉D,M i=0)(qf:0 ≤ h)(u:1≤p)(hv:Force_M P.B σ m)(hk:p*(chi_f P.order*w)≤ s)(hg:3 ≤ P.B)(xq:Dorm D X)(yp:Dorm D Y)(pk:Dorm D K): ∃ (a b: Key I → I → Aura n → ℝ),∃ H:∀ z∈hill I,∀ i:I,∀ T':Aura n,Flight P q T' h (alure P X Y M z i T') (a z i T') (b z i T'), Crews D K σ (gearOcc (b:=P) p T) (alure P X Y M) H := by
 let Occ:=gearOcc (b:=P) p T
 have hr(z) (vz:z∈hill I) := tag_wide (e z vz) (hK z vz) u qf
 have he(z)(vz:z∈hill I):∃ (a_ b_ : I → Aura n→ ℝ), ∃ Q:∀ (i:I)(X':Aura n),Flight P q X' h (alure P X Y M z i X') (a_ i X') (b_ i X'), ∃ r,OrbitRack Occ σ q (K z) h (zealPitch (alure P X Y M z) a_ b_ Q) (∑ i:I,a_ i) (∑ i:I,b_ i) r (fun i U t=> pinSeries (alure P X Y M z) i t U):=by
    obtain ⟨r,v,t⟩:=hr z vz; obtain ⟨a,b,Q,t',u',x⟩:=gearRack (σ:=σ) p u T (wV z vz) hS hv hg qf r v (fun i=>(t i).trans hk); exact ⟨a,b,Q,r,x⟩
 choose! a b v w z' using he; refine ⟨a,b,v,V0,pk,(fun z u y v t=>by change alure _ _ _ _ z= alure _ _ _ _ y; funext i; unfold alure; rw [xq z u y v t, yp z u y v t]),(fun i t z v=>by unfold alure; rw [x i t,roll_none]),?_,?_⟩ -- shadow proof arity binder choose!
 · have ht(i:I):Rears σ (fun z=>alure P X Y M z i):=by
      have hm:Rears σ (fun _=> M i):=⟨(fun _ _ _ _ _=>rfl),fun _ _ _ _ _ _=>rfl,fun _ _=>zeroR _⟩
      exact rear_up hm (backs U)
   exact series_R ht (fun z h i X' p=>by obtain ⟨_,_,_,W,_⟩:= (wV z h i).price; exact (W X' fun t=>p (t (hS i))).1)
 intro z h; rw [funext (fun w=> pressed v z w h)]; exact ⟨_,_,_,z' z h⟩
end YM.CF.Vow.TreasuryFog
