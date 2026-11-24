import YM.CF.Chaff.Mite
import YM.CF.Vale.Sail
import YM.CF.Fief.Vex
import YM.CF.Hype.Ace
import YM.CF.Ione.Mesh
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) 
variable {r Y V x μ b θ C' ρ:ℝ}
open Gloss Maize Ione Salt Hive Vow
open Hom Vale Vale.Grace Kea Nova RP RP.Str Spark
open Wilson Precision Next.Free Gauge Paige Vault Brace
variable {L:Patch}{Z:Teller SU.group}{W:ChartRatio SU.group}{N0:Postal}(D':Grace Z L W){X:Grasp D'.U B e}{R':Scree.Loom (CSide m B)}{k:ℕ}{u:ℝ}
open Fief

lemma coat_H(n k:ℕ)(v:1≤n):∃ B0:ℕ,∀ B:Side, B0≤ B.val→∃ e:ℝ,0< e ∧∀ s:ℝ,0< s→s≤e→∀ (L:Patch)(Z:Teller SU.group)(W:ChartRatio SU.group)(V:Grace Z L W)(X:Grasp V.U B s)(K:Spire.Pearl X)(t:Stamped Z.j L.L L.odd_side V.U),1≤ Z.j→Z.top.clip.direct≤1 → ∃ d a u:ℝ,0<d∧0<a∧0<u∧ Budget B s d∧∃ (F:(m:Side)→ Scroll m B (northZ m B)),(∀ m:Side, ScaleK a u (F m)) ∧ ∀ C H:ℝ,1≤H→∃ T:ℝ→ℝ,sizeK L.L 2 T∧∀ᶠ x:ℝ in atTop, ∀ (m:Side)(P:BudgetPoint)(R:Scree.Loom (CSide m B))(q d':ℝ)(c:ℕ), hintF P k n x C→ X.roundZ ≤ (CSide m B).val → Roof (CSide m B) q d' c R →c ≤ P.B →P.threshold ≤ q →d' < s→ 4*P.B < (Domain m B).val → ∃ b:ℝ,∃ I:RegBudget (CSide m B), Lives_B (H:=H) V (F m) I (radiusB x) (T x) P R X b:=by
 obtain ⟨K,q,h⟩:=larder n; obtain ⟨σ,A,a,Q,hS,hQ,vA,vq,vB,N,X⟩:= cant_X K q n; refine ⟨N,fun B x=>?_⟩
 obtain ⟨d,e,P,E,Y,F,W⟩:= X B x; choose F H using F
 refine ⟨e,E,fun s p y L Z R V Y' K' B' hZ g=>⟨d,a,Q,P,vq,vB,Y _ p y,F,fun m=>(H m).meter,?_⟩⟩ -- tune goal
 intro c μ0 tv; obtain ⟨D',w,u,hD,pW,pU,Yt⟩:= W s p y _ _ _ _ K' B' hZ; let W(x:ℝ):= w+radiusB x*u
 obtain ⟨μ,gX,T⟩:= Garn (K:=K) (a:=D') n k v L.L c tv h q p hD hS hQ W ((sizeK.mild L.L w).accrue ((sizeK.Bcash _).tint (sizeK.mild L.L u))) -- tune type
 refine ⟨μ,gX,?_⟩; filter_upwards [T,Work.E01.radiusB_tendsto.eventually (Yt μ0 tv)] with x tX vX M Q' R' q' d' c' hx v' xρ Kc p' hρ t
 exact livesB p.le xρ p' hρ Kc V (F M) v' g _ (vX M v' (F M) (H M)) (tX Q' hx) t
end YM.CF.Chaff
