import YM.CF.Sour.Cabot
import YM.CF.Sour.Pie
import YM.CF.Sour.Wave
import YM.CF.Stax.Cast
import YM.CF.Sour.Maize
import YM.CF.Sour.Seal
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {N:Side} (T S:BeatL N)(E:χL N κ)
local notation "Sta"=> fC N S E
local notation "Bel"=> κR N E
local notation "Q"=> tickA N
local notation "Lx"=> Firing N
namespace BondL
variable {a b c d e s:ℝ}{T S E}(A: BondL T S E b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
variable (s_:Sweep N)(V:Orbit N)(i:κ)(Z:Aura N)(pF:Injective (priorP V.2))
open Levier Salt Ione
local notation "Λ"=> sauce s_.charge (detX s_.s) (γS s_)
local notation "OA"=> σX p Z ∅
local notation "WZ"=> yellA s_ V
local notation "Px"=> p.B
local notation "Sg"=> Support (More N)
local notation "Ut"=> (moldA s_ Z)
lemma recoil (D:Sg)(X:Aura N)(B:ℕ):actY s_ D ∈ αW B (moldA s_ X)↔ D∈ αW B X:=by
 have hx:halo B (actY s_ D)=actY s_ (halo B D):=by unfold actY; rw [←sitU,paysT]
 constructor
 · intro hp; have ht:= (mem_filter.mp hp).2; rw [hx] at ht; exact mem_filter.mpr ⟨mem_univ _,map_injective _ ht⟩
 intro p; refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [hx, ← (mem_filter.mp p).2]; rfl
include pF
lemma soloD {c:ℝ}(U₀ U₁:Elm N κ d a c)(b:Bool)(pL:leafJ s_ b U₀ U₁) (F G: Op (Single N)→FC (Dwell N))(hG:∀ x, Λ (F x)=G (realR s_ b x)): U₁.into.vik G g h p i Ut WZ=Λ (U₀.into.vik F g h p i Z V):=by
 let M:= V; let O:=roller h g V;
 change (∑ j∈ αW p.B Ut,Glyph.cure G g h _) WZ=Λ ((∑ j∈αW p.B Z,Glyph.cure F g h _) V); rw [Finset.sum_apply,Finset.sum_apply,sauce,singT,win_sum,map_sum]; symm; refine sum_bij (fun l _=>actY s_ l) (fun a u=> (recoil s_ a ..).mpr u) (fun x _ y _ h=> map_injective _ h) (fun i p=> ?_) ?_
 · have he:actY s_ (actY s_⁻¹ i)=i:=by ext; simp [actY,sitU]
   refine ⟨actY s_⁻¹ i,(recoil s_ ..).mp ?_,he⟩; rw [he]; exact p
 intro j v; change Λ (F (U₀.F j i (roller h g V)))= G (U₁.F _ _ _); rw [hG,← pL i j _ _ (show (roller h g V).val=_ from rfl)]; congr 2; -- equality of arguments.K
 apply Subtype.ext; rw [real_box _ _ _ _ (show (roller h g V).val=Tulip.profile (L V) from rfl)]; exact congrArg Tulip.profile (g.move V.1 V.2 s_ pF).symm
lemma wenK:A.choir (p:=p) g h i Ut WZ= Λ (A.choir (p:=p) g h i Z V):=by
 unfold choir; have ht(x y:FC (Dwell N)):Λ (x+y)= Λ x+Λ y:= Sault.flare ..; simp only [Pi.add_apply,ht]; obtain ⟨ha,hb,hc,hd,he⟩:= A.sQ s_
 -- mixed
 let F(b:Bool)(Y:Aura N)(V:Orbit N):=(A.cosY b).into.vik (Sault.crib b) g h p i Y V
 have hv(b:Bool): F (tipQ s_ b) Ut WZ=Λ (F b Z V):= soloD g h s_ V i Z pF _ _ _ (he b) (Sault.crib b) _ (fun x=> Sault.dew ..)
 rw [soloD g h s_ V i Z pF _ _ _ ha _ _ (fun x=> arm ..),soloD g h s_ V i Z pF _ _ _ hb _ _ (fun x=>arm ..),soloD g h s_ V i Z pF _ _ _ hc _ _ (fun x=>tiltH ..),soloD g h s_ V i Z pF _ _ _ hd _ _ (fun x=> Sault.boon ..)]; congr 1; let H:= tipQ s_; have hl:H true≠H false:=by unfold H tipQ; cases det_S s_ <;>simp; -- tune
 let X':= Λ (A.ela.into.vik (faceD true false) g h p i Z V)
 let D:= Λ (A.elt.into.vik (faceD true false) g h p i Z V)
 let T:= Λ (A.coreS.into.vik (fun A=>Matrix.trace A • (1:FC (Dwell N))) g h p i Z V)
 change X'+D+T+F false _ _+F true _ _= X'+D+T+_+ _
 cases h:det_S s_
 · rw [show F false Ut WZ=_ from (show F false Ut WZ=Λ (F false Z V) from (by have hx:=hv false; unfold tipQ at hx; rw [h] at hx; exact hx)),show F true Ut WZ=_ from (show F true Ut WZ=Λ (F true Z V) from (by have hx:=hv true; unfold tipQ at hx; rw [h] at hx; exact hx))] -- tune
 · rw [show F false Ut WZ=Λ (F true Z V) from (by have hx:=hv true; unfold tipQ at hx; rw [h] at hx; exact hx),show F true Ut WZ=Λ (F false Z V) from (by have hx:=hv false; unfold tipQ at hx; rw [h] at hx; exact hx)]; rw [add_right_comm]
omit pF
end BondL
end YM.CF.Sour
