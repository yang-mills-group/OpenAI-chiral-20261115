import YM.CF.BProof.Axial.Basis
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Axial
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
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
variable {T S:BeatL n}{R d e a b:ℝ}[Nonempty (ΘS R)](E:Elm n (ΘS 1) d a b)
abbrev knot (R:ℝ)(b:ℝ):= cQ*b*R
def grows(X:SO)(x:Openc (More n) d): SpaceM→ₗ[ℝ]Op (Single n):= stitch fun i=> E.F X (pole i) x
lemma grow_lab (v:0≤R)(X:SO)(t:ΘS R): Suite (badge _) (bail n d) (bail n d) X (fun i j=>cQ*R*E.W X i j) (fun x=> grows E X x t.val):=by
 let G(i:Tiles)(x:↥(Openc (More n) d)):= (cloth i) t.val • E.F X (pole i) x
 let c(i:Tiles)(u w:Single n):= ‖cloth i t.val‖* E.W X u w
 have e(i:Tiles): Suite (badge _) (bail n d) (bail n d) X (c i) (G i):=by simpa only [G,c,Complex.coe_smul,Complex.norm_real] using ((E.coat X).1 (pole i)).accel ((cloth i t.val:ℝ):ℂ)
 have l := Ticket.sumT univ c G fun i _ => (e i).toTicket
 have h: Suite (badge _) (bail n d) (bail n d) X (fun u w=>∑ i:Tiles,c i u w) (fun x=>grows E X x t.val):=by simp_rw [grows,sit]; exact ⟨l,License.suppose _ _ G (fun i _=>(e i).fuel)⟩
 let t' : ΘS 1:=⟨0,by simp⟩
 refine ⟨⟨h.frame,fun i j=>?_⟩,h.fuel⟩
 have H:= h.expo i j; have hz:= ((E.coat X).1 t').expo i j
 let P:=bail n d
 have w: (∑ l:Tiles,c l i j)≤ cQ*R*E.W X i j:=by simp_rw [c,←sum_mul]; gcongr; exact hz.positive; exact (cloth_b _).trans (mul_le_mul_of_nonneg_left t.property cQ_p.le)
 exact ⟨H.positive.trans w,fun t=> hz.triggered (right_ne_zero_of_mul t),fun x=> (H.bounded x).trans w,fun x y=>(H.variation x y).trans (mul_le_mul_of_nonneg_right w (Stage.pos _ _ _ _)),H.connected⟩
-- Family assembled from unit production respecting all tickets
noncomputable def grow (R:ℝ)[Nonempty (ΘS R)] (p:0≤R):Elm n (ΘS R) d a (knot R b):=by
 refine ⟨fun X t x=> grows E X x t.val, fun X i j=> cQ*R*(E.W X i j),fun X=>⟨grow_lab E p X,fun x=> (LinearMap.continuous_of_finiteDimensional (grows E X x)).comp continuous_subtype_val⟩,?_⟩; rw [knot,mul_right_comm]; exact E.bank.funds (mul_nonneg cQ_p.le p)
open Salt
lemma grantG (p:0≤R)(F:Elm n (ΘS 1) d a b)(s:Sweep n)(u:Bool)(t:leafJ s u E F) : leafJ s u (grow E R p) (grow F R p):=by
 intro Q X V Y y; change grows F _ _ _= realR _ _ (grows E _ _ _); simp_rw [grows,sit,real_f,←Complex.coe_smul,real_t]; exact sum_congr rfl fun i _=>congrArg ((cloth i Q.val:ℂ) • ·) (t (pole i) X V Y y)
lemma nearG (p:0≤R)(F:Chin n→SpaceM→ₗ[ℝ]Op (Single n))(t:NearL E (fun i x=> F x i.val)) : NearL (grow E R p) (fun i x=> F x i.val):=by
 intro Q x V h y; change _=∑ S:SO,grows E S x Q.val
 dsimp only
 rw [show F x.val Q.val=∑ i:Tiles,(cloth i Q.val) • F x.val (rankV i) from ?_]; swap; · nth_rw 1 [←cloth_eq Q.val]; rw [map_sum]; exact sum_congr rfl fun i _=> map_smul ..
 simp_rw [show ∀ i:Tiles,F x.val (rankV i)= _ from fun i=> t (pole i) x V h y,smul_sum,grows,sit]; rw [sum_comm]
end YM.CF.Sour.Axial
