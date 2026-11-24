import YM.CF.BProof.Axial.Sprig
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
open Salt Nacre
variable (n:Side)
local notation "D'"=> (Fir.Aop-(1/2:ℂ) • 1)
def pL : Op SU.Slot→ₗ[ℂ]Op (Single n) where
 toFun:= plankP n
 map_add' x y:=by simp_rw [plankP,headW,Matrix.kronecker_add]; rw [←map_add]; exact congrArg (love n) (jump_add (Equiv.refl (Site n)) (fun _=>D' ⊗ₖ x) (fun _=>D' ⊗ₖ y))
 map_smul' r x:=by change plankP n (r • x)=r • plankP n x; simp_rw [plankP,headW,Matrix.kronecker_smul]; rw [←map_smul]; exact congrArg (love n) (jump_smul (Equiv.refl (Site n)) (fun _=> D' ⊗ₖ x) r)
local notation "J"=> Op (Single n)
def pR : SpaceM→ₗ[ℝ]J:= -(((pL n).restrictScalars ℝ).comp SpaceM.subtype)
def pX (A:J) : J→ₗ[ℝ] J where
 toFun:=(A*·)
 map_add':=fun _ _=> mul_add ..
 map_smul':=fun _ _=> Matrix.mul_smul ..
def pY (A:J) : J→ₗ[ℝ] J where
 toFun:=(· *A)
 map_add':=fun _ _=> add_mul ..
 map_smul':=fun _ _=> Matrix.smul_mul ..
def up (A:J) : SpaceM→ₗ[ℝ]J:= pY n (1+A) ∘ₗ pX n (1-A) ∘ₗ pR n
def puff (A:J) : J→ₗ[ℝ]J:= (2:ℂ)⁻¹ • (pX n A+pY n A-LinearMap.id)
lemma puff_r (A B:J): puff n A B= Sault.rise A B:=rfl
variable {n}{R d a b c:ℝ} [Nonempty (ΘS R)] {T S:BeatL n} (F:BondL T S (body_Q (N:=n) 1) b c a d)
def orchard (R:ℝ)[Nonempty (ΘS R)] (w:0≤R): BondL T S (body_Q (N:=n) R) (knot R b) (knot R c) a d:=by
 refine ⟨grow F.ela R w,grow F.elt R w,grow F.coreS R w,fun i=> grow (F.cosY i) R w,grow F.heel R w, nearG _ w (fun _=>pR n) F.Yh,nearG _ w (fun x=> up n (S x)-pR n) F.Th,nearG _ w (fun x=> puff n (T x) ∘ₗ up n (S x)-puff n (tickA n) ∘ₗ pR n) F.Ch,?_,nearG _ w (fun x=>pY n (1-T x) ∘ₗ pX n (T x) ∘ₗ up n (S x)) F.Hc,fun s=>?_⟩
 · intro i; cases i; exact nearG _ w (fun x=>pX n (T x) ∘ₗ up n (S x)) (F.Hh _); exact nearG _ w (fun x=>pY n (1-T x) ∘ₗ up n (S x)) (F.Hh _)
 obtain ⟨z,y,x,t,b⟩:= F.sQ s; exact ⟨grantG _ w _ s _ z,grantG _ w _ s _ y,grantG _ w _ s _ x,grantG _ w _ s _ t,fun i => grantG _ w _ s _ (b i)⟩
lemma pureC (w:0≤R)(t:pureB F 1) : pureB (orchard F R w) (cQ*R):=by
 obtain ⟨u,v⟩:=t; refine ⟨?_,fun S t=>?_⟩
 · have e:= u.funds (mul_nonneg cQ_p.le w); rw [show cQ*R*_ = _ from (show cQ*R*(Tenant.quota^2*(wingRent D' 1*1))= Tenant.quota^2*(wingRent D' 1*(cQ*R)) from by ring)] at e; exact e
 funext i j; change cQ*R*F.ela.W S i j=0; rw [v S t]; simp
end YM.CF.Sour.Axial
