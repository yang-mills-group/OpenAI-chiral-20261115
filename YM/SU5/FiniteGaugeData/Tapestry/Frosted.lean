import YM.SU5.FiniteGaugeData.Tapestry.RoofWindow
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat
open PiTensorProduct (tprod)

/-!
# Direct positivity for the selected cross-resolution state

No Printed, no post-limit factorization hypothesis. Norm EST & separated factor
law of the sharp inter-level maps supplied by the one election. `GlassRule` is
not an alternative funding axiom; here paying it. `fireside` is using comparison
to the heat *of this same election*, gives positivity, no fixed-period workstation
required. This describes precisely its application (in contrast to assuming an
additional history matching Requisite only on gauge functionals etc.).
-/
set_option quotPrecheck false
section
variable {A V:Type*}[CommRing A][Algebra ℂ A][AddCommGroup V][Module ℂ V]
def lustre (F:A→ₗ[ℂ]ℂ)(R:A→ₗ⋆[ℂ]A)(G:V→ₗ[ℂ]A): V→ₗ⋆[ℂ] (V→ₗ[ℂ]ℂ) where
 toFun x:= ⟨⟨fun y=> F (R (G x)* G y),fun y z=>by rw [map_add, mul_add,map_add]⟩,fun c y=>by change F (R (G x)* G (c • y))=c • F _; rw [map_smul,Algebra.mul_smul_comm,map_smul]⟩
 map_add' a b:= LinearMap.ext fun y=>by change F _=F _+F _; rw [map_add,map_add,add_mul,map_add]
 map_smul' c x:= LinearMap.ext fun y=>by change F _=starRingEnd ℂ c • F _; rw [map_smul,R.map_smulₛₗ,Algebra.smul_mul_assoc,map_smul]

variable (G: V→ₗ⋆[ℂ] (V→ₗ[ℂ]ℂ))(p:∀ x,0 ≤ G x x)
include p
lemma polarized(x y:V): star (G y x)=G x y:=by
 have h(x:V):(G x x).im=0:= ((Complex.le_def.mp (p x)).2).symm
 have hx:= h x; have hy:= h y; have a:= h (x+y); have b:= h (x+Complex.I • y)
 simp only [map_add,LinearMap.add_apply, G.map_smulₛₗ, LinearMap.smul_apply] at a b
 simp only [map_smul,smul_eq_mul,starRingEnd_apply] at b
 simp [hx,hy, Complex.mul_re,Complex.mul_im] at a b
 apply Complex.ext <;> simp <;> linarith
lemma lustred {I:Type*}[Fintype I](x:I→V): (Matrix.of fun i j=> G (x i) (x j)).PosSemidef := by
 apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
 · ext i j; exact polarized G p _ _
 intro t; have he:= p (∑ i,t i • x i)
 rw [map_sum G,LinearMap.sum_apply] at he; simp_rw [map_sum,LinearMap.map_smulₛₗ] at he -- also scalar map standard ℂ; simp only
 change 0 ≤ ∑ i, star (t i)* ∑ j, G (x i) (x j) * t j
 simpa only [smul_eq_mul,starRingEnd_apply,LinearMap.smul_apply,RingHom.id_apply, Finset.mul_sum, mul_assoc,mul_comm,mul_left_comm] using he
end
namespace Exhibition
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (s:ℕ) {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
variable (α:Axis)(z:Sunlight Λ)
local notation "K"=> tent Y H
local notation "∆" => Sunlight.sanctum Λ l α z K
local notation "flanked"=> flank α (z.hinge Λ)
lemma glass : GlassRule Λ l α z K (D.vistaDressing Y H) :=by
  refine ⟨fun i x=>rfl,fun i x h=>?_,?_⟩
  · exact roofline Λ l i true _ D h -- choose V? args order
  intro i h x y a b
  obtain ⟨s,e,u⟩:=a; obtain ⟨t,g,w⟩:= b
  let r:= z.marks i
  change liftD Y H i D (aureole K α r x*y)=_
  rw [Bseparated Y H i (negativeSide s (z.marks i) α) t D (aureoleBay K s _ α (z.marks i) x e) g (reflectedSep Y H s t i α (z.marks i) ((z.rents Λ l α i h).1 u) ((z.rents Λ l α i h).1 w)),Breflect]; rw [z.aligned i h]; rfl

lemma plainPos(t:z.start≤ s) {x:Dome K}(p:x∈keep Λ l s K true (flank α (z.hinge Λ))):
    0 ≤ planet Y H s D (aureole K α (z.marks s) x*x):=by
  obtain ⟨B,h,v⟩:= p
  have he:= (Sunlight.rents Λ l α z s t).1 v -- binders?
  obtain ⟨x,rfl⟩:= accolade (tent Y H) B x h
  obtain ⟨a,t⟩:= z.shifted s t; rw [t]; rw [t] at he
  exact fireside Y H B s α a D he x -- order
lemma glassE {x y: Cloud (Dome K)} (t:z.start ≤ s)(p:x∈Sunlight.cloister Λ l α z K s)(q:y∈Sunlight.cloister Λ l α z K s):
    vistaTake Y H D (z.oppose Λ α K x*y)= planet Y H s D (aureole K α (z.marks s) (vistaFinish Y H s D x) * vistaFinish Y H s D y):=by
  rw [vistaCall Y H s _ D ((shorter (Dome (tent Y H)) s).mul_mem (z.respectsCut Λ l α K p) (jettyBan Λ l _ _ _ _ s q))]; unfold vistaFinish; rw [reflectionHat Λ l α z s (D.vistaDressing Y H) _ (glass Y H D α z) t p q]
lemma glassOK {x: Cloud (Dome K)}(p:x∈Sunlight.sanctum Λ l α z K):
    0 ≤ Exhibition.vistaTake Y H D (z.oppose Λ α K x*x):=by
  obtain ⟨n,u,v⟩:= z.limitsArena Λ l α K p
  let S:= glass Y H D α z
  rw [glassE Y H n D α z u v v]; exact D.plainPos Y H n α z u (crownShelter Λ l n (D.vistaDressing Y H) (auxiliaryPad K) S.lantern (flank α (z.hinge Λ)) S.onward v)

def snowGram: ↥(Sunlight.sanctum Λ l α z (tent Y H)) →ₗ⋆[ℂ] (↥(Sunlight.sanctum Λ l α z (tent Y H))→ₗ[ℂ]ℂ):= lustre (vistaTake Y H D) (z.oppose Λ α K) (Sunlight.sanctum Λ l α z K).val.toLinearMap
lemma gramReal (x): 0 ≤ snowGram Y H D α z x x:= glassOK Y H D α z x.property
lemma gramReality (x y): star (snowGram Y H D α z y x)=snowGram Y H D α z x y:= polarized (V:=↥(Sunlight.sanctum Λ l α z K)) (snowGram Y H D α z) (D.gramReal Y H α z) x y
lemma polychromatic {ι:Type*} [Fintype ι](x:ι→ Cloud (Dome K))(p:∀ i,x i∈Sunlight.sanctum Λ l α z (tent Y H)):
   (Matrix.of (fun i j=> vistaTake Y H D (z.oppose Λ α K (x i)*x j))).PosSemidef:= lustred (snowGram Y H D α z) (gramReal Y H D α z) (fun i=>(⟨x i,p i⟩ : ↥(Sunlight.sanctum Λ l α z K))) -- applies to any
end Exhibition
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.glass
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.polychromatic
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.glassE
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.gramReality
