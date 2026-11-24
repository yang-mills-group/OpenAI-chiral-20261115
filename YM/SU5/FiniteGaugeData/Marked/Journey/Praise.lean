import YM.SU5.FiniteGaugeData.Marked.Journey.Roll

/-! Direct RP consumer (no hypothesis that a Printed exists), on actual
volume subsequences of the course. For application to *Printed* use
`Studio.result` and `Concert.gram`, or same E bridge at level zero.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x) (s:ℕ){u v:ℕ→ℕ}(p:Cabinet Y h u v)
local notation "K"=> tent Y h
local notation "Ξ"=> Cabinet.field Y h s p
local notation "Θ"=> Cabinet.audience Y h s p
include p
namespace Cabinet
lemma field_add {f g} (t:TestFamily K true f)(w:TestFamily K true g): Ξ (f+g)=Ξ f+Ξ g:=funext fun i=>
  tendsto_nhds_unique_of_eventuallyEq ((p.booked Y h s (t.add w)).1.inner i)
    (((p.booked Y h s t).1.inner i).add ((p.booked Y h s w).1.inner i))
    ((p.pass Y h s i).mono fun _ P=>hot_add Y h s t w P)
lemma addA {f g} (t:TestFamily K true f)(w:TestFamily K true g):Θ (f+g)=Θ f+Θ g:=
  tendsto_nhds_unique ((p.booked Y h s (t.add w)).1.periods)
    ((field_add Y h s p t w).symm ▸ (p.booked Y h s t).1.periods.add (p.booked Y h s w).1.periods)
lemma field_smul {f} (a:ℂ)(t:TestFamily K true f): Ξ (a • f)=a • Ξ f:=funext fun i=>
  tendsto_nhds_unique_of_eventuallyEq ((p.booked Y h s (t.scale a)).1.inner i)
    (((p.booked Y h s t).1.inner i).const_mul a)
    ((p.pass Y h s i).mono fun _ P=>hot_mul Y h s a P)
lemma smulA {f} (a:ℂ)(t:TestFamily K true f): Θ (a • f)=a*Θ f:=
  tendsto_nhds_unique ((p.booked Y h s (t.scale a)).1.periods)
    ((field_smul Y h s p a t).symm ▸ ((p.booked Y h s t).1.periods.const_mul a))
lemma unit (i): Ξ 1 i=1:=tendsto_nhds_unique_of_eventuallyEq ((p.booked Y h s TestFamily.oneT).1.inner i)
    (tendsto_const_nhds (f:=atTop) (x:=(1:ℂ))) ((p.pass Y h s i).mono fun _ H=>by
      dsimp only; unfold hot; rw [dif_pos H.depth]; exact (boxprice Y h i _ H.depth s H.fire H.enters).unit)
lemma unitA:Θ 1=1:= tendsto_nhds_unique_of_eventuallyEq ((p.booked Y h s TestFamily.oneT).1.periods) (tendsto_const_nhds (f:=atTop) (x:=(1:ℂ))) (Eventually.of_forall fun i=> p.unit Y h s _)
lemma lamp {f}(a: Eligible K true f):0 ≤ Θ (thetaK K f*f):=by
  apply ge_of_tendsto (p.booked Y h s (a.forget.ref.mul a.forget)).1.periods
  filter_upwards [((momentum Y s).comp p.grow_i.tendsto_atTop).eventually a.fits_time] with i w
  apply ge_of_tendsto ((p.booked Y h s (a.forget.ref.mul a.forget)).1.inner (u i))
  filter_upwards [p.pass Y h s (u i)] with n H
  unfold hot; rw [dif_pos H.depth]; exact (boxprice Y h _ _ H.depth s H.fire H.enters).fund 3 (K).ζ _ w

local notation "reading" => Settled.cross Θ
lemma lin₂ (f g k : eligible (tent Y h) true) : reading f (g+k)=reading f g+reading f k := by unfold Settled.cross; rw [AddSubmonoid.coe_add,mul_add]; exact p.addA Y h s ((Eligible.forget f.property).ref.mul (Eligible.forget g.property)) ((Eligible.forget f.property).ref.mul (Eligible.forget k.property))
lemma lin₁ (f g k : eligible (tent Y h) true) : reading (f+g) k=reading f k+reading g k := by unfold Settled.cross thetaK; rw [AddSubmonoid.coe_add, ref_plus,add_mul]; exact p.addA Y h s ((Eligible.forget f.property).ref.mul (Eligible.forget k.property)) ((Eligible.forget g.property).ref.mul (Eligible.forget k.property))
lemma scale₂ (f g : eligible (tent Y h) true) (a : ℂ) : reading f (a•g)=a*reading f g := by unfold Settled.cross; rw [Submodule.coe_smul,Algebra.mul_smul_comm]; exact p.smulA Y h s _ ((Eligible.forget f.property).ref.mul (Eligible.forget g.property))
lemma scale₁ (f g : eligible (tent Y h) true) (a : ℂ) : reading (a•f) g=star a*reading f g := by unfold Settled.cross thetaK; rw [Submodule.coe_smul, ref_scale,Algebra.smul_mul_assoc]; exact p.smulA Y h s _ ((Eligible.forget f.property).ref.mul (Eligible.forget g.property))

def form : eligible (tent Y h) true →ₗ⋆[ℂ] (eligible (tent Y h) true →ₗ[ℂ] ℂ) where
 toFun f:= ⟨⟨fun g=> reading f g,fun g k=>p.lin₂ Y h s f g k⟩,fun a g=>p.scale₂ Y h s f g a⟩
 map_add' f g:= LinearMap.ext fun k=>p.lin₁ Y h s f g k
 map_smul' a f:= LinearMap.ext fun g=>p.scale₁ Y h s f g a
lemma form_diagonal (f : eligible (tent Y h) true) : 0 ≤ p.form Y h s f f := p.lamp Y h s f.property
lemma herm (f g : eligible (tent Y h) true) : star (p.form Y h s g f)=p.form Y h s f g := by
 -- as in ReflectTest, get hermitian only from the limit proof of positivity
 have x(f : eligible (tent Y h) true) : (reading f f).im=0:= ((Complex.le_def.mp (p.lamp Y h s f.property)).2).symm
 have ht:=x f; have hg:=x g; have h₁:=x (f+g); have h₂:=x (f+Complex.I • g)
 rw [p.lin₁ Y h s,p.lin₂ Y h s,p.lin₂ Y h s] at h₁ h₂; rw [p.scale₁ Y h s,p.scale₁ Y h s,p.scale₂ Y h s,p.scale₂ Y h s] at h₂
 simp [ht,hg,Complex.mul_re,Complex.mul_im] at h₁ h₂; change star (reading g f)=reading f g; apply Complex.ext <;> simp <;> linarith
/-- Explicit Gram version: can test ANY finite list from the class with its admitted
cutoff limit then period limit. -/
theorem matrix {I : Type*} (F : I → eligible K true) [Fintype I] :
    (Matrix.of (fun i j=> Θ (thetaK K (F i).val*(F j).val))).PosSemidef := by
 apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
 · ext i j; exact p.herm Y h s _ _
 intro x; have he := Cabinet.form_diagonal Y h s p (∑ j,x j • F j)
 rw [map_sum (p.form Y h s),LinearMap.sum_apply] at he; simp_rw [map_sum,map_smulₛₗ (f:=(p.form Y h s))] at he -- argument
 change 0 ≤ ∑ i, star (x i)*∑ j, (p.form Y h s) (F i) (F j)*x j
 simpa only [smul_eq_mul,starRingEnd_apply,map_smulₛₗ,LinearMap.smul_apply, RingHom.id_apply,Finset.mul_sum, mul_assoc,mul_comm,mul_left_comm] using he
end Cabinet
end YM.CF.Buffered.Afterglow.Journey
