import YM.SU5.FiniteGaugeData.Tower.Pool
import YM.SU5.FiniteGaugeData.Tower.Flood
import YM.SU5.FiniteGaugeData.Tower.MeshClock
import YM.Heat.Duration
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Euclidean and real-time dynamics on the physical resolution hierarchy

First **with no spatial dynamics**. Use the reconstructed time semigroup with dummy space operators to access the established spectral and ground API (units all packed in E4 momentum of positive j-coordinate). The signatures below remove this spectator, and expose only energy and the one real parameter. Nothing Lorentz asserted (yet). Operators named with care: OC uses `duration t = t`, `sideways = -it`, `loft z` with imaginary part positive; evaluate `F (-iz)`.
-/
open Fock
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
variable (C:Arena Y H Q j z strict)
local notation "T" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "A"=> Ark.Ht Y H Q j z strict C
local notation "ρ" s:max i:max=>ripple Y H V s Q j z strict C i
open MeshClock
-- movement of one even step in level0 fermion spacings
noncomputable def timeMesh (Λ:Preparation):Mesh where
 L:=Λ.R.L.val
 Llarge:=Nat.le_trans (by decide: 2 ≤ 3) Λ.R.coarse
 base:=8*Λ.block.val
 baseP:=mul_pos (by norm_num) (show 0 < (Λ.block.val:ℝ≥0) by exact_mod_cast Λ.block.property) 

noncomputable def clockdrive: Many (timeMesh Λ) A where
 move s i:=ρ s i
 source s:=unleash Y H V s Q j z strict C
 add s i k:= breeds Y H V s Q j z strict C i k
 close s i := current_adjoint Y H V s Q j z strict C i
 refines s t i p:= (consistent_τ Y H V s Q j z strict C i t p).symm
 small s i:=ripple_le Y H V s Q j z strict C i
 early:=by
   apply Dense.mono (s₁:=itinerary Y H V Q j z strict C) _ (sounds Y H V Q j z strict C)
   intro x t; obtain ⟨s,v⟩:=Set.mem_iUnion.mp t; obtain ⟨u,rfl⟩:=v
   obtain ⟨r,y,h⟩:= nowPositive Y H V s Q j z strict C u
   exact Set.mem_iUnion.mpr ⟨r, (Set.mem_range.mpr ⟨(κ r) y,h.symm⟩)⟩
local notation "f₀"=>clockdrive Y H V Q j z strict C
private noncomputable def temporal:OS.Semigroup A j:= (f₀).monoAxis j
local notation "F₀"=>temporal Y H V Q j z strict C
-- positive Euclidean time; 'track' type no spectator
noncomputable def advance (t:ℝ≥0): A →L[ℂ] A:= (f₀).track t
local notation "ἂ" t:max=> advance Y H V Q j z strict C t
lemma advance_at (i':ℕ): (ἂ (whenly (timeMesh Λ) s i')) =ρ s (2*i'):=(f₀).track_even s i'
lemma advance_strong (v:A):UniformContinuous fun t:ℝ≥0=>(ἂ t) v:= (f₀).trekU v
lemma advance_smag (a b:ℝ≥0): (ἂ (a+b))=(ἂ a).comp (ἂ b):=(F₀).time a b
lemma advance_source:(ἂ 0)=ContinuousLinearMap.id ℂ A:=(F₀).eZero
lemma advance_adjoint (a:ℝ≥0):(ἂ a).adjoint=(ἂ a):=(F₀).sym a
lemma advance_small (a:ℝ≥0): ‖ἂ a‖≤1:= (F₀).shrinks a
lemma advance_vacuum (a:ℝ≥0):(ἂ a) (floorV Y H Q j z strict C)=floorV Y H Q j z strict C:= (f₀).track_invariant _ (by intro s i; exact normalized_τ Y H V s Q j z strict C (2*i)) a

-- Minkowski time and its norm holomorphic interior continuation,
-- agreeing on heated data up to the boundary.
open OS.Semigroup Complex
open scoped InnerProductSpace ContDiff
noncomputable def continued(z':ℂ): A →L[ℂ] A:= (F₀).F (-Complex.I*z')
local notation "Z" a:max=> continued Y H V Q j z strict C a
noncomputable def mink(t:ℝ): A →L[ℂ] A:= (F₀).edge t
local notation "Tt" a:max=> mink Y H V Q j z strict C a
lemma mink_source:(Tt 0)=ContinuousLinearMap.id ℂ A:=(F₀).birth
lemma mink_group(a b:ℝ):(Tt a).comp (Tt b)=Tt (a+b):=(F₀).send a b
lemma mink_norm(t:ℝ)(x:A):‖(Tt t) x‖=‖x‖:=(F₀).life t x
lemma mink_strong(v:A):Continuous (fun t:ℝ=>(Tt t) v):=(F₀).cont v
lemma mink_commutes(a:ℝ≥0)(t:ℝ): (ἂ a).comp (Tt t)=(Tt t).comp (ἂ a):=(F₀).eitherE a t
lemma agrees_euclid{a:ℝ≥0}(h:0<a): (Z ((a:ℝ)*Complex.I :ℂ))=ἂ a:=by
 rw [continued,show (-(Complex.I:ℂ)* (((a:ℝ):ℂ)*Complex.I))=duration a from ?_]; swap; · simp [duration,mul_comm _ Complex.I,←mul_assoc]
 exact (F₀).roots_heat h
lemma agrees_edge{a:ℝ≥0}(h:0<a)(t:ℝ): (Z (((t:ℂ))+((a:ℝ):ℂ)*Complex.I))=(Tt t).comp (ἂ a):=by
 have hi: -(Complex.I:ℂ) * ((t:ℂ)+((a:ℝ):ℂ)*Complex.I) = duration a + sideways t := by apply Complex.ext <;> simp [duration,sideways]
 unfold continued mink; rw [hi,←OS.Semigroup.along (F₀) (OS.Semigroup.dur.mpr h) t]; rw [OS.Semigroup.roots_heat (F₀) h]; rfl
lemma holo : AnalyticOnNhd ℂ (fun t=>Z t) {p:ℂ|0<p.im}:=by
 intro v h; unfold continued
 have he: -(Complex.I:ℂ)*v∈ OS.Semigroup.inside:= by change 0 < (-Complex.I*v).re; simpa using (show 0 < v.im from h)
 exact ((F₀).localHeat (-Complex.I*v) he).comp (analyticAt_const.mul analyticAt_id)

-- One-dimensional positive energies -- no proof/use of spectrum inequality vs transverse momenta.
open Spectral Boundary Probe
noncomputable def measureE (v:A): Measure ℝ:= ((F₀).ℚmeasure.diagonal v).map (fun y:E4 => y j)
local notation "μ" v:max=> measureE Y H V Q j z strict C v
instance billE_finite (v:A):IsFiniteMeasure (μ v):=by unfold measureE; infer_instance
lemma billE_positive (v:A): ∀ᵐ t:ℝ ∂(μ v),0 ≤ t:=by
 have h:Measurable (fun i:E4=>i j):=by fun_prop
 exact (ae_map_iff h.aemeasurable (measurableSet_le measurable_const measurable_id)).2 ((F₀).bright v)

lemma billE_char (t:ℝ)(v:A): inner ℂ v ((Tt t) v) = ∫ r:ℝ, Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I) ∂(μ v):=by
 let m:=(F₀).ℚmeasure.diagonal v; let e(x:E4):ℝ:=x j
 have he:Measurable e:= by unfold e; fun_prop
 rw [measureE,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* (t:ℂ)*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*(t:ℂ)*Complex.I))).aestronglyMeasurable)]
 have ht:=(F₀).assigned v t 0
 change (F₀).J 0 v v (t:ℂ)=_ at ht
 simpa [OS.Semigroup.J,OS.Semigroup.ray,(F₀).eZero,(F₀).unit.origin,Probe.plane,mink,e] using ht

lemma billE_laplace(t:ℂ)(h:0<t.im)(v:A):inner ℂ v ((Z t) v) = ∫ r:ℝ, Complex.exp ((r:ℂ)*t*Complex.I) ∂(μ v):=by
 let m:=(F₀).ℚmeasure.diagonal v; let e(x:E4):ℝ:=x j
 have he:Measurable e:= by unfold e; fun_prop
 rw [measureE,integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* t*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*t*Complex.I))).aestronglyMeasurable)]
 have ht:=(F₀).heat 0 v (z:=t) (show t∈_ from h.le)
 rw [OS.Semigroup.J, (F₀).lift_ray v h] at ht
 simpa [ (F₀).unit.origin,Probe.plane,e,continued] using ht
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.billE_char
#print axioms YM.CF.Buffered.Afterglow.Tower.billE_laplace
#print axioms YM.CF.Buffered.Afterglow.Tower.advance_at
#print axioms YM.CF.Buffered.Afterglow.Tower.agrees_edge
