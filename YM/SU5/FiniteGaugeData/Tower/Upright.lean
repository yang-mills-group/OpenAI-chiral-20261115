import YM.SU5.FiniteGaugeData.Tower.Performed
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
# Single PSD form across fixed scales, incl direct election corollary

Cross entries genuinely defined via the operators on the hierarchy, not
assumed a 0 pairing between scales. Register at any common finer resolution
and prove independence of this choice. This includes all finite linear
combinations of tests at different levels. Not assuming isometric transport
on unbuffered forms (and not yet density in any continuum space). Quantitative
actual array convergence for these entries follows also from `pirouette`, once
specify the actual joint products. Do that below.
-/
open Heat
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)
def meshface(s:ℕ):ℤ:= (Λ.R.L.val:ℤ)^s * gaugeShift Λ.block z
local notation "J" u:max=> meshface (Λ:=Λ) z u
abbrev Clock:= (wing (tent Y H) j (meshface (Λ:=Λ) z s)).toSubmodule -- s parameter order
#check @Clock
local notation "W" t:max => Clock Y H t j z
def Voice:= Σ t:ℕ, ↥(Clock Y H t j z)
local notation "Z"=> Voice Y H j z

def finer {s t:ℕ} (p:s ≤ t) (f:W s) : Family (tent Y H):= stream Y H D s (t-s) f.val -- D not arg? include
lemma meshconsistent {s t:ℕ}(p:s ≤ t): (Λ.R.L.val:ℤ)^(t-s)*(meshface (Λ:=Λ) z s)=meshface (Λ:=Λ) z t:=by rw [meshface,meshface,←mul_assoc,←pow_add,Nat.sub_add_cancel p]
include Q
lemma newer {s t:ℕ}(p:s ≤ t)(f:W s): finer Y H (D:=D) j z p f∈ W t:=by
 unfold finer Clock; rw [← meshconsistent (Λ:=Λ) z p]; exact wings Y H Q s _ j _ f.property
noncomputable def invoke {s t:ℕ} (p:s ≤ t)(f:W s) : ↥(W t):= ⟨finer Y H (D:=D) j z p f,newer Y H Q j z p f⟩
local notation "V₀" => invoke Y H Q j z
lemma invoke_linear {s t:ℕ}(p:s≤ t)(f g:W s)(x:ℂ): V₀ p (x•f+g)= x•V₀ p f+V₀ p g:=by
 apply Subtype.ext; change stream Y H D s (t-s) (x • (f:Family K)+g.val)=_ 
 rw [woven_add Y H Q s (t-s) (((exam j _ K f.property).1).scale _) (exam j _ K g.property).1,woven_smul Y H Q s (t-s) (exam j _ K f.property).1]; rfl -- .. plus argument pattern
noncomputable def linking (s t:ℕ)(p:s≤ t): (W s) →ₗ[ℂ] (W t) where
 toFun:= V₀ p
 map_add':= fun f g=>by simpa using invoke_linear Y H Q j z p f g (1:ℂ)
 map_smul':= fun x f=>by apply Subtype.ext; exact woven_smul Y H Q s (t-s) (exam j _ K f.property|>.1) x
lemma linking_diagram {s t u:ℕ}(p:s≤ t)(q:t≤u)(f:W s):V₀ q (V₀ p f)=V₀ (p.trans q) f:=by
 apply Subtype.ext; change stream Y H D t (u-t) (stream Y H D s (t-s) f.val)=stream Y H D s (u-s) f.val
 conv_lhs => arg 4; rw [←Nat.add_sub_of_le p]
 rw [←joined,show t-s+(u-t)=u-s by omega]
lemma linking_cross {s t:ℕ}(p:s≤ t)(f g:W s): E t (mirror K j (J t) (V₀ p f).val*(V₀ p g).val) = E s (mirror K j (J s) f.val*g.val) :=by
 have ht:= teach Y H Q s (t-s) j (J s) f.property g.property; rw [show s+(t-s)=t by omega, meshconsistent (Λ:=Λ) z p] at ht; exact ht
lemma pan {s:ℕ}: J s=gaugeShift Λ.block ((Λ.R.L.val:ℤ)^s*z):=by unfold meshface gaugeShift; ring
omit Q
include V
lemma positive_level {s:ℕ}{I:Type*}[Fintype I](F:I→W s): Matrix.PosSemidef (Matrix.of fun i k=> E s (mirror K j (J s) (F i).val * (F k).val)):=by
 -- pan gives the library certificate at this plane. apply with casts across equality
 have h: J s= gaugeShift Λ.block (Λ.R.L.val^s*z):= by unfold meshface gaugeShift; ring
 let A (x:ℤ):Prop:= ∀ G:I→(wing K j x).toSubmodule, Matrix.PosSemidef (Matrix.of fun i v=>E s (mirror K j x (G i).val*(G v).val))
 apply (show A (meshface (Λ:=Λ) z s) from ?_) F; rw [h]; intro G; exact boson_allRP Y H V s j (Λ.R.L.val^s*z) G

omit V
include Q
variable (v w:Voice Y H j z)
def kennel :ℂ:=let A:=max v.1 w.1; E A (mirror K j (J A) (invoke Y H Q j z (le_max_left v.1 w.1) v.2).val*(invoke Y H Q j z (le_max_right v.1 w.1) w.2).val)
lemma vitals{n:ℕ}(p:v.1 ≤ n)(k:w.1 ≤ n): kennel Y H Q j z v w=E n (mirror K j (J n) (V₀ p v.2).val*(V₀ k w.2).val):=by
 let h:=max_le p k; have ht:= linking_cross Y H Q j z h (V₀ (le_max_left v.1 w.1) v.2) (V₀ (le_max_right v.1 w.1) w.2); rw [linking_diagram, linking_diagram] at ht; exact ht.symm
lemma linking_id {s}(f:W s): V₀ (le_refl s) f=f:=Subtype.ext (show stream Y H D s (s-s) _=_ by rw [Nat.sub_self]; rfl)
lemma kennel_eq {s:ℕ}(f g:W s): kennel Y H Q j z ⟨s,f⟩ ⟨s,g⟩=E s (mirror K j (J s) f.val*g.val):=by
 rw [vitals Y H Q j z _ _ (le_refl s) (le_refl s)]; simp only [linking_id]
include V
lemma eclectic {X:Type*}[Fintype X](F:X→Z):Matrix.PosSemidef (Matrix.of fun i j'=> kennel Y H Q j z (F i) (F j')):=by
 let r:ℕ:=univ.sup (fun i=>(F i).1)
 have h(i): (F i).1≤r:= Finset.le_sup (f:=fun i=>(F i).1) (mem_univ i) -- tune
 simp_rw [vitals Y H Q j z _ _ (h _) (h _)]
 exact positive_level Y H V j z _ -- Q remove
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.eclectic
