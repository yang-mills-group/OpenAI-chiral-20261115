import YM.SU5.Relativistic.AllHeights
set_option pp.universes false
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
local notation "W"=>wingspan Λ l

variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(u:ℕ→ℕ)(p: StrictMono u)
local notation "A" r:max=>i (a (u r))
local notation "B" r:max=>k (b (u r))
local notation "L₁" r:max s:max S:max b':max => moveUp Y H s (i (a (u r))) (k (b (u r))) S b'
local notation "Σ₀"=>Bedside Y H (i:=i) (k:=k) (a:=a) (b:=b)

variable (s:ℕ)

variable {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=i) (a:=a) (k:=k) (b:=b) Y H u T)
variable {S:Finset Cover}{v:Bool}{x y:Family (tent Y H)}

open Tapestry Heat
-- b/d clash aliases
-- independent marks pushed only height. Use stream T b as existing recursion.
local notation "D₀" p:max=> (fun s=> T s p)
local notation "Z" b:max n:max=> stream Y H (fun s=> T s b) s n
include V Q
include t
variable (n:ℕ) (h:InTest (tent Y H) true S v x)
namespace GradesAll
include h
lemma allSupport : InTest K true (volumeAround Λ l n S) v ((Z v n) x):=by
    induction n with
    | zero=> exact h
    | succ n ih=> exact pays Y H u (s+n) t ih -- order
lemma allTurning (j:Axis)(z:ℤ): (Z v n) (mirror K j z x) = mirror K j (planeAt z Λ.R.L n) ((Z v n) x):=by
    induction n with
    | zero=> rw [planeAt,pow_zero,one_mul]; rfl
    | succ n ih=> change T (s+n) v ((Z v n) (mirror _ _ _ x))= _; rw [ih, lay Y H V Q u (s+n) t (allSupport Y H V Q u s t n h) j, step_plane]; rfl
lemma allCrossing {g:Bool}{A₀:Finset Cover}(hp: InTest K true A₀ g y)(e: Detached Λ l S A₀): (Z (v.xor g) n) (x*y) =(Z v n) x * (Z g n) y:=by
    induction n with| zero=> rfl| succ n ih=>change T (s+n) (v.xor g) ((Z (v.xor g) n) (x*y))=_; rw [ih,sealPair Y H V Q u (s+n) t (allSupport Y H V Q u s t n h) (allSupport Y H V Q u s t n hp) (Around_detaches Λ l e n)]; rfl
-- any Euclidean order add and twist
lemma allAdding {y:Family (tent Y H)}(w:InTest K true S v y) : (Z v n) (x+y)=(Z v n) x+(Z v n) y:=by induction n with| zero=>rfl| succ n ih=>change T (s+n) v ((Z v n) (x+y))=_; rw [ih,addL Y H V Q u (s+n) t (allSupport Y H V Q u s t n h) (allSupport Y H V Q u s t n w)]; rfl
lemma ampAll (z:ℂ): (Z v n) (z • x)=z • (Z v n) x:=by induction n with| zero=>rfl| succ n ih=>change T (s+n) v ((Z v n) (z • x))=_; rw [ih,scaleL Y H V Q u (s+n) t (allSupport Y H V Q u s t n h)]; rfl
lemma allColor (y:Family K)(z:InTest K true S v y)(w: GPhysical) (p:Circular S (restrictG Λ s w) x y): Circular (volumeAround Λ l n S) (restrictG Λ (s+n) w) ((Z v n) x) ((Z v n) y):=by
    induction n with
    | zero=>exact p
    | succ m ih=>
      have ht:restrictG Λ (s+m) w=parentGauge Λ (restrictG Λ (s+m+1) w):= gaugeHarmony ..
      rw [ht] at ih
      exact post Y H V Q u (s+m) t (allSupport Y H V Q u s t m h) (allSupport Y H V Q u s t m z) _ ih
lemma neutrally (p: CovCover K x): CovCover K ((Z v n) x):=by induction n with| zero=>exact p| succ n ih=> exact t.bless Y H V Q u (s+n) (allSupport Y H V Q u s t n h) ih
omit h
lemma originally {x:Family K}(p:TestFamily K true x): (Z false n) x=stream Y H D s n x:=by
 obtain ⟨S,p⟩:=p.paid
 induction n with| zero=> rfl| succ n ih=>change T (s+n) false ((Z false n) x)=_; rw [t.formerly Y H V Q u (s+n) (aux_test (allSupport Y H V Q u s t _ p)),ih]; rfl
end GradesAll

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
