import YM.SU5.Reconstruction.Brazier.Trailing
import YM.SU5.Reconstruction.Brazier.Beacon
/-! Real trajectories: factorization of one widely stationed later PINHOLE with ANY support $F$ early (also at same clocks if you paid pairing). Exact in the physically aligned sequence of regulators; maintain all support charges to the UV roof. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "X" => Cloud (Dome (tent Y H))
local notation "Kx" t:max=> vistaFinish Y H t Z
namespace Tarmac
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
  Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
local notation "βr" => 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)
lemma contrast {S T:Finset Cover}{n:Side}(h:PhaseChoice.FullDistances (S∪T) n)(p:Detached Λ l S T) : ∀ x∈Satin.region S n,∀ y∈Satin.region T n,
  2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l) < separation x y:=by
 rintro x hxx y hyy; obtain ⟨x,hx,rfl⟩:= Finset.mem_image.mp hxx; obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp hyy; by_contra! v
 have hv:= p.act Λ l x hx y hy
 have ht:= h y (mem_union_right S hy) x (mem_union_left T hx)
 apply hv; rw [Lattice.box_test]
 have he(i:Axis): ( (x-y) i).natAbs ≤ βr:=by
   rw [←ht]; exact (component_le ..).trans v
 exact ⟨fun i=> by have p:=he i; omega,fun i=>by have p:=he i; omega⟩
lemma origin_mono {U W:Finset Cover}(e:U⊆W)(r:ℕ): volumeAround Λ l r U ⊆ volumeAround Λ l r W:=by
 induction r with
 | zero=> exact e
 | succ n ih=> exact followGrows _ _ ih
lemma dist_mono_here {S T:Finset Cover}{n:Side}(p:S⊆T)(q:PhaseChoice.FullDistances T n): PhaseChoice.FullDistances S n := fun x hx y hy=> q x (p hx) y (p hy)
variable (m u:ℕ)
local notation "v" s:max=> side Y m s -- avoid v binder
local notation "CLK"=> Y.uv u
noncomputable abbrev faceOf (s:ℕ)(x:Cloud (Dome (tent Y H))) : Mark (Journey.side Y m s) := attire (breathing Y H s m u x)
local notation "W"=> faceOf Y H m u
lemma source (s:ℕ)(f:Cloud (Dome (tent Y H)))(p:f∈shorter (Dome (tent Y H)) s){Q:Finset Cover}(b:AtSupport false (Satin.region Q (Journey.side Y m s)) (faceOf Y H m u s f))(w:ℕ)
    (e:Tapestry.Pay Y (s+w) m u): AtSupport false (Satin.region (volumeAround Λ l w Q) (Journey.side Y m (s+w))) (faceOf Y H m u (s+w) f):=
 hike_coverage Y H s Q p _ _ w e b
lemma connection {s:ℕ}{f:Cloud (Dome (tent Y H))}(p:f∈ shorter (Dome (tent Y H)) s) : faceOf Y H m u (s+1) f= ascender Y s m u (faceOf Y H m u s f):=by
 unfold faceOf breathing; rw [Decking.joins (tidalDressing Y H m u) s f (auxiliaryPad _) p]; change attire (music Y s m u _)=_; rw [music,flowing]
lemma factor_native {U Uw:Finset Cover}(s:ℕ)(p:Detached Λ l U Uw)(f g:Cloud (Dome (tent Y H)))(a:f∈shorter (Dome (tent Y H)) s)(b:g∈shorter (Dome (tent Y H)) s)
    (f₀:AtSupport false (Satin.region U (Journey.side Y m s)) (faceOf Y H m u s f)) (g₀:AtSupport false (Satin.region Uw (Journey.side Y m s)) (faceOf Y H m u s g))
    (h: faceOf Y H m u s (f*g)=faceOf Y H m u s f * faceOf Y H m u s g)
    (t:∀ r:ℕ, PhaseChoice.FullDistances (volumeAround Λ l r U∪volumeAround Λ l r Uw) (Journey.side Y m (s+r))) {r:ℕ}(hp:Tapestry.Pay Y (s+r) m u):
    faceOf Y H m u (s+r) (f*g) = faceOf Y H m u (s+r) f * faceOf Y H m u (s+r) g:=by
 induction r with
 | zero=> exact h
 | succ n ih=>
   have hx:Tapestry.Pay Y (s+n) m u:= ⟨hp.1,(by have he:= hp.2; omega)⟩
   have hj:Satin.PairIdx Y (s+n) m u:= hp -- defeq
   rw [Nat.add_assoc s n 1|>.symm,connection Y H m u (climbs (Dome K) (by omega) ((shorter ..).mul_mem a b)),connection Y H m u (climbs _ (by omega) a), connection Y H m u (climbs _ (by omega) b),ih hx]
   exact ascendSep Y (s+n) m u hj (source Y H m u s f a f₀ n hx) (source Y H m u s g b g₀ n hx) (contrast (t n) (Around_detaches Λ l p n))
lemma laterRead {n s:ℕ} (h:n < s) {x: Cloud (Dome (tent Y H))} (p:x∈shorter (Dome (tent Y H)) n) (f:Dome (tent Y H)):
    faceOf Y H m u s (x*pinhole _ s f)= faceOf Y H m u s x * faceOf Y H m u s (pinhole _ s f):= by
 unfold faceOf breathing; rw [Note.move_read _ _ p h f,Decking.outcrop,attire_mul]
lemma singleRead (s:ℕ) (x:Dome (tent Y H)): faceOf Y H m u s (pinhole _ s x)= exhibit Y H s m x.val:=by unfold faceOf breathing; rw [Decking.outcrop]; rfl
lemma singleFactor (s:ℕ)(x y:Dome (tent Y H)): faceOf Y H m u s (pinhole _ s (x*y))= faceOf Y H m u s (pinhole _ s x) * faceOf Y H m u s (pinhole _ s y):= by rw [singleRead,singleRead,singleRead]; exact actual_product .. -- tune
lemma singleCover {s:ℕ}{S:Finset Cover}{x:Dome (tent Y H)}(p:InTest (tent Y H) true S false x.val): AtSupport false (Satin.region S (Journey.side Y m s)) (faceOf Y H m u s (pinhole _ s x)):= by rw [singleRead]; exact exhibited Y H s m S p
end Tarmac
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
