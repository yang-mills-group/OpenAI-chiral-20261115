import YM.SU5.Reconstruction.Based.Fission
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
set_option quotPrecheck false
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
open SlabMark Finset Fock Lat Laurent Cube Spire Vale Pastry Peaks Dial Phase Lifted Skye Tenant Rush Tulip Girt Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
namespace LineCharge
open WalkRoots Rooted Orbitals Tapestry.Exhibition Tapestry.Altitude
variable (z:SU.Slot){k₀:ℕ}(a:Fin k₀→ Cover) {J:Calibration}(S:Finset Cover){μ:Multiset Cover}
-- keep both permissions: even before filling contour AND in that larger U. And definite arm poses.
structure Digest (μ:Multiset Cover)(f:Dome J):Prop where
 raw_origin : f.val∈raw S J (Window.family z) a μ
 paid : f.val ≠0 ∧ Tapestry.Neutral J f.val
 sized : (∃ i,a i∈μ) ∧ ∃ y∈ μ,y∉ Set.range a
 support : ∀ x∈ μ, nodeC x ∈ S
 current (y:Cover) (_:y∈ μ) (_:y∉ Set.range a): ∃ R:RouteMap (LineCharge.rect S), (∀x∈ LineCharge.rect S, R.base x=nodeC y) ∧ f.val∈ connected R J (Window.family z) a μ -- all terms genuinely charged through y
lemma extend_profile (S':Finset Cover)(h:S⊆ S') : raw S J (Window.family z) a μ≤raw S' J (Window.family z) a μ:=by
 let W:= Window.family z; apply Submodule.span_le.mpr; rintro v ⟨l,t,u,e⟩; apply Submodule.subset_span; refine ⟨l,t,u,?_⟩; suffices p: Rooted.scene S J W a l μ (removal J) (creation J) (scalar J) ≤ Rooted.scene S' J W a l μ (removal J) (creation J) (scalar J) from p e
 apply Submodule.span_le.mpr; rintro f ⟨x,G',t,e,rfl⟩; exact Submodule.subset_span (show _∈ _ from ⟨x,G', rise_ h t,e.mono h,rfl⟩)
where
 rise_ {X Y:Finset Cover}{A B':Atoms J}{l:List (Fin k₀)}{μ:Multiset Cover}{f:Family J}(e:X⊆ Y)(u:Stitches J (Window.family z) a X A B' l μ f) : Stitches J (Window.family z) a Y A B' l μ f:=by
    induction u with | empty=> exact .empty | put i y c d a b t v w s p q u h ih=> exact .put i y c d a b t v w s (e p) (e q) u ih
lemma paid_digest {f:Dome J} (t:f.val∈ raw S J (Window.family z) a μ)(u:f.val≠0)(p:Tapestry.Neutral J f.val) : Digest z a S μ f:=by
 obtain ⟨l,e,k,x,b⟩:= Rooted.was_here J (Window.family z) a _ _ _ u t; refine ⟨t,⟨u,p⟩,⟨b.anchor_here e, b.creation_here e⟩, b.reaches,fun y g hy=> ?_⟩
 obtain ⟨R,h⟩:= fixed_root (x:=nodeC y) (S:=rect S) (fun v h=> rect_connected (rect_contains S (b.reaches _ g)) h); exact ⟨R,fun x _=> h x, fromComponent R J _ a (extend_profile z a S _ (rect_contains S) t) p⟩ -- implicit k binder route

/- even on the ENTIRE enlarged stencil STILL authenticated as CP1 even questions inside U.
Preserve same purchase at every post. No further positivity price needed. Use on any pair. -/
variable (s:ℕ)(j:Axis)(p q:Cover)
local notation "Lp" x:max=>FirstWindows.leg j p x
local notation "Lq" x:max=> reposition (tent Y H) q x
local notation "Z" a:max=>streetBox (tent Y H) a (rect S)
local notation "A" => bufferedHull Λ l s (reflectedBox j 0 (streetBox (tent Y H) p (rect S)))
local notation "C'" => bufferedHull Λ l s (streetBox (tent Y H) q (rect S))
local notation "P" x:max=> pinhole (Dome K) s x
local notation "Ω"=> ((Set.univ:Set ℕ) ∩ Set.Iic s)
local notation "N" x:max k:max=>insideAt Λ l (tent Y H) true x k
structure Housed (f:Dome (tent Y H)):Prop where
 bills_left : FirstWindows.leg j p f∈ insideAt Λ l K true (A) s
 bills_right : Lq f ∈ insideAt Λ l (tent Y H) true (C') s
 query_left : (P (Lp f))∈ PhaseChoice.circum Λ l K false A Ω
 query_right : (P (Lq f))∈PhaseChoice.circum Λ l K false (C') Ω
 holds_left (t:ℕ)(p':s≤ t): spreadTo Y H G s t (Lp f)∈ N A t
 holds_right (t:ℕ)(p':s≤ t):spreadTo Y H G s t (Lq f)∈ N C' t
lemma housing {f:Dome (tent Y H)}(t:Digest z a S μ f): Housed Y H G S s j p q f:=by
 let u: InTest K false (rect S) false f.val:= FilTest (visible K _ a μ (rect S) (extend_profile z a S _ (rect_contains S) t.raw_origin))
 let L:= Lp f; let R:= Lq f; have ht : InTest K false (reflectedBox j 0 (Z p)) false L.val := leg_narrow (x:=f) j p u
 have hz:InTest K false (Z q) false R.val:= other_narrow (y:=f) q u
 have he:f.val∈ marksAlgebra (tent Y H) true:= ⟨f.property,fun _=> t.paid.2⟩ -- casing?
 let v:Marks (tent Y H) true:=⟨_,he⟩; have hv:fromStrict v=f:=rfl
 have hk:L∈N A s :=(mem_insideAt ..).2 ⟨⟨_,ht.widen,hull_support _ _ _ _⟩,fun _=>(show CovCover (tent Y H) L.val from (by unfold L; rw [←hv,leg_strict Y H]; exact (marksSpec true _).2 rfl))⟩
 have hn:R∈N C' s:=(mem_insideAt ..).2 ⟨⟨_,hz.widen,hull_support _ _ _ _⟩,fun _=>(show CovCover (tent Y H) R.val from (by unfold R; rw [←hv,reposition_strict Y H]; exact (marksSpec true _).2 rfl))⟩
 exact ⟨hk,hn,narrow_price Y H s ht (hull_support Λ l s _) hk,narrow_price Y H s hz (hull_support Λ l s _) hn,fun _ r=>inside_spread Y H G hk r,fun _ r=>inside_spread Y H G hn r⟩
end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LineCharge.housing
