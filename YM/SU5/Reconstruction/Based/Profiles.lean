import YM.SU5.Reconstruction.Based.Program
import YM.SU5.FiniteGaugeData.Pannier.Filigree
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
/- Canonical task patterns. **Every Profile** identified by a multiset of matter sites
(Cover, not yet taking Torus). Need keep support restrictions & separation vs pure-gauge splits. -/
open CF.Pannier.Chancel
variable {k:ℕ}(K:Calibration)(W:Window.Family)(p:Fin k→ Cover)
abbrev Atoms (K:Calibration) := Cover → SpinIdx→ SU.Slot → Family K
inductive Stitches (K:Calibration)(W:Window.Family)(p:Fin k→ Cover)(S:Finset Cover)(ρ π:Atoms K): List (Fin k) → Multiset Cover → Family K→Prop where
 | empty : Stitches K W p S ρ π [] 0 1
 | put (i:Fin k)(y:Cover)(c d:SpinIdx)(a b:SU.Slot){l μ f} :
    family a=W → family b=W→ c∉ plusHalf → d∈ plusHalf→
     nodeC y ∈ S→ nodeC (p i)∈ S→ (∀ t,y≠p t)→ Stitches K W p S ρ π l μ f→
      Stitches K W p S ρ π (i::l) ((p i) ::ₘ y ::ₘ μ) ((ρ (p i) c a*π y d b)* f)
local notation "ρ" => removal K
local notation "π" => creation K
local notation "B" => Stitches K W p S
local notation "F" => Family K
variable {Q:Family K}{μ:Multiset Cover}{l:List (Fin k)}
namespace Stitches
variable {K W p R} {ρ₀ π₀:Atoms K}
lemma gives (h:Stitches K W p S (removal K) (creation K) l μ Q) : CRow K W p S l Q := by
 induction h with | empty=> exact .gave | put i y c d a b e q k v w u r _ h=> exact .pair i y c d b a e q k v w u r h
lemma reaches (h: B ρ₀ π₀ l μ Q): ∀ x∈ μ,nodeC x∈ S:=by
 induction h with
 | empty => simp
 | put i y c d a b _ _ _ _ g e _ _ ih=> rintro x p; rw [Multiset.mem_cons,Multiset.mem_cons] at p; rcases p with u|u|u; rwa [u]; rwa [u]; exact ih _ u
lemma count_of_anchor (i:Fin k)(v:Injective p)(h:B ρ₀ π₀ l μ Q) : μ.count (p i)= l.count i:=by
 induction h with
 | empty=> simp
 | @put j y c d a b l μ f _ _ _ _ _ _ r _ ih=>
    simp_rw [Multiset.count_cons]; by_cases h:j=i
    · subst j; simp [Ne.symm (r i), ih];
    · have e:= (fun u:p j=p i=> h (v u)); simp [Ne.symm (show p j≠p i from e),Ne.symm (r i),ih,h] -- tune i syntax
lemma anchor_here (e:l≠[]) (q:B ρ₀ π₀ l μ Q):∃ i,p i∈ μ:=by cases q with | empty=> exact False.elim (e rfl) | put i=> exact ⟨i,Multiset.mem_cons_self ..⟩
lemma creation_here (e:l≠[])(q:B ρ₀ π₀ l μ Q):∃ x∈ μ,x∉ Set.range p:=by
 cases q with
 | empty=> exact False.elim (e rfl)
 | put i y c d a b ea eb t v w z h _=> exact ⟨y,Multiset.mem_cons_of_mem (Multiset.mem_cons_self ..), fun ⟨i,k⟩=> h i k.symm⟩
end Stitches
variable (S)
noncomputable def scene (l:List (Fin k))(μ:Multiset Cover)(ρ₁ π₁:Atoms K)(A:(PairsC→ℂ) → Family K) : Submodule ℂ (Family K):=
 Submodule.span ℂ {x | ∃ (f:Family K)(F₁:PairsC→ℂ),Stitches K W p S ρ₁ π₁ l μ f∧ Coeff false S F₁∧ x=A F₁*f}
/-- Finally not yet requiring gauge neutral. -/
noncomputable def component (μ:Multiset Cover) (ρ₁ π₁:Atoms K) (A : (PairsC → ℂ) → Family K): Submodule ℂ (Family K):=
 Submodule.span ℂ {x | ∃ l:List (Fin k), l ≠ [] ∧ l.Nodup∧ x∈ scene S K W p l μ ρ₁ π₁ A}
noncomputable def raw (μ:Multiset Cover):= component S K W p μ (removal K) (creation K) (scalar K)
variable {S}
noncomputable def connected (μ:Multiset Cover):= component S K W p μ (rootRemove R K) (rootCreate R K) ((scalar K) ∘ ask R)
private lemma scene_fili (k': l≠[])(h:l.Nodup): scene S K W p l μ ρ π (scalar K) ≤ Filigree K W p S:= by
 apply Submodule.span_le.mpr; rintro _ ⟨f,g,t,k,rfl⟩; apply Submodule.subset_span; exact ⟨f,g,(Submodule.subset_span (show f∈ _ from ⟨l,k',h,t.gives⟩)), k,rfl⟩ -- check
lemma visible (μ:Multiset Cover)(S:Finset Cover): raw S K W p μ ≤ Filigree K W p S:=by
 apply Submodule.span_le.mpr; rintro v ⟨l,h,t,e⟩; exact scene_fili K W p h t e
lemma weave_on_charge (q:B (rootRemove R K) (rootCreate R K) l μ Q): Test R K false false Q:=by
 induction q with | empty=> exact Test.one | put i y c d a b _ _ x z e v _ _ ih=> exact Test.mul (Test.mul (.remove a x v) (.create b z e)) ih
lemma toll_on_charge (q:Q∈ scene S K W p l μ (rootRemove R K) (rootCreate R K) ((scalar K)∘ ask R)): Test R K false false Q:=by
 refine Submodule.span_induction (p:=fun x _=> Test R K false false x) (fun v u=>?_) (.zero) (fun _ _ _ _ v q=>.add v q) (fun i _ _ v=>.scale i v) q
 obtain ⟨f,g,t,h,rfl⟩:=u; exact Test.mul (Test.loops h) (weave_on_charge R K W p t)
lemma paid_on_charge (q: Q∈ connected R K W p μ): Test R K false false Q:=by
 refine Submodule.span_induction (p:=fun x _=> Test R K false false x) (fun v u=>?_) (.zero) (fun _ _ _ _ v q=>.add v q) (fun i _ _ v=>.scale i v) q
 obtain ⟨l,_,_,t⟩:=u; exact toll_on_charge R K W p t
abbrev Populated(K:Calibration)(W:Window.Family)(p:Fin k → Cover)(S:Finset Cover)(μ: Multiset Cover)(ρ₁ π₁:Atoms K):Prop:=∃l:List (Fin k), l≠ []∧ l.Nodup∧ ∃ f,Stitches K W p S ρ₁ π₁ l μ f
lemma was_here (ρ₁ π₁:Atoms K)(A : (PairsC→ℂ)→Family K){v:Family K}(u:v≠(0:Family K))(t:v∈ component S K W p μ ρ₁ π₁ A): Populated K W p S μ ρ₁ π₁:=by
 by_contra r
 suffices p':component S K W p μ ρ₁ π₁ A ≤ ⊥ from u ((Submodule.mem_bot ℂ).mp (p' t))
 apply Submodule.span_le.mpr; rintro v ⟨l,h,e,u⟩
 suffices t:scene S K W p l μ ρ₁ π₁ A≤ ⊥ from t u
 apply Submodule.span_le.mpr; rintro _ ⟨f,F₁,z,_,_⟩; exact False.elim (r ⟨l,h,e,f,z⟩)
end YM.CF.Buffered.Afterglow.Rooted
