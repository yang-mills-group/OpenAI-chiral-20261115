import YM.SU5.Reconstruction.Based.Profiles
import Mathlib.LinearAlgebra.DFinsupp
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
open CF.Pannier.Chancel
variable {k:ℕ}(K:Calibration)(W:Window.Family)(p:Fin k→ Cover)
local notation "B" => Stitches K W p S
local notation "F" => Family K
local notation "D" l:max t:max => scene S K W p l t (removal K) (creation K) (scalar K)
local notation "φ" => removal K
local notation "γ" => creation K
local notation "Γ" => raw S K W p
variable {Q:Family K}{μ:Multiset Cover}{l:List (Fin k)}
private lemma shelves (h:CRow K W p S l Q): Q∈ Submodule.span ℂ {f|∃ μ:Multiset Cover, B (removal K) (creation K) l μ f}:=by
 induction h with
 | gave=> exact Submodule.subset_span (show _∈ _ from ⟨_,Stitches.empty⟩)
 | zip=> exact Submodule.zero_mem _
 | glaze c _ h=> exact Submodule.smul_mem _ _ h
 | fuse _ _ h p=> exact Submodule.add_mem _ h p
 | @pair i y c d b a f l ea eb u v p' z h _ ih=>
    let T:= Submodule.span ℂ {w:F|∃ μ:Multiset Cover,B (removal K) (creation K) (i::l) μ w}
    refine Submodule.span_induction (p:=fun t _=> (φ (p i) c a*γ y d b)*t∈ T) (fun t e=>?_) (by rw [mul_zero]; exact T.zero_mem) (fun _ _ _ _ q v=>by rw [mul_add]; exact T.add_mem q v) (fun _ _ _ v=>by rw [Algebra.mul_smul_comm]; exact T.smul_mem _ v) ih
    obtain ⟨μ,A⟩:=e; exact Submodule.subset_span (show _∈ _ from ⟨_,A.put i y c d a b ea eb u v p' z h⟩)
private lemma typing (h:Q∈ Lode K W p S) {g:PairsC→ℂ} (t:Coeff false S g) : scalar K g*Q∈ (⨆ μ:Multiset Cover, raw S K W p μ):=by
 let U:= ⨆ μ:Multiset Cover, raw S K W p μ; let T:= scalar K g
 refine Submodule.span_induction (p:=fun f _=> T*f∈ U) (fun v u=>?_) (by rw [mul_zero]; exact U.zero_mem)
   (fun _ _ _ _ p q=>by rw [mul_add]; exact U.add_mem p q) (fun _ _ _ p=>by rw [Algebra.mul_smul_comm]; exact U.smul_mem _ p) h
 obtain ⟨L,p',t',r⟩:=u; refine Submodule.span_induction (p:=fun f _=> T*f∈ U) (fun v u=>?_) (by rw [mul_zero]; exact U.zero_mem) (fun _ _ _ _ p q=>by rw [mul_add]; exact U.add_mem p q) (fun _ _ _ p=>by rw [Algebra.mul_smul_comm]; exact U.smul_mem _ p) (shelves K W p r)
 obtain ⟨μ,C⟩:=u; have h':T*v∈ D L μ:= Submodule.subset_span ⟨v,g,C,t,rfl⟩; exact (show Γ μ ≤ U from le_iSup Γ μ) (Submodule.subset_span (show T*v∈ _ from ⟨L,p',t',h'⟩))
lemma reading_all (S:Finset Cover) : Filigree K W p S=(⨆ μ:Multiset Cover,raw S K W p μ):=by
 refine le_antisymm (Submodule.span_le.mpr ?_) (iSup_le (fun μ=>visible K W p μ S)); rintro _ ⟨x,tx,g,q,rfl⟩; exact typing K W p g q

noncomputable def Breakdown (Q:Family K) (A₀:(Multiset Cover) →₀ Family K):Prop:=(∀ μ:Multiset Cover,A₀ μ∈ Γ μ) ∧ (∑ a∈ A₀.support,A₀ a)=Q
lemma exists_profiles (p₀:Q∈ Filigree K W p S):∃ A, Breakdown (S:=S) K W p Q A:=(Submodule.mem_iSup_iff_exists_finsupp Γ _).1 ((reading_all K W p S) ▸ p₀)
end YM.CF.Buffered.Afterglow.Rooted
