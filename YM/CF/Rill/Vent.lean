import YM.CF.Rill.Peer
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Atala
variable {a b':ℝ}
lemma sapien{L:Teller G}(Y:HomeL c f)(h:Agrees F Y.1 V)(p:F∩ RG.flags (temp x) V ⊆ M.key.flags)(δ:(wires M.key.flags).biUnion pinPos=M.key.flags)(hz:0<temp x)(hv:1000≤radiusB x)(g:L.Funds S T)(j:r≤18)(v:0<d)(k:2*d<firstRadius G)(P:MossX l r x (ray M.key x V) M.park T V M.k K d (fiery G x S.patch.L) q) (u:0< Y.2.2.1) (t:a<e)(hs:b<b')(hp:0<b)(he:halo ((r+70)*radiusB x) E⊆ F) :
 let R:Monk G S:={(monkD M Y) with key:=ray M.key x V,V:=V}
 Bell S R x T q d r Y.2.2.1 a b→ MarkP M E x e b' Y r l T q d:=by
 intro R g'; have hh:Beat (monkD M Y) R F:=⟨last_v M.key δ p,fun _ _=>rfl,fun _ _=>rfl,fun _ _=> Iff.rfl, h,fun _ _=>rfl,fun _ _=>rfl⟩
 refine ⟨uplift hh P.ready h p g' t hs hp hv he,fun i v' => shoot Y h p δ hz hv g j v k P u i ?_⟩
 intro w t; obtain ⟨z,h,p⟩:=halo_spec.mp v'; obtain ⟨a,u,k⟩:=halo_spec.mp t; rw [mem_singleton.mp u] at k; exact he (halo_spec.mpr ⟨z,h,(separation_triangle z a w).trans (by rw [mem_singleton.mp u]; simp_rw [Nat.add_mul] at *; omega)⟩) -- tune
private lemma compactS (P:Set (Config G c))(F: Support c)(A:Set (Config G c))(p:IsOpen A)(h:∀ U∈P,moist U F⊆ A):∃ H:Set (Config G c),P⊆ H∧ IsOpen H∧H⊆ A∧∀ U∈H,moist U F⊆ H:=by
 let Z:=colors («G»:=G) F; have he:Continuous Z:= color_c F; let B:=Z '' Aᶜ; let M:=Z ⁻¹' Bᶜ; have hv:IsOpen M:= ((IsCompact.isClosed (p.isClosed_compl.isCompact.image he)).isOpen_compl).preimage he
 refine ⟨M,fun U e k=>?_,hv,fun i p=>?_,fun U h t v=>?_⟩ -- tune
 · obtain ⟨W,e',g⟩:=k; exact e' (h U e ((of_color F U W).mpr g.symm))
 · by_contra k; exact p (Set.mem_image_of_mem _ k)
 change Z t ∉ B; rw [← show Z U=Z t from (of_color F U t).mp v]; exact h
lemma latticeFieldEstimates {P:Set (Config G c)}{J:Set (Config G f × Foil f)}(hq:b<firstRadius G)(hu:IsCompact J) (h:∀ U∈P,∀ V∈moist U F,∀ t∈J, MarkP M E x e b (V,t) r l T q d):∃ A:Set (Config G c),P⊆ A ∧ IsOpen A∧(∀ U∈A,moist U F⊆ A)∧∀ U∈A,∀ t∈J,MarkP M E x e b (U,t) r l T q d:=by
 let Z: Set (HomeL c f):={Q|MarkP M E x e b Q r l T q d}; have hp:IsOpen Z:= isOpen_iff_mem_nhds.mpr fun i p=> mead p hq; let A:Set (Config G c):={V|∀ t∈J,(V,t)∈Z}
 have hh(U)(p:U∈P)(V:Config G c)(v:V∈moist U F):V∈interior A:=by
    change V∈interior A; apply mem_interior_iff_mem_nhds.mpr
    have he:{V} ×ˢ J ⊆ Z:=fun Q q=>by rcases Q with ⟨x,y⟩; obtain ⟨t,g⟩:= q; have hx:x= V:= Set.mem_singleton_iff.mp t; subst x; exact h U p V v y g
    obtain ⟨K,L,p',v',w,z,t⟩:=generalized_tube_lemma isCompact_singleton hu hp he; exact _root_.mem_nhds_iff.mpr ⟨K,(fun i u x h=>t ⟨u,z h⟩),p',w (Set.mem_singleton V)⟩
 obtain ⟨B,p,q,j,hP⟩:= compactS P F (interior A) isOpen_interior (fun i v y p=>hh i v y p); exact ⟨B,p,q,hP,fun i v t k=> (interior_subset (j v)) t k⟩
end YM.CF.Rill
