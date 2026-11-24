import YM.CF.Forge.Toast
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
-- synthesizing an admissible book from merely local optical evidence; don't treat equality and changed flags as differentiable
variable {D X Y:Support c} {t:ℝ}{U V:Config G c}
def wires (D:Support c): Finset (Bond c):= univ.filter fun i=>pinPos i⊆D
lemma band(i:Cell c): touched i=pinPos (i.1,i.2.val.1)∪pinPos (i.1+Lattice.step i.2.val.2,i.2.val.1):=by ext x; simp [touched,pinPos,square_corners,add_right_comm i.1 (step i.2.val.2)]; tauto
lemma star_p (H:Support c)(h:H⊆RG.flags t U) (p: X∩RG.flags t U=H)(hx:inspected H ⊆ X): (wires H).biUnion pinPos=H:=by
 apply subset_antisymm (biUnion_subset.mpr fun i p=>(mem_filter.mp p).2) _; intro i l
 obtain ⟨k,u,v⟩:= (flags_spec ..).mp (h l)
 have hz:touched k⊆ H:=by
    intro j e; have hv:j ∈ inspected H:=mem_union_right _ (mem_biUnion.mpr ⟨k,mem_univ _,?l⟩); swap; · rw [if_neg]; exact e; exact fun h=> disjoint_left.mp h l u
    rw [←p]; exact mem_inter.mpr ⟨hx hv,(flags_spec ..).mpr ⟨k,e,v⟩⟩
 rw [band] at u hz; obtain ⟨z,t⟩:= Finset.union_subset_iff.mp hz; rcases mem_union.mp u with e|e; exact mem_biUnion.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,z⟩,e⟩; exact mem_biUnion.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,t⟩,e⟩
-- synthetic for atlas compactness; FLAGS actual even if U-external or changes D strict; inflate place via noise hull. Supports only X matter
variable (A:Stores S)
def ray(x:ℝ)(U:Config G c): Stores S:=⟨A.costs,A.aisles∪ wires A.flags,RG.flags (temp x) U⟩
lemma last_v (h:(wires A.flags).biUnion pinPos=A.flags)(v:X∩RG.flags (temp x) V ⊆ A.flags) (i:Site c)(p:i∈X): i∈A.place ↔ i∈(ray A x V).place:=by
 simp only [Stores.place,ray, union_biUnion,h,mem_union]; have hx : i∈ RG.flags (temp x) V → i∈ A.flags:=fun k=>v (mem_inter.mpr ⟨p,k⟩); tauto
-- real extension unchanged synt
abbrev cusp (A:Stores S)(x:ℝ)(U:Config G c):Stores S:= { A with flags:=RG.flags (temp x) U}
lemma cusp_d {M:Monk G S}(p:M.key=A)(h:X∩ RG.flags (temp x) V=A.flags) (K:Config G c) : Duo G S {M with V:=K} {M with V:= K,key:=cusp A x V} X:=by
 have he(i:Site c)(p:i∈X):i∈A.flags ↔ i∈RG.flags (temp x) V:=by rw [←h,mem_inter,and_iff_right p]
 refine ⟨⟨fun i u=> ?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩,fun i k=>p.symm ▸ Iff.rfl,fun i k=> p.symm ▸ Iff.rfl,fun i k=>?_⟩
 · change _ ∈ M.key.place ↔ i∈ (cusp A x V).place; rw [p]; simp only [Stores.place,cusp,mem_union,he i u]
 change i∈M.key.flags ↔ _; rw [p]; exact he i k
lemma cusp_b(O: Hos S r)(hO:O∈ blip S A r)(h:X∩ RG.flags (temp x) V=A.flags)(hv:O.val.dome (v+v) ⊆ X)(hp:v ≤ r): Packet O.val (cusp A x V) v:=by
 let Y:=temp x; let D:=cusp A x V; have hz:= (Esti.pack S O hO).carry hp
 refine ⟨subset_trans hz.subset_plots ((plots_sub A D).mpr ⟨fun _ k=>k,fun _ k=>k, h ▸ inter_subset_right⟩),fun i k w=>?_⟩; by_cases s:planted A i; exact hz.alone i s w
 rcases i with (i|i)|i; exact (s k).elim; exact (s k).elim
 apply disjoint_left.mpr; intro j t q; change j∈halo v {i} at t; obtain ⟨z,hp,t⟩:=halo_spec.mp t; obtain ⟨p,l,q⟩:=halo_spec.mp q; rw [mem_singleton.mp hp] at t; have he:i∈X:=hv (halo_spec.mpr ⟨p,l,(separation_triangle p j i).trans (Nat.add_le_add q ((separation_comm ..).trans_le t))⟩); exact s (show i∈ A.flags from h ▸ mem_inter.mpr ⟨he,k⟩)
section shadow
local notation "G" => SU.group
variable {A} {T:Tube SU.group S} {i:Type}[NormedAddCommGroup i][NormedSpace ℝ i] {M:Monk SU.group S}
abbrev highlight (X:Support c) : Directions G c→L[ℝ]Directions G c:= ContinuousLinearMap.pi fun x=>if pinPos x⊆ X then ContinuousLinearMap.proj x else 0
lemma high_nn(X:Support c): ‖highlight X‖ ≤ 1:=by refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>?_ ; rw [one_mul]; refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=>?_ ; unfold highlight; rw [ContinuousLinearMap.pi_apply]; split; exact norm_le_pi_norm i j; rw [ContinuousLinearMap.zero_apply,norm_zero]; exact norm_nonneg _
lemma high_read(X:Support c)(V:Config G c)(F:Directions G c):Agrees X (Vmove x V F) (Vmove x V (highlight X F)):=by
 intro e h p; have he:pinPos e ⊆ X:= insert_subset h (singleton_subset_iff.mpr p); change SU.group.lieExp _ * _=SU.group.lieExp (temp x•highlight X F e)* _; rw [highlight,ContinuousLinearMap.pi_apply,if_pos he]; rfl
lemma padT (p: halo 15 X⊆Y) {U:Config SU.group c} (h: Y∩ RG.flags t U = D) (v: Directions SU.group c) (g:axl D (t • v)=t • v): axl (RG.flags t U) (t • highlight X v)= t • highlight X v:=by
 funext e; unfold axl; split; next hx =>
    by_cases k:pinPos e⊆ X; swap; · simp only [highlight,Pi.smul_apply,ContinuousLinearMap.pi_apply,if_neg k, ContinuousLinearMap.zero_apply,smul_zero]
    have hp : Set.MapsTo (id : Site c → Site c) (↑X∩ ↑(halo 15 (RG.flags t U))) ↑(halo 15 D):=by
       intro x h'; obtain ⟨a,l,w⟩:=halo_spec.mp h'.2; rw [← h]; have ht:a∈ Y:=p (halo_spec.mpr ⟨x,h'.1,(separation_comm ..).trans_le w⟩); exact halo_spec.mpr ⟨a,mem_inter.mpr ⟨ht,l⟩,w⟩
    have hz : _ ∨ _:=hx.imp (fun t=>show e.1∈ halo 15 D from hp ⟨k (mem_insert_self ..),t⟩) (fun t=>show e.1+step e.2∈ halo 15 D from hp ⟨k (mem_insert_of_mem (mem_singleton_self _)),t⟩)
    have ht:= congrFun g e; unfold axl at ht; rw [if_pos hz] at ht; rw [Pi.smul_apply,highlight, ContinuousLinearMap.pi_apply,if_pos k,ContinuousLinearMap.proj_apply]; exact ht
 rfl
lemma high_p {X Y:Monk G S}(p:Duo G S X Y D)(v: Directions SU.group c): Duo G S {X with V:= Vmove x X.V v} { Y with V:=Vmove x Y.V (highlight D v)} D :=by
 refine ⟨⟨p.road,p.fr,p.fe,p.trunks,?_,p.data,p.color⟩,p.cost,p.aisles,p.flags⟩; intro e u g
 refine Eq.trans ?_ (high_read D Y.V v e u g); unfold Vmove increment; dsimp only; rw [p.view e u g] -- tune target with let
end shadow
end YM.CF.Forge
