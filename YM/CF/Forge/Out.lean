import YM.CF.Forge.Brook
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
local notation "G"=> SU.group
open Jet
variable {T:Tube G S}{s u:ℝ}{K:Stores S}{J:ChartRatio G}
namespace Monk
def atop (M: Monk G S)(A: Directions G c)(x:ℝ): Monk G S:={M with V:=Vmove x M.V A}
variable {M:Monk G S}{Y X: Support c}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma gain_e (F:E→L[ℝ] Directions G c) (M:Monk G S):
 (fun y:E => (M.atop (F y) x).pep x T s K q d l β w J r)=grandP T M.key K M.park x M.k q d (M.bush x) l (M.bell x) β J r s w (Vmove x M.V∘ F):=rfl
lemma rootU {u':ℕ} (F:E→L[ℝ] Directions G c) (p:Y∩RG.flags (temp x) M.V=M.key.flags) (O:Hos S u') -- undecl
 (ht:shovel S.patch+10 ≤ radiusB x)(hO:1000 ≤ radiusB x) (hr:Ready T x)(hz: spanO T x)(X:Support c) (hx: halo 15 X ⊆ Y)(he:M.key.flags ⊆ X)(hu:O.val.dome ((r+187+l)*radiusB x) ⊆ X):
 let A:= cusp M.key x M.V; let N:Monk G S:={M with key:=A}; let H:= (highlight X).comp F
 (fun i:E=> (M.atop (F i) x).pep x T s O.val q d l β w J r)= grandP T A O.val M.park x M.k q d (N.bush x) l (N.bell x) β J r s w (Vmove x M.V∘ H):=by
 intro A N H
 have hf:X∩ RG.flags (temp x) M.V=M.key.flags:= subset_antisymm ((inter_subset_inter (Subset.trans (halo_subset ..) hx) (Subset.refl _)) |>.trans (subset_of_eq p)) ?_ -- tune
 -- convert goal
 swap
 · intro i g; exact mem_inter.mpr ⟨he g,(mem_inter.mp (p.symm ▸ g)).2⟩
 change _=grandP T N.key O.val N.park x N.k q d _ _ _ _ _ _ _ _ (Vmove x N.V ∘ H); rw [←gain_e (F:=H) (M:=N)]
 funext y; exact pepr (x:=x) (q:=q) (w:=w) (s:=s) (d:=d) (β:=β) (high_p (x:=x) (X:=M) (Y:=N) (show Duo G S M N X from cusp_d M.key rfl hf M.V) (F y)) hr hO ht hz hu
lemma golden (P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:2 ≤ j)(hl:l≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(R:ChartRatio G)(hp:LocalRatio R)(w:ℝ)(hw:0<w) {γ:ℝ}(hγ:0<γ) :∃ N:ℝ,1 ≤ N∧∀ width ≥ N,∃ s A B:ℝ, 0<s∧0<A∧0<B∧∀ᶠ x in atTop, let L:= (2*j+200+l)*radiusB x; SafeX P Q R w γ width 0 j n x ∧∀ β∈ Set.Icc (y G Q.L x/2) (2*y G Q.L x), let t:= fiery G x Q.L; let Y:=B*Scales.p G Q.L x; let d:=width*t; 0<t ∧ 0<β∧0<Y∧wireP G (coupling β) d (A*t) A ≤ Y∧∀{c f:Side}(S:StepData c f)(U:Tube G S),Cert Q P S U x→∀M: Monk G S,sizedP G Q P S U M.park → (M.key.flags= RG.flags (temp x) M.V → MossX n l x M.key M.park U M.V M.k A d t q) ∧ ∀ X:Support c,X∩RG.flags (temp x) M.V=M.key.flags→∀ H:ℕ, L≤H→(M.key.dome H ⊆ X) →‖M.z‖ ≤ Y → ∀ O∈blip S M.key H, 0<O.val.shares→PointCharge U x w γ→∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E] (F:E→L[ℝ]Directions G c), ‖F‖≤1→ (∀ y, axl M.key.flags (temp x• F y)=temp x • F y)→ Allows n (fun i:E=> (atop M (F i) x).pep x U s O.val q d l β w R j) 0 (Real.exp (-γ/8*(Scales.p G Q.L x)^2 *O.val.shares)):=by
 obtain ⟨N,hN,hx⟩:=Esti.blaze P Q h n j l hn hj hl W W' q R hp w hw hγ; refine ⟨N,hN,fun width p=>?_⟩; obtain ⟨A,B,s,hA,hB,hs,Hx⟩:=hx width p; refine ⟨s,A,B,hs,hA,hB,?_⟩; filter_upwards [Hx,order_r P Q, PatchReads.reserve P Q, Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel Q+1010)] with x ⟨H,h⟩ hp hz hB; intro a; refine ⟨H,fun β v=>?_ ⟩
 obtain ⟨p,t,P₁,u,g⟩:=h _ v; intro l' y d; refine ⟨p,t,P₁,u,@fun c f S T E M e=>?_⟩; refine ⟨fun p=>(g S T E M.key M.key M.park M.V M.k e p).1,fun X ht U' hr hy hV O p0 h₀ hw D _ _ _ F hF hq=>?_⟩
 let A':= cusp M.key x M.V; let N: Monk G S:={M with key:=A'}; let R':= (j+187+l)*radiusB x
 let D':= M.key.dome R'; have hs:1000≤radiusB x:=by omega
 have hj':shovel S.patch+10 ≤ radiusB x:=by rw [E.got]; omega
 have hu: halo 15 D' ⊆ X:=by
    intro i t; obtain ⟨y,s,e⟩:=halo_spec.mp t; obtain ⟨z,t,h⟩:=halo_spec.mp s; refine hy (halo_spec.mpr ⟨z,t,(separation_triangle z y i).trans ?_⟩); unfold a at hr; unfold R' at h; simp_rw [Nat.add_mul,two_mul,Nat.add_mul] at *; omega
 have hb: M.key.flags ⊆ D':=fun _ p=> halo_subset R' M.key.place (mem_union_right _ p)
 have hP : O.val.place ⊆ M.key.place:=by rw [place_plots,place_plots]; intro i h; obtain ⟨j,p,l⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨j,(Esti.pack S O p0).subset_plots p,l⟩
 let Q':=(highlight D').comp F
 rw [rootU (Y:=X) F ht O hj' hs (hz S T E.got E.size E.funds.1) (hp S T E.got.symm E.funds.1) D' hu hb (Corona.halo_mono le_rfl hP)]
 let r':=(j+5)*radiusB x; have hr':r'≤ U':=by unfold a at hr; unfold r'; simp_rw [Nat.add_mul,two_mul,Nat.add_mul] at *; omega
 have hc:O.val.dome (r'+r') ⊆ X:=Subset.trans (Corona.halo_mono (by unfold r'; unfold a at hr; simp_rw [Nat.add_mul,two_mul,Nat.add_mul] at *; omega) hP) hy
 exact (g _ _ E A' O.val _ _ M.k e rfl).2 h₀ (cusp_b M.key O p0 ht hc hr') hw (N.bush x) (N.bell x) ((pi_norm_le_iff_of_nonneg P₁.le).mpr fun i=> (norm_le_pi_norm M.z i.val.val).trans hV) D Q' ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_one₀ (high_nn _) (norm_nonneg _) hF)) (fun z=>padT hu ht _ (hq z))
end Monk
end YM.CF.Forge
