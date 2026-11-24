import YM.CF.Graph.Learn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
variable {α:Type*}{m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z:ℝ}{P:Grasp Y B e}{hP:Pearl P}
variable (V:GramM (mid m B))(S:Loom (mid m B))
variable (Q: Pic.Span hP K b v c l r' n)(H:SkinT V S e)
lemma bonB {R:GramM N}{v k η r C a b d:ℝ}(X:Ledger k v η r C R)(h:R.path.Bounds R.funds a b d) : Ward R:= ⟨⟨_,_,_,h⟩,fun i=> by obtain ⟨f,h,-⟩:=X.reg.weight; exact ⟨_,_,h i⟩,fun i=> by obtain ⟨f,h,-⟩:=X.slip.weight; exact ⟨_,_,h i⟩,fun i=> by obtain ⟨f,h,-⟩:=X.force.weight; exact ⟨_,_,h i⟩⟩
include H Q
lemma integrable_s (h:Ward V)(O:Opt (α:=α) (mid m B))(p:n ≤ (mid m B).val) : Integrable (recW O P V S) (city _) ∧ Integrable (baseW O P V S) (city _):=by
 obtain ⟨t,n',T⟩:=H.wave; have hu:= Q.plan m p; have ht:=Girt.sailW V h hP Q.stmt Q.eP Q.p n' S T hu.1; let X: Envelope (recX P V S):= pole_w (denZ V P S) (T:=fun v=> Complex.exp (-V.v) • v) (by fun_prop) ht; have hx:= earned O _ X; refine ⟨Integrable.of_bound hx.meas.aestronglyMeasurable _ (Eventually.of_forall hx.cost.choose_spec),?_⟩; have hv:= earned O _ (moon hP Q.stmt Q.eP Q.p hu.1 V S H); exact ((worth h).integrable _).smul_bdd _ hv.meas.aestronglyMeasurable (Eventually.of_forall hv.cost.choose_spec)
def phM (V:GramM (mid m B))(O:Opt (α:=α) (mid m B))(P:Grasp Y B e)(S:Loom (mid m B)):ℝ:=∫ x,‖recW O P V S x-baseW O P V S x‖∂city _
lemma cents(W:Ledger R u η r C V)(a:0<r)(t:0≤vA)(k':0≤k)(h:1≤R)(g:V.path.Bounds V.funds μ D L')(hv:0≤V.beta)(w':0≤w)(vL:w≤V.funds.linear)(l:n ≤ (mid m B).val)(hC:0≤C)(hy:0≤y)(f:∀ T∈Lace V, Gall.Yep k (mateK (mid m B)) (changeM (m:=m) P T.1 V.J.M) (y*Kea.angel m P V.J.M))(f':∀ T∈Lace V,∀ i:LeanV (Single (mid m B)),Pays k (drawT (spar j V.J.M T.1) i) R)(b:∀ T∈Lace V,HelpP T.1 vA r)(l':pittance (mid m B) vA C≤1)(O:Opt (α:=α) (mid m B))(hp:‖gain O.R‖ ≤ (mid m B).val^2): let z:= baton (mid m B) u vA C k
     phM V O P S ≤ drip V P*(z*y*feeP O k)+ lite O *Real.exp (flagT (mid m B) u η C-kinetic (More (mid m B)) V.p D L' V.beta w):=by
 intro z; let N:=mid m B; let A:=Kea.angel m P V.J.M; let Y:=lite O * Real.exp (flagT N u η C-kinetic (More N) V.p D L' V.beta w); have he:0≤Y:=by unfold Y lite; positivity
 -- dim on flag complement zero
 let F(x):= recW O P V S x-baseW O P V S x; let K:=z*(y*A)*feeP O k
 have hh (x): ‖F x‖ ≤ dim V x*K + Y:=by by_cases ht:x∈ Lace V; exact le_trans (pall_b V S Q H x O l ht W (b _ ht) t a.le (zero_le_one.trans h) k' hC hp (f _ ht) hy (f' _ ht) l') (le_add_of_nonneg_right he); rw [dim, Set.indicator_of_notMem ht,zero_mul,zero_add]; exact road_b V S Q H x O l ht W a.le h hC hp g hv w' vL
 have ht:= bonB W g; obtain ⟨p,q⟩:= integrable_s V S Q H ht O l; let μ:=city N; have hA:= ((worth ht).integrable μ).mul_const K; apply le_trans (integral_mono (p.sub q|>.norm) (hA.add (integrable_const _)) hh); apply le_of_eq; change (∫ x, dim V x*K + Y ∂μ)=drip V P*(z*y*feeP O k)+ Y; change Integrable (fun x=>dim V x*K) (city _) at hA; unfold μ N; rw [integral_add hA (integrable_const _), integral_mul_const,integral_const,probReal_univ,one_smul]; unfold drip K angle Y A; ring -- tune
end YM.CF.Graph
