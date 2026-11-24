import YM.CF.Rink.Cape
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
open Affine Reine AnalyticBridge.Annulus1AD
lemma av_a(s:Signed)(f g:Signed→ℝ)(h:∀ k,f k=g (s*k)): averaged f=averaged g:=by unfold averaged; simp_rw [h]; rw [show (∑ k,g (s*k))=_ from Equiv.sum_comp (Equiv.mulLeft s) g] -- tune binder rhs
lemma caps_u (A:Stores S)(x:ℝ)(s v:Signed)(b:Site c)(j:ℕ)(i:Dill S): i∈tie (whim x j (Locations.book s b A) v)↔ stepZ S (Channels.offset s b v) i∈ tie (whim x j A (s*v)):=by unfold whim; simp only [hop_x,mem_filter,true_and,mem_univ,dome_map]; exact (herZ b v s (Sum.inl i : Along S)) ▸ Iff.rfl -- tune redex
section
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(A:Stores S)(j:ℕ)
abbrev settle :=-β * averaged (fun v=>∑ i∈tie (whim x j A v), fence T x M q d l β v i)
lemma offer (h:K.Funds S T)(a g D z:ℝ) (p:Volo S n a g D z)(ht: FuelG ℝ (fun _=>M.sent x T q d l β) 0 n D)(w:ℝ)(hp: spanO T x)(he: 0<temp x)(hf:0 <fiery G x S.patch.L)(hg:fiery G x S.patch.L ≤ a/2)(H:M.key.flags=RG.flags (temp x) M.V) (m:shovel S.patch +10 ≤ radiusB x)(hz:M.silver x T a A q d l β w j≠0): M.tin x T a A q d l β j=settle T x M q d l β A j:=by
 let F:=M.sent x T q d l β; let V:= M.V; let X:=M.key; let N:=M.park; let s:=M.k; let r(u):=whim x j A u; let B:= M.fuel x T q d l β; let K:= liftN T x V s X N q d (M.bush x) l; let W(b):=wheel X N T x s q d (M.bush x) b V; let Y:= W B; let Z:= W K
 have hQ: total X x q F (obv x j 110 A) ≠0:=fun P=> (left_ne_zero_of_mul (left_ne_zero_of_mul hz)) P -- tune
 change -β*averaged (fun u:Signed=> caseP T x X s q a F V u (r u)- columnP u Y (r u)+ columnP u Z (r u))=_
 refine congrArg (-(β)*·) (congrArg averaged (funext fun i=>?_)); rw [show caseP _ _ _ _ _ _ _ _ _ _=_ from keeps_f (x':=(0:ℝ)) T (fun _:ℝ=> F) V (j*radiusB x) ((j+110)*radiusB x) p ht i hp H m hf he hg (by rw [Nat.add_mul]; omega) (funds_branch h) hQ]; exact (mirX T x M i (r i) F (fun i=>media i Y) (fun i=>media i Z)).symm
variable (h:K.Funds S T)(p: FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)
include h p hm hf
lemma tally_s(s:Signed)(b:Site c): settle T x (clue S s b M) q d l β (Locations.book s b A) j= settle T x M q d l β A j:=by apply congrArg (-(β)*·); apply av_a s; intro v; exact Finset.sum_equiv (stepZ S (Channels.offset s b v)) (caps_u A x s v b j) (fun i _=> fence_s T x M q d l β h p hm hf s v b i)
lemma tally_e(H: Reef.Rare T.up): settle T x (cedar M) q d l β A j=settle T x M q d l β A j:=by unfold settle; simp_rw [fence_e T x M q d l β h p hm hf H]
lemma tally_g(g:Site c→ SU.group.El): settle T x (shiftZ g M) q d l β A j=settle T x M q d l β A j:=by unfold settle; simp_rw [fence_g T x M q d l β h p hm hf g]
end
end YM.CF.Rink
