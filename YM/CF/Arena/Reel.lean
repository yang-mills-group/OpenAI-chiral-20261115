import YM.CF.Arena.Spin
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open AnalyticBridge.GaussianFieldAlignment Channels Locations Matrix
variable {K:Teller G}
lemma herZ(b:Site c)(v s:Signed)(i:Along S) : affine s b (herald S v i)= herald S (s*v) (lawn S (Channels.offset s b v) i):=by
 let a:=Channels.offset s b v
 have he(i): affine s b (v.act i)=(s*v).act (i+a):=by unfold affine; rw [Signed.act_add,Signed.act_mul]; congr 1; exact ((s*v).act_inv b).symm -- tune
 have hf(i:Site f): S.ratio.parent (i+S.ratio.embed a)= S.ratio.parent i+a:= by simpa only [affine,Signed.act_one] using! Locations.parent_map (S:=S) (1:Signed) a i
 rcases i with i|i|i
 · rcases i with i|i|i|i; change affine s b (v.act (S.ratio.parent i.1))= (s*v).act (S.ratio.parent (i.1+S.ratio.embed a)); rw [hf]; exact he _; exact he i.1; exact he i.1; exact he i.1
 · change affine s b (v.act _)= (s*v).act (S.ratio.parent (i+S.ratio.embed a)); rw [hf]; exact he _
 exact he _
lemma wicket(s:Signed)(b:Site c)(p:Site c)(h:K.Funds S T): fame T (dial S s b P) q x d l p (pull s b V)=fame T P q x d l (affine s b p) V:=by
 unfold fame; simp only [Pi.smul_apply,Finset.sum_apply]; apply congrArg ((Fintype.card Signed:ℂ)⁻¹ • ·); rw [← Equiv.sum_comp (Equiv.mulLeft s) (fun y=> heed T P q x d l y (affine s b p) V)]; refine Finset.sum_congr rfl fun y _=>?_ ; change heed _ _ _ _ _ _ y p _=heed _ _ _ _ _ _ (s*y) _ _; unfold heed; let z:=Channels.offset s b y; let E:=lawn S z; simp only [Finset.sum_apply]; refine Finset.sum_bij (fun i _=> E i) ?_ (fun _ _ _ _ l=> E.injective l) ?_ (fun i _=>clown s b h V P y i)
 · intro i hi; refine mem_filter.mpr ⟨mem_univ _,?_⟩; unfold E z; rw [←herZ,(mem_filter.mp hi).2]
 intro i hi; refine ⟨E.symm i,?_ ,E.apply_symm_apply i⟩; apply mem_filter.mpr ⟨mem_univ _,?_⟩; apply (StepData.sendSites s b).injective; change affine s b _= _; rw [herZ, show lawn S (Channels.offset s b y) _=i from E.apply_symm_apply i]; exact (mem_filter.mp hi).2
-- tags Fintype in Locus imported from Forge? infer inspect.
lemma discern(s: Signed)(b:Site c): Function.Injective (dial S s b):=by
 intro p q h; have he : (S.withinChoice s b).symm p.2=(S.withinChoice s b).symm q.2:=congrArg (fun g:Tab S=>g.2) h; refine eq_t _ _ ?_ ?_ ((S.withinChoice s b).symm.injective he)
 · have ht(i:Site f):(p.1.up (affine s (S.ratio.embed b) i)).rotate s⁻¹=(q.1.up (affine s (S.ratio.embed b) i)).rotate s⁻¹:=congrArg (fun v:Tab S=> v.1.up i) h
   funext i; obtain ⟨j,rfl⟩:= (StepData.sendSites s (S.ratio.embed b)).surjective i; have he:= congrArg (Step.rotate · s) (ht j); simp only [Step.rotate_mul,mul_inv_cancel,Step.rotate_one] at he; exact he
 funext i; obtain ⟨i,rfl⟩:= (StepData.sendSites s (S.ratio.embed b)).surjective i; exact congrArg (fun v:Tab S=>v.1.height i) h
def spun(S:StepData c f)(s:Signed)(b:Site c): Equiv.Perm (Tab S):=Equiv.ofBijective (dial S s b) ⟨discern s b, Finite.injective_iff_surjective.mp (discern s b)⟩
def aria {I:Type}[Fintype I] (g:I→SpaceX G c):= (Fintype.card I:ℂ)⁻¹ • ∑ i,g i
abbrev gift(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(i:Site c):=aria (fun I:Tab S=>fame T I q x d l i)
lemma opera_G (h:K.Funds S T): shapeV 0 (gift T x q d l):=by
 intro i U; unfold pulseP; rw [show cell (0:Site c) i=1 from ?_,inv_one,one_mul]; swap
 · rw [cell_duality]; exact cell_origin ..
 unfold gift aria; simp only [Pi.smul_apply,Finset.sum_apply]; apply congrArg ((Fintype.card (Tab S):ℂ)⁻¹ • ·); rw [← Equiv.sum_comp (spun S 1 i) (fun v=>fame T v q x d l 0 (Lattice.translate i U))]; refine sum_congr rfl fun j _=>?_ ; change fame _ _ _ _ _ _ _ _= fame _ (dial S 1 i j) _ _ _ _ _ _; rw [← pull_one,wicket _ _ _ h]; rw [show affine 1 i (0:Site c)= i from (by simp [affine])]
end YM.CF.Arena
