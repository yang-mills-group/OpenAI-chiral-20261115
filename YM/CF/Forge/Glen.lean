import YM.CF.Forge.Seal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
open Jet
variable {A F E H α:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup H][NormedSpace ℝ H][TopologicalSpace α]
variable {f:A→α→ Config G c→F}{W Y:Set (Config G c)}{I:Finset (Bond c)}{X:Support c}{n:ℕ}{C:ℝ}
def ciB(X:Support c):Finset (Bond c):=univ.filter fun x=>pinPos x⊆ X
def colors(X:Support c) (U:Config G c)(x:ciB X):G.Mat:=G.mat (U x)
lemma of_color(X:Support c)(U V:Config G c): Agrees X U V ↔ colors X U=colors X V:=by
 constructor
 · intro h; refine funext fun i=>congrArg G.mat (h _ ((mem_filter.mp i.property).2 (mem_insert_self ..)) ((mem_filter.mp i.property).2 (mem_insert_of_mem (mem_singleton_self _))))
 intro hu i h p; exact G.mat_injective (congrFun hu ⟨i,mem_filter.mpr ⟨mem_univ _,insert_subset h (singleton_subset_iff.mpr p)⟩⟩)
lemma color_c(X:Support c):Continuous (colors (G:=G) X):=by unfold colors; fun_prop
lemma gap_s[FiniteDimensional ℝ E]{U Y:Set E}(hp:IsOpen U)(h:IsCompact Y)(p:Y⊆ U) (n:ℕ):∃ f:E→ℝ, ContDiff ℝ (↑n) f ∧ tsupport f⊆ U ∧ ∀ x∈Y,∀ᶠ v in 𝓝 x,f v=1:=by
 choose F hF uF t H r using fun i:Y=> exists_contDiff_tsupport_subset (n:=(n:ℕ∞)) (hp.mem_nhds (p i.property))
 let V(i:Y):= {z:E|(2:ℝ)⁻¹ < F i z}; have he(i):IsOpen (V i):= isOpen_lt continuous_const (t i).continuous
 obtain ⟨Z,hz⟩:= h.elim_finite_subcover V he (fun x k=> Set.mem_iUnion.mpr ⟨⟨x,k⟩,(show (2:ℝ)⁻¹<F ⟨x,k⟩ x by rw [show F ⟨x,k⟩ x=1 from r ⟨x,k⟩]; norm_num)⟩)
 let A(x:E):= 2*∑ i∈ Z,F i x; refine ⟨Real.smoothTransition ∘ A,(Real.smoothTransition.contDiff (n:=(n:ℕ∞))).comp (by refine contDiff_const.mul (ContDiff.sum ?_); exact fun i _=>t i),?_ ,fun x e=>?_⟩
 · intro x g; by_contra! h; have ht:∀ᶠ i in 𝓝 x,(Real.smoothTransition ∘ A) i=0:=by
      have hp(i:Y):∀ᶠ y in 𝓝 x,F i y=0:= notMem_tsupport_iff_eventuallyEq.mp (fun p=>h (hF i p))
      filter_upwards [(eventually_all_finset Z).mpr (fun i _=>hp i)] with i hl; simp only [Function.comp_apply,A,sum_eq_zero hl,mul_zero,Real.smoothTransition.zero]
   exact (notMem_tsupport_iff_eventuallyEq.mpr ht) g
 obtain ⟨i,y,j⟩:= Set.mem_iUnion₂.mp (hz e); filter_upwards [(he i).mem_nhds j] with z s
 refine Real.smoothTransition.one_of_one_le ((show 1≤2* F i z from ?_).trans (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i=>F i z) (fun i _=> (H i (Set.mem_range_self z)).1) y) zero_le_two))
 change (2:ℝ)⁻¹ < F i z at s; linarith
lemma chrom (G:Gauge)(X:Support c)(I: Finset (Bond c))(n:ℕ):∃ D:ℝ,0≤D∧∀ U:Config G c, Allows n (colors X ∘ gyrate I U) 0 D:=by
 let f(t: Bond c → G.Mat)(u:Directions G c): (x:ciB X)→G.Mat:=fun x=> G.mat (G.lieExp (wakeB I u x.val))* t x.val
 have hf: ContDiff ℝ (↑n) (uncurry f):=by
    refine contDiff_pi.mpr fun i=> ContDiff.mul ?_ ?_
    · exact (G.exp_jet.of_le le_top).comp (f:=fun x: (Bond c→ G.Mat)× Directions G c=>wakeB I x.2 i.val) (by fun_prop)
    exact (contDiff_apply ..).comp contDiff_fst
 let W(U: Config G c)(i:Bond c):=G.mat (U i); have ht:Continuous W:=by unfold W; fun_prop
 -- better via together and per norm.sup over V compact
 have hp(j:Fin (n+1)):Continuous (fun u:Bond c→ G.Mat=>‖iteratedFDeriv ℝ j.val (f u) 0‖):=by
    apply continuous_iff_continuousAt.mpr; intro x; exact ((((Warm.together (hf.contDiffAt (x:=(x,(0:Directions G c))))).light _ (Nat.le_of_lt_succ j.isLt)).comp (f:=fun x=> (x,0)) (by fun_prop)).norm)
 choose C m using fun j=> ((isCompact_univ.image ht).bddAbove_image (hp j).continuousOn)
 let V:=∑ i, |C i|; refine ⟨V,by unfold V; positivity,fun U=>?_⟩
 rw [show colors X ∘ gyrate I U=f (W U) from funext fun i=>funext fun j=> G.mat_mul ..]; refine ⟨(Warm.together (hf.contDiffAt (x:=(W U,(0:Directions G c))))).today,fun i hi=>?_⟩ -- unneeded obtains
 let z:Fin (n+1):=⟨i,Nat.lt_succ_of_le hi⟩; exact (m z (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (Set.mem_univ U)))).trans ((le_abs_self (C z)).trans (single_le_sum (f:=fun i=>|C i|) (fun i _=>abs_nonneg _) (mem_univ z)))
abbrev moist (V:Config G c) (X:Support c):= {W|Agrees X V W}
lemma jaws(X:Support c)(W:Set (Config G c))(y:∃ w:Set (Config G c), IsOpen w ∧ W=w) (P:IsCompact Y) (H:∀ U∈Y, moist U X⊆ W) (I: Finset (Bond c))(n:ℕ):∃ (v:Config G c→ℝ) (C:ℝ), 0 ≤ C ∧ Continuous v ∧ LocalOn X v∧tsupport v⊆ W∧(∀ u∈Y,∀ᶠ i in 𝓝 u,v i=1)∧ Arbor (α:=α) Set.univ (fun _=>v) I n C:=by
 let T:= colors (G:=G) X; have ht:Continuous T:= color_c X; obtain ⟨w,y,e⟩:=y; subst W; let K:=(T '' wᶜ)ᶜ; have hp:IsOpen K:=((IsCompact.image y.isClosed_compl.isCompact ht).isClosed).isOpen_compl; obtain ⟨f,h,hf,h'⟩:=gap_s (U:=K) hp (P.image ht) (fun u v=>by
    obtain ⟨a,p,rfl⟩:=v; intro t; obtain ⟨b,i,v⟩:=t; exact i ((H a p) ((of_color X a b).mpr v.symm))) n
 obtain ⟨C,hC,hU⟩:=payment_for n ((isCompact_univ (X:=Config G c)).image ht) f (fun _ _=> h.contDiffAt); obtain ⟨M,hM,m⟩:=chrom G X I n
 refine ⟨f ∘ T, composeCost n C M,by unfold composeCost; positivity,h.continuous.comp ht,fun i j p=>congrArg f ((of_color X i j).mp p),?_ ,fun u v=> ht.continuousAt.tendsto.eventually (h' _ (Set.mem_image_of_mem T v)),?_⟩
 · intro i v; by_contra! h; have hu:T i ∉ tsupport f:=fun p=> hf p (Set.mem_image_of_mem T h)
   exact (notMem_tsupport_iff_eventuallyEq.mpr (show ∀ᶠ t in 𝓝 i,(f ∘ T) t=0 from ht.continuousAt.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp hu))) v
 intro U p t; have hh:T (gyrate I U 0)∈ T '' Set.univ:=Set.mem_image_of_mem _ (Set.mem_univ _); have hV:= (hU _ hh).comp (f:=T ∘ gyrate I U) (m U); exact ⟨Warm.simple _ hV.smooth,hV⟩
end YM.CF.Forge
