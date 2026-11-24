import YM.CF.Rill.Ala
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
abbrev Foil (n:Side):= ℝ×Directions G n
abbrev HomeL (c f:Side):= Tilt c f (Foil f)
def monkD (K:Monk G S)(u:HomeL c f):Monk G S:={K with V:=u.1,U:=u.2.1,z:=u.2.2.2}
def legL(M:Monk G S)(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(u:HomeL c f): Config G f:= (monkD M u).sent x T q d l u.2.2.1
lemma shoot{L:Teller G}(Y:HomeL c f)(h:Agrees F Y.1 V)(p:F∩ RG.flags (temp x) V ⊆ M.key.flags)(δ:(wires M.key.flags).biUnion pinPos=M.key.flags)(hz:0<temp x)(hv:1000≤radiusB x)(g:L.Funds S T)(j:r≤18)(v:0<d)(k:2*d<firstRadius G)(P:MossX l r x (ray M.key x V) M.park T V M.k K d (fiery G x S.patch.L) q) (u:0< Y.2.2.1)(i:Bond f)(he:Beat.shadows (o:=S.ratio.parent i.1) F ((r+62)*radiusB x)):
 CurlP (l:=l) (fun y=> SU.group.mat (legL M T x q d r y i)) Y:=by
 let W:=raiseW Y; let g₀(v:RingP c f (Foil f)):=(temp x)⁻¹ • v.1
 have hp:∀ v:RingP c f (Foil f),(W v).1= Vmove x Y.1 (g₀ v):=fun v=>by unfold W raiseW Vmove; unfold g₀; simp [hz.ne']
 let f₀(a:RingP c f (Foil f)) :=(raiseW Y a).2.2.1
 let z(a:RingP c f (Foil f)) := (raiseW Y a).2.2.2; let Z(a:RingP c f (Foil f)):=(W a).2.1; have hs(i:Bond f):Scope (l:=l) (fun a=> Z a i) 0:=by
    unfold Z W raiseW increment Scope Function.comp; dsimp only; simp_rw [Gauge.mat_mul]; exact (((SU.group.exp_jet.contDiffAt.of_le (m:=(l:WithTop ℕ∞)) le_top).comp (f:=fun a: RingP c f (Foil f)=>a.2.1 i) 0 (by fun_prop)).mul contDiffAt_const)
 have hz':= glow (monkD M Y) x F Z z g₀ V h p δ ‹L.Funds S T› hv j v k f₀ P (U:=0) (by simp [g₀]) (by unfold g₀; fun_prop) (by unfold f₀ raiseW; fun_prop) (by unfold f₀; rw [scrub]; exact u) (by unfold z raiseW; fun_prop) hs i he
 unfold CurlP; refine hz'.congr_of_eventuallyEq (Eventually.of_forall fun y=> ?_)
 refine congrArg (fun (A:Monk _ _)=> SU.group.mat (A.sent x T q d r (f₀ y) i)) (show monkD M (W y)= _ from ?_); unfold monkD mural; dsimp only; rw [hp]
lemma strut (p:v≤r) (hs:halo r E⊆F){i}(h:i∈E): Beat.shadows (o:=i) F v:= by -- tune typed syntax
 exact (Corona.halo_mono p (singleton_subset_iff.mpr ‹_›)).trans hs
open Atala
-- owner boundary visitor.D region F contains X halo
def Passage (S:StepData c f)(X:Support c): Support f:= univ.filter fun i=> S.ratio.parent i∈X
def SeeW (V: Config G c)(a:ℝ) (Y D: Support c): Prop:= ∀ i∈Y,∀ k:Cell c,i∈ touched k → SU.group.chord (faceValue V k) < a ∨ i∈ D
lemma sav (F:Config G c)(a:ℝ)(Y D:Support c): SeeW F a Y D → Y∩ RG.flags a F ⊆ D:=by
 intro p i v; obtain ⟨t,l⟩:=mem_inter.mp v; obtain ⟨k,h,u⟩:=(flags_spec ..).mp l; exact (p _ t _ h).resolve_left u.not_gt
lemma terrain {i:Cell c}{p y: Site c}(h:p∈touched i)(g:y∈ touched i):separation p y ≤ 12:=by
 have hx:= Work.E01.sep_touched i p h; have hk:= Work.E01.sep_touched i y g; apply (separation_triangle p i.1 y).trans; rw [separation_comm p]; omega
lemma parent_hK(X:Support c) : halo r (Passage S X) ⊆ Passage S (halo (r+1) X):=by
 intro i p; obtain ⟨a,h,v⟩:=halo_spec.mp p; exact mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨S.ratio.parent a,(mem_filter.mp h).2,(Work.E04.parent_separation S.ratio ..).trans (Nat.add_le_add_right v 1)⟩⟩
lemma cotton {D:Type}[TopologicalSpace D]{t':D}(V: D→ Config G c)(g:∀ i:Bond c,i.1∈ halo 12 E→ ContinuousAt (fun x=>V x i) t')(p:SeeW (V t') e E F):∀ᶠ v in 𝓝 t',SeeW (V v) e E F:=by
 -- use constant Burg
 let W(v:D): Config G c:=fun i=> if i.1∈ halo 12 E then V v i else V t' i
 have hp:W t'=V t':=funext fun i=> by simp [W]
 have hz:ContinuousAt W t':=by refine continuousAt_pi.mpr fun i=>?_ ; unfold W; split; exact g i ‹_›; exact continuousAt_const
 have ht(j:Site c):∀ᶠ v in 𝓝 t',j∈ E → ∀ k:Cell c,j∈ touched k→ SU.group.chord (faceValue (V v) k)< e∨j∈F:=by
    by_cases v:j∈E; swap; · exact Eventually.of_forall fun i p=> (v p).elim
    have hh(k:Cell c):∀ᶠ x in 𝓝 t',j∈ touched k→ SU.group.chord (faceValue (V x) k)< e ∨ j∈F:=by
       by_cases h:j∈ touched k; swap; · exact Eventually.of_forall fun i p=>(h p).elim
       rcases p _ v k h with w|w; swap; · exact Eventually.of_forall fun _ _=> Or.inr w
       let f(x:D):= SU.group.chord (faceValue (W x) k); have he: ContinuousAt f t':= SU.group.continuous_chord.continuousAt.comp ((Continuous.continuousAt (show Continuous (fun U: Config G c=>faceValue U k) from ?_)).comp hz); swap; · unfold faceValue; fun_prop
       filter_upwards [he.eventually (gt_mem_nhds (show f t'<e from by unfold f; rw [hp]; exact w))] with i w p; apply Or.inl; rw [show faceValue (V i) k=faceValue (W i) k from ?_]; exact w; apply travel_local; intro a u l; exact (show W i a=V i a from if_pos (halo_spec.mpr ⟨j,v,terrain h (List.mem_toFinset.mpr u)⟩)).symm
    exact (eventually_all.mpr hh).mono fun i v _=> v
 exact eventually_all.mpr ht
end YM.CF.Rill
