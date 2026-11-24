import YM.CF.Err.Pale
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Err
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
variable{T:Tube SU.group S} {A:Stores S}{F:Forest S.ratio}{V:Config SU.group c}{k:S.Choices}{L:Teller SU.group} {α:Type*}[NormedAddCommGroup α][NormedSpace ℝ α]{R:α→ Directions SU.group c}{Y:α→LinkArray SU.group (Frozen A x F)}{N m l:ℕ}{C u:ℝ}
variable {p:ℝ}{K:Monk G S}{U:α}{Y:LinkArray G (Frozen A x F)}
lemma lure {ψ:α→ Prices G (Active A x F)}{S':α→ Config G c}{P:α→ LinkArray G (Frozen A x F)} (p:ContDiffAt ℝ (↑l) ψ U) (h:∀ i, Scope (l:=l) (fun x=> S' x i) U)(t:∀ i,Scope (l:=l) (fun x=> P x i) U): ∀ i, Scope (l:=l) (fun v=> landed x A F (S' v) (P v) (ψ v) i) U:=by
 intro i
 by_cases k:i∈ F.trunks; · apply (show Scope (l:=l) (fun _:α=> (1:SU.E)) U from contDiffAt_const).congr_of_eventuallyEq; exact Eventually.of_forall fun _=> congrArg SU.group.mat (F.on_tree _ ⟨i,k⟩)
 let a:F.Free:=⟨i,k⟩; by_cases g:chill A x F a
 · let t':Frozen A x F:=⟨a,g⟩; apply (t t').congr_of_eventuallyEq; exact Eventually.of_forall fun v=>congrArg SU.group.mat (held_physical x A F _ _ (ψ v) t')
 let b:Active A x F:=⟨a,g⟩; have ht :Scope (l:=l) (fun v=> replica S.ratio (S' v) i) U:=by unfold replica; split; exact contDiffAt_const; exact h _
 have hh: ContDiffAt ℝ (↑l) (fun v=> tape (ψ v)) U:= (gaugeCount (ι:=Active A x F) («G»:=SU.group)).contDiff.contDiffAt.comp _ p
 apply (((SU.group.exp_jet.contDiffAt.of_le (m:=(l:WithTop ℕ∞)) le_top).comp U (contDiffAt_pi.mp hh b)).mul ht).congr_of_eventuallyEq; refine Eventually.of_forall fun v=>?_ ; exact (congrArg SU.group.mat (clear_physical x A F _ _ (ψ v) b)).trans (Gauge.mat_mul ..)
lemma Vlu (p:ContDiffAt ℝ (↑N) R U)(i:Bond c): Scope (l:=N) (fun y=>Vmove x V (R y) i) U:=by
 unfold Scope; change ContDiffAt ℝ (↑N) (fun y=>SU.group.mat (SU.group.lieExp (temp x • R y i)* V i)) U; simp_rw [Gauge.mat_mul]; exact (((SU.group.exp_jet.of_le le_top).contDiffAt).comp _ ((contDiffAt_pi.mp p _).const_smul _)).mul contDiffAt_const
lemma sentE {Z:α→ LinkArray G (Frozen A x F)}{z:α→LogArray G (Active A x F)}(g:MossX N l x A F T V k C d p q)(h:L.Funds S T) (hk:l≤18)(hv:0<d)(hP:2*d<firstRadius G){β:α→ℝ}(t:ContDiffAt ℝ (↑N) R U)(hp:R U=0)(θ:ContDiffAt ℝ (↑N) β U)(q':0 < β U)(w:∀ i,Scope (l:=N) (fun v=>Z v i) U)(u:ContDiffAt ℝ (↑N) z U):∀ i, Scope (l:=N) (fun v=>fieldU (β v) T F A ((Vmove x V ∘ R) v) k x l q d (Z v) (z v) i) U:= lure (ψ:=fun i=>realP (β i) T F A ((Vmove x V∘R) i) k x l q d (Z i) (z i)) (coinL g h hk hv hP hp t w θ q' u) (Vlu t) w -- tune
-- local synthetic readiness, Flags may be missing some region.B.Paint.
variable (M:Monk G S)(x:ℝ)(F:Support c)(Z:α→ Config G f)(p:α→Directions G f)(y:α→Directions G c){C':Config G c}
def mural(C:Stores S)(V: Config G c)(v:α):Monk G S:={M with key:=C, V:= Vmove x V (y v), U:=Z v,z:=p v}
lemma glow (W:Config G c)(g:Agrees F M.V W) (v: F∩ RG.flags (temp x) W⊆ M.key.flags) (δ:(wires M.key.flags).biUnion pinPos=M.key.flags) (h:L.Funds S T) (ht:1000≤radiusB x)(hk:l ≤18)(hp:0<d)(hb:2*d<firstRadius G)(b:α→ℝ) (p':MossX N l x (ray M.key x W) M.park T W M.k C d (fiery G x S.patch.L) q) (hx:y U=0) (t:ContDiffAt ℝ (↑N) y U)(θ:ContDiffAt ℝ (↑N) b U)(u:0<b U)(c:ContDiffAt ℝ (↑N) p U) (w:∀ i,Scope (l:=N) (fun v=>Z v i) U) (i:Bond f)(e:Beat.shadows (o:=S.ratio.parent i.1) F ((l+62)* radiusB x)):
 Scope (l:=N) (fun a=>(mural M x Z p y M.key M.V a).sent x T q d l (b a) i) U:=by
 let Bee:=fun a=> mural M x Z p y M.key M.V a; let Q:=ray M.key x W; let J:=mural M x Z p y Q W; have he(a):Beat (Bee a) (J a) F:=by
    refine ⟨last_v M.key δ v, fun _ _=>rfl,fun _ _=> rfl,fun _ _=>Iff.rfl, ?_,fun _ _=>rfl,fun _ _=> rfl⟩; intro i p l; change Vmove x _ _ _= Vmove x W _ _; unfold Vmove increment; rw [g i p l]
 rw [show (fun a=>(mural M x Z p y M.key M.V a).sent x T q d l (b a) i)=(fun a=> (J a).sent x T q d l (b a) i) from funext fun a=>(he a).backF p'.ready ht i e]
 let Y(v)(i: Frozen Q x M.park):= Z v i.val.val; let H(v)(i:Active Q x M.park):= p v i.val.val; have hv:∀ i, Scope (l:=N) (fun v=>Y v i) U:=fun i=>w _; have hg:ContDiffAt ℝ (↑N) H U:=contDiffAt_pi.mpr fun j=> contDiffAt_pi.mp c j.val.val; exact sentE p' h hk hp hb t hx θ u hv hg i
end YM.CF.Err
