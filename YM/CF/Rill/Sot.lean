import YM.CF.Rill.Pools
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes Tenant
attribute [local instance] opCStarAlgebra
variable {N:Side}
set_option synthInstance.maxSize 20000
-- Lens output meas theorem.G.For kernels.Finite CUT. input Leg probe local.F.B.Health. $U.P Bound project from compact Triple_REAL`.
variable {A:Type}[MeasurableSpace A]
lemma fare_r (U V:Pane N)(S:Support (More N))(p:Agrees S U V):fare S (Tulip.profile U) (Tulip.profile V)=0:=by
 unfold fare; apply sum_eq_zero; intro i v; rw [show Tulip.profile U i=Tulip.profile V i from funext fun j=>by unfold Tulip.profile; rw [p _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2],sub_self,norm_zero] -- tune
variable {G':Ratio c f}
abbrev Arch(G':Ratio c f)(e:ℝ):= {u:Nom c f × Pane f//JointB G' u.1 e∧Guard u.2 e}
open Rush Dial Phase Phase.Sample
instance :CompactSpace (Arch G' e):=by
 let X:Set (Nom c f):={x|JointB G' x e}; let P(i:Guy (N:=c))(x:Nom c f):=‖brand (x.2 i) - brand (travel x.1 ((ratio G').embed i.1) (pathL G' i.2))‖; have he(i):Continuous (P i):=by unfold P; apply Continuous.norm; apply (spinD.comp _).sub (spinD.comp _) <;> fun_prop -- tune
 have hp : IsClosed X:=by
    let T:Set (Nom c f):= Prod.fst ⁻¹' {u:Bkg (More f)|Guard u e}; let U:Set (Nom c f):= Prod.snd ⁻¹' {u:Bkg (More c)|Guard u e}; rw [show X=(T∩ U)∩ ⋂ i,{x|P i x≤e} from ?_]; swap; · ext; simp only [X,T,U,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_iInter]; exact ⟨fun ⟨g,s,p⟩=>⟨⟨g,s⟩,p⟩,fun ⟨⟨p,h⟩,z⟩=>⟨p,h,z⟩⟩
    exact ((((cover_closed (More f) e).preimage continuous_fst).inter ((cover_closed _ e).preimage continuous_snd)).inter (isClosed_iInter fun i=>isClosed_le (he i) continuous_const))
 exact isCompact_iff_compactSpace.mp ((hp.prod (cover_closed (More f) e)).isCompact)
lemma arch_k(p:0<e)(x:Arch G' e): (unionP x.val.1,Tulip.profile x.val.2)∈ cro G' e:=⟨⟨x.val.1,x.property.1,by simp [p]⟩,⟨x.val.2,x.property.2,by simp [p]⟩⟩
abbrev bring(p:0<e)(x:Arch G' e):↥(cro G' e):=⟨_,arch_k p x⟩
lemma brick(p:0<e)(S:Support (More f))(F:cro G' e→ Op (Iota G'))(t k:Bool)(W:Toll (Iota G'))(q:Suite (badge _) (pinH G' e t) (pinH G' e k) S W F)(U V:Arch G' e)(u:Agrees S U.val.1.1 V.val.1.1)(v:Agrees (cloudG G' S) U.val.1.2 V.val.1.2)(g:Agrees S U.val.2 V.val.2): F (bring p U)= F (bring p V):=by
 ext i j; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; have ht:= (q.expo i j).variation (bring p U) (bring p V); rw [show (hall G' e).eval S (bring p U) (bring p V)=0 from ?_,mul_zero] at ht; exact ht
 change (deal G' S (unionP _) (unionP _))/ _ +_/_=0; dsimp only [deal,unionP, bring]; simp only [fare_r _ _ S u, fare_r _ _ _ v, fare_r _ _ _ g,zero_div,add_zero] -- tune
private abbrev Stax(n:Side)(S:Finset (Site (More n))):= {i:Bond (More n)//Skye.ends i⊆S}
-- meas via compact real profile argument
lemma bill_k (p:0<e)(S:Support (More f))(F:cro G' e→ Op (Iota G'))(t k:Bool)(W:Toll (Iota G'))(q:Suite (badge _) (pinH G' e t) (pinH G' e k) S W F)(U:A→ Arch G' e)(h:∀ i:Bond (More f),Skye.ends i⊆ S→ Measurable (fun y:A=> (U y).val.1.1 i) ∧ Measurable (fun y:A=> (U y).val.2 i))(hp:∀ i:Bond (More c),Skye.ends i⊆cloudG G' S→ Measurable (fun y:A=>(U y).val.1.2 i))(i j:Iota G'):Measurable fun y=> F (bring p (U y)) i j:=by
 let g(x:Arch G' e): ((Stax f S→ SU.E) × (Stax c (cloudG G' S)→ SU.E))× (Stax f S→ SU.E):= ((fun a=> x.val.1.1 a.val, fun a=> x.val.1.2 a.val),fun a=> x.val.2 a.val)
 let f(x):= F (bring p x) i j; refine project_meas g f U ?_ ((q.expo i j).connected.comp ?_) (fun i' j' p' =>congrArg (fun A:Op _=> A i j) (brick p S F t k W q _ _ (fun a g u=>congrFun (congrArg (fun x=>x.1.1) p') ⟨a,insert_subset g (singleton_subset_iff.mpr u)⟩) (fun a g u=>congrFun (congrArg (fun x=>x.1.2) p') ⟨a,insert_subset g (singleton_subset_iff.mpr u)⟩) (fun a g u=> congrFun (congrArg Prod.snd p') ⟨a,insert_subset g (singleton_subset_iff.mpr u)⟩))) ?_
 · refine Continuous.prodMk (Continuous.prodMk (continuous_pi fun _=>?_) (continuous_pi fun _=>?_)) (continuous_pi fun _=>?_) <;> fun_prop
 · exact (((profile_c.comp (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))).prodMk (profile_c.comp (continuous_snd.comp (continuous_fst.comp continuous_subtype_val)))).prodMk (profile_c.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
 exact Measurable.prodMk (Measurable.prodMk (measurable_pi_lambda _ fun a=>(h a.val a.property).1) (measurable_pi_lambda _ fun a=>hp a.val a.property)) (measurable_pi_lambda _ fun a=>(h a.val a.property).2)
end YM.CF.Rill
