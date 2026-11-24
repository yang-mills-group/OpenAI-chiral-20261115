import YM.CF.Tye.Spin
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
variable (f k:Sweep (mid N B))
open PhysicalNext.InteractingRank
abbrev dice(t:Bool)(M:Monk SU.group S):Monk SU.group S:= if t then cedar M else M
abbrev airport(f:Sweep (mid N B))(W:Stores S):= Locations.book f.s (Facet.pasta f) W
abbrev rot(f:Sweep (mid N B))(M: Monk SU.group S): Monk SU.group S:= dice f.charge (clue S f.s (Facet.pasta f) M)
abbrev chart(f:Sweep (mid N B)): Equiv.Perm (Site (Domain N B)):= StepData.sendSites f.s (Facet.pasta f)
lemma hype {Q:Type}[Fintype Q][DecidableEq Q](O:ColorOrtho SU.group Q)(e:Equiv.Perm Q)(p:LogArray SU.group Q): ‖Tensor.lifting O e p‖=‖p‖:= le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr (fun i=> ((O i).norm_map _).trans_le (norm_le_pi_norm p (e i)))) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=>by obtain ⟨i,rfl⟩:=(e.surjective i); exact ((O i).norm_map _).symm.trans_le (norm_le_pi_norm (Tensor.lifting O e p) i)))
lemma here_k : ‖(rot f M).z‖=‖M.z‖:=by
 unfold rot dice; split
 next t=> change ‖Tensor.lifting (Char.shiftF _) _ (Tensor.lifting _ _ M.z)‖=_; rw [hype,hype]
 change ‖Tensor.lifting _ _ M.z‖=_; rw [hype]
lemma thereZ : (rot f M).key=airport f M.key:=by unfold rot dice; split<;>rfl
lemma past_s{m:Side}{A:Sweep m}(i:Site (More m)) : Shape.anon (castX A) m i= affine A.s (wrap (More m) (2 • (castX A).t)) i:=rfl
lemma pose_t : (rot f M).V= flashA f M.V:=by unfold rot dice; unfold flashA; cases H:f.charge; rfl; rw [Cour.spin_c,Nacre.mores]; rfl
lemma aura_b(C:StepData d d'): Pump.meet (f.s,Facet.pasta f) (k.s, Facet.pasta k)=((f*k).s,Facet.pasta (f*k)):=by
 let o:Site d:=0; have he:= Spire.stirP f k o; simp_rw [past_s] at he; unfold affine o at he; simp only [Signed.act_zero,zero_add] at he; exact Prod.ext rfl he
lemma cloak_t : rough (rot f M) 0=rot f (rough M 0):=by unfold rot dice; split; rw [rough_f,rough_s]; exact rough_s ..
lemma flank {μ τ:Side}{S:StepData μ τ}(M N:Monk SU.group S)(p:M.key=N.key)(h:M.park=N.park)(x:M.k=N.k)(v:M.V=N.V)(hv:M.U=N.U): rough M 0=rough N 0:=by unfold Cay.rough; congr 1
lemma person : (rot f M).park=Locations.forest f.s (Facet.pasta f) M.park ∧ (rot f M).k=Channels.ticket f.s (Facet.pasta f) M.k:=by unfold rot dice; split <;> exact ⟨rfl,rfl⟩
abbrev focus {D:Side}(t:Bool)(M:Config SU.group D):= if t then Reef.echo M else M
lemma toss_a : (rot f M).U=focus f.charge (Lattice.pull f.s (S.ratio.embed (Facet.pasta f)) M.U):=by unfold rot dice focus; split <;> rfl
lemma oxa {D:Side}(v w:Bool)(W0:Site D)(s:Signed)(U':Config SU.group D):focus w (Lattice.pull s W0 (focus v U'))= focus (v.xor w) (Lattice.pull s W0 U'):=by cases v<;>cases w <;> simp [focus,Reef.echo_p,Reef.echo2]
lemma crewX : rough (rot k (rot f M)) 0=rough (rot (f*k) M) 0:=by
 let i:Pump.Wheel d:=(f.s,Facet.pasta f); let t:Pump.Wheel d:=(k.s,Facet.pasta k); have he:Pump.meet i t=((f*k).s, Facet.pasta (f*k)):= aura_b f k S -- S argument first?
 refine flank _ _ ?_ ?_ ?_ ?_ ?_
 · simp_rw [thereZ]; have hp:= Pump.marks i t M.key; rw [he] at hp; exact hp.symm
 · rw [(person ..).1,(person ..).1,(person ..).1]; have hp:= Pump.merged (S:=S) i t M.park; rw [he] at hp; exact hp.symm
 · rw [(person ..).2,(person ..).2,(person ..).2]; have hp:= Pump.paying M.k i t; rw [he] at hp; exact hp.symm
 · simp_rw [pose_t, lights]
 rw [toss_a,toss_a,toss_a,oxa, Lattice.pull_pull]; have hp:= Pump.grow S i t; rw [he] at hp; refine congrArg (focus _) (congrArg (fun b=> Lattice.pull _ b M.U) (congrArg Prod.snd hp.symm)) -- tune
abbrev Chir (M:Monk SU.group S)(x:ℝ):Prop:= M.key.flags=flags (temp x) M.V
lemma sing_b(p: Chir M x):Chir Y x:= (PhysicalNext.OrderedAffine2B.SymStencil.flagged M.key s b M.V (temp x)).2 p -- tune
lemma flagE : flags (temp x) (Reef.echo M.V)= flags (temp x) M.V:= by ext i; rw [flags_spec,flags_spec]; simp_rw [faceValue,Reef.echo_t,Reef.cool]
lemma rotT(p: Chir M x):Chir (rot f M) x:=by
 unfold rot dice; have hp:= sing_b M f.s (Facet.pasta f) p; split; change _=flags (temp x) (Reef.echo _); rw [flagE]; exact hp; exact hp -- tune order
lemma typT : airport k (airport f M.key)=airport (f*k) M.key:=by rw [←thereZ,←thereZ,←thereZ]; have hp:=congrArg Monk.key (crewX M f k); exact hp
end YM.CF.Tye
