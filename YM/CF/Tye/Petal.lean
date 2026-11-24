import YM.CF.Tye.Peak
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tye
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
open Affine Reine
open Corne Rink Primitives.HaarLogJets.Guard
open Gauges Cloak
section
variable (U V:Config G c)(i:Site c)(g:Site c→ SU.group.El)(P:PathData G)(t:ℝ)(A:Finset (Cell c))(Q:Clip)(j r u:ℕ)
abbrev Visit (U V:Config G c) (i:Site c)(Z: RG.Atom G n):Prop:= Z.unmasked U i=Z.unmasked V i
lemma brace_v(p:∀ i:Cell c,Pressure.toll U i=Pressure.toll V i)(O:Support c): east q O A t U=east q O A t V:=by
 unfold east nose wrapM shutters; simp_rw [p,polP,p]; split_ifs <;> rfl
lemma pollP (p:∀ i:Cell c,Pressure.toll U i=Pressure.toll V i)(O:Support c): polP t U O A↔polP t V O A:=by unfold polP; simp_rw [p]
lemma preserve(p:∀ i:Cell c,Pressure.toll U i=Pressure.toll V i): pers A Q t U i↔ pers A Q t V i:=by unfold pers; refine forall_congr' fun v=> imp_congr_right fun _=>?_ ; have h:=p v; unfold Pressure.toll at h; rw [h] -- rw Pressure toll
local notation "W₀"=> Lattice.gauge g U
local notation "F"=> Reef.echo U
lemma gauge_l(o:Cell c): Pressure.toll W₀ o=Pressure.toll U o:=by simp [Pressure.toll,face_gauge,SU.group.chord_conj]
lemma batch_g(K:ℕ→ RG.Atom SU.group n)(p:∀ i,(K i).Invariant) : Visit W₀ U i (batch K r j):=by
 unfold Visit batch; split
 · unfold RG.Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact p j ..
 simp only [dimU]
lemma batch_f(K:ℕ→ RG.Atom SU.group n)(p:∀ i,Prist (K i)): Visit F U i (batch K r j):=by
 unfold Visit batch; split
 · unfold RG.Atom.unmasked; simp_rw [Reef.tollSlot]; exact p j _
 simp only [dimU]
lemma haste_g(K:ℕ→ RG.Atom SU.group n)(p:∀ i,(K i).Invariant): Visit W₀ U i (haste r K j):=by
 unfold Visit haste Newt.farther; split; simp only [dimU]; unfold RG.Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact p j ..
lemma haste_f(K:ℕ→ RG.Atom SU.group n)(p:∀ i,Prist (K i)): Visit F U i (haste r K j):=by
 unfold Visit haste Newt.farther; split; simp only [dimU]; unfold RG.Atom.unmasked; simp_rw [Reef.tollSlot]; exact p j _
lemma rod_g: Visit W₀ U i (rod P r j):=by
 have he(z): Visit W₀ U i (Stationary.gramPath P z):=by
    let f(Z:Config G c)(k:ℕ):= P.ellTerms (i,z.1) k Z; have hp(s:ℕ): f W₀ s= SU.group.adjoint (g i) (f U s):=by unfold f PathData.ellTerms; rw [Work.F05.slot_gauge,map_smul]
    unfold Visit; refine (Stationary.gram_eval P z i W₀).trans (Eq.trans ?_ (Stationary.gram_eval P z i U).symm); change inner ℝ (f W₀ _) (f W₀ _) /2=_; simp_rw [hp]; rw [show ∀ x y,inner ℝ (SU.group.adjoint (g i) x) (SU.group.adjoint (g i) y)=inner ℝ x y from fun x y=> (Gauges.turn (g i)).inner_map_map x y] -- tune
 unfold Visit rod Function.comp; unfold Newt.farther; split; simp only [dimU]; exact he _
lemma rod_f: Visit F U i (rod P r j):=by
 have he(z): Visit F U i (Stationary.gramPath P z):=by
    let f(Z:Config G c)(k:ℕ):=P.ellTerms (i,z.1) k Z; have hp(s:ℕ):f F s=frolic (f U s):=by unfold f PathData.ellTerms; rw [Reef.tollSlot,map_smul]
    unfold Visit; refine (Stationary.gram_eval P z i F).trans (Eq.trans ?_ (Stationary.gram_eval P z i U).symm); change inner ℝ (f F _) (f F _) /2=_; simp_rw [hp]; rw [frolic.inner_map_map]
 unfold Visit rod Function.comp; unfold Newt.farther; split; simp only [dimU]; exact he _
lemma frame_g(o:Cell c): Esti.king A P Q r u t W₀ o=Esti.king A P Q r u t U o:=by
 unfold Esti.king hallP taken; rw [gauge_l,face_gauge,SU.group.price_conj]; simp only [ite_true]; rw [preserve W₀ U _ t A Q (gauge_l U g),plotted_turn]; split_ifs <;> first | rfl | rw [SU.group.norm_adjoint]
lemma frame_f(o:Cell c): Esti.king A P Q r u t F o= Esti.king A P Q r u t U o:=by
 unfold Esti.king hallP taken; rw [mint_b]; simp only [ite_true]; rw [faceValue,Reef.echo_t,cold, preserve F U _ t A Q (mint_b _),Char.plotE]; split_ifs <;> first|rfl|rw [frolic.norm_map]; try rfl
variable {U V}(p:∀ i:Cell c,Pressure.toll U i=Pressure.toll V i)(S':RG.Atom SU.group n)(h: Visit U V i S')
include p h
lemma lushP : lush_k q S' A t i U=lush_k q S' A t i V:=by unfold lush_k; rw [brace_v U V _ _ p,h] -- Visit rw defeq
lemma peerP : peer_k S' A t i U=peer_k S' A t i V:=by unfold peer_k; rw [pollP U V _ _ p]; split; exact h; rfl
lemma path_p :sleeve S' A Q i t U= sleeve S' A Q i t V:=by unfold sleeve; rw [preserve U V i t A Q p]; split; exact h; rfl
end
end YM.CF.Tye
