import YM.CF.Esti.Arise
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
open Offset Rows Matrix
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{H V:Config G c}
section column
variable (A:Stores S) (F:Forest S.ratio)(T:Tube G S)(x:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(Y: LinkArray G (Frozen A x F))(z:Prices G (Active A x F))(V:Config G c)
local notation "g"=> Rows.move T x V k (shots S x) A F
def axle := g *ᵥ z + Offset.f0 T x A F k V q d Y
def wheel := tape (axle A F T x k q d Y z V)
variable (h:Offset.f0 T x A F k V q d Y=Rows.source T x V k (shots S x) A F q d Y){σ Λ hC:ℝ} (p: T.up.Bounds T.high σ hC Λ)
include h p
lemma along : wheel A F T x k q d Y z V= Rows.restrict x (shots S x) A F (Rows.lands T x V k (shots S x) A F q d Y z) :=by unfold wheel axle; rw [h]; exact Rows.arrived _ _ _ _ _ _ _ _ _ _ p z -- tune
end column
lemma airK{u:E}{τ κ:Type}[Fintype τ][Fintype κ]{D L:ℝ}{A:E→Matrix τ κ ℝ}{f:E→ Fish κ}(h:Allows n (fun i=>ranQ (A i)) u D)(p:Allows n f u L):Allows n (fun k=>A k *ᵥ f k) u (2^n *D*L):=by
 let W: (Fish κ →L[ℝ] Fish τ)→L[ℝ] Fish κ →L[ℝ] Fish τ:=(ContinuousLinearMap.apply ℝ _).flip
 exact (h.bilinear W p (ContinuousLinearMap.opNorm_le_bound₂ W zero_le_one fun i j=> by rw [one_mul]; exact i.le_opNorm _)).mono (show _ ≤2^n*D*L by ring_nf; rfl)
variable {P:Patch}{K': Teller G}{F:Forest S.ratio}{A:Stores S} {T:Tube G S}{k:S.Choices}{q:Chi} {Y:LinkArray G (Frozen A x F)}{N M v' e L D:ℝ}
lemma gifts (V:Config G c)(a θ r l b:ℝ)(h: Offset.Shift n x a θ d M T F A V k q)(p: Estimate n b θ r l N A F T x V k 0) (ht:0 < temp x)(ht':temp x ≤ 1)(ha:0 < a)(hb:0 < b)(hk:0 < N)(hm:0 < M)(f:Directions G c→Prices G (Active A x F))(v:Allows n f 0 D):
 Allows n (fun i=> wheel A F T x k q d Y (f i) (Vmove x V i)) 0 (Push.Uniform.shade G*((2:ℝ)^n * (activation G n 0 b*N)*D + activation G n 0 a*(M*fiery G x S.patch.L))):=by
 let P(y:Config G c):=Rows.move T x y k (shots S x) A F
 let Q(R:PriceCoords G c) := P (pulse x V R)
 have hi:= polar_compress (t:=temp x) p.toKernelJets.moves ht.le ht'
 have hx': Polar 0 (Wisps.down S) (Wisps.front A F) Q n b N:=hi
 let g(y:Directions G c):= P (Vmove x V y); have he: Allows n (fun y=> ranQ (g y)) 0 (activation G n 0 b*N):=by
    apply (radon 0 Q ((map_zero (reader G c)).symm ▸ hx') hk.le hb).germ; apply Eventually.of_forall; intro y; unfold g Q Vmove pulse; simp_rw [Function.comp_apply,←map_smul, reader_field] -- tune
 let H(y:Config G c):= Offset.f0 T x A F k y q d Y; have hp:=parcels H (h.corners Y) (mul_nonneg hm.le (temp_nonneg _)) ha ht -- tune hp Y
 let G': Prices SU.group (Slots S) →L[ℝ] LogArray SU.group (Slots S):= (Push.Uniform.tint G (Slots S)).toContinuousLinearMap; refine ((airK he v).add hp).linear G' ?_; apply ContinuousLinearMap.opNorm_le_bound _ (Push.Uniform.shade_pos _).le; exact fun p=>Push.Uniform.tint_le p
lemma owns (K':Teller G)(P:Patch)(q:Chi)(n:ℕ)(D:ℝ)(hd:0<D) (h: P.Branches K'.bind G): ∃ M:ℝ,1 ≤ M ∧ ∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S), Cert P K' S T x→∀ (A:Stores S)(F: Forest S.ratio)(V:Config G c), A.flags=RG.flags (temp x) V→ ∀ k:S.Choices,
 let t:=fiery G x S.patch.L; let d:= D*t
 Offset.f0 T x A F k V q d=Rows.source T x V k (shots S x) A F q d ∧∀ Y:LinkArray G (Frozen A x F),∀ (r:Directions G c→Prices G (Active A x F))(a:ℝ), Allows n r 0 a → Allows n (fun i=> wheel A F T x k q d Y (r i) (Vmove x V i)) 0 (M*(a+t)):=by
 obtain ⟨r,d,d',v,M,N,η,l,hr,hd',he,hv,hM,hN,hη,hl,H⟩:=Offset.prices G P K' D hd q n h
 let m:= Push.Uniform.shade G*(2^n*(activation G n 0 d'*N)+ activation G n 0 d*M); have ha:0 ≤ activation G n 0 d:=zero_le_one.trans (activation_one _ n 0 hd'); have hp:0 ≤ activation G n 0 d':=zero_le_one.trans (activation_one _ n 0 he)
 refine ⟨max 1 m,le_max_left ..,?_⟩
 filter_upwards [H,monitors G P.L] with x hY hx c f S T p A F V y k t d0; obtain ⟨hs,hm⟩:=hY.2 S T p.got p.size p.funds.1 A F V y k
 refine ⟨hm.okay,fun Y S u T'=>?_⟩; have hu:= Push.Uniform.shade_pos G; have he':= T'.nonneg; have hU:0≤ t:=temp_nonneg _
 refine (gifts (Y:=Y) _ d v η l d' hm (hs 0 (by simpa using hr.le)) hx.1 hx.2.1 hd' he hN hM S T').mono ((le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right 1 m) (add_nonneg he' hU))))
 unfold m; change _ ≤ Push.Uniform.shade G*(_+_)*(u+t); rw [mul_assoc (Push.Uniform.shade G)]; apply mul_le_mul_of_nonneg_left _ hu.le; change _+ (_*(M*t)) ≤_; nlinarith only [mul_nonneg (mul_nonneg ha hM.le) he',mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2^n) (mul_nonneg hp hN.le)) hU] -- shade shown u+t
end YM.CF.Esti
