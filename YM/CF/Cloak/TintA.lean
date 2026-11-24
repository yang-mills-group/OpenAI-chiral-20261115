import YM.CF.Cloak.Coil
import YM.CF.Cloak.Wear
import YM.CF.Cloak.Mint
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Vol Pressure.Tube
open Vol Cay Slate
variable {l:ℕ}{M:Monk G S}{s':ℝ}
-- μ independent aperture near ordinary stencils; Caps Witness no flags.U required.
local notation "V₀"=>M.V
local notation "b₀"=>M.bush x
lemma red_d (T:Tube G S)(x b d:ℝ)(k:S.Choices)(Y:LinkArray G (Frozen (bareStores S) x F))(q:Chi)(Z: Config G c)(l:ℕ): liftN T x Z k (bareStores S) F q d Y l= liftN T x Z k (bareStores S) F q b Y l:=by
 let Q(e):= Offset.mean T x k (bareStores S) F q e Y Z
 have hs:Q d=Q b:=by
    unfold Q Offset.mean Offset.b f0; rw [show autoShell (F:=F) (x:=x) q d Z Y= autoShell q b Z Y from funext (fun i=> False.elim ((notChilled S F x i.val) i.property))]
 have ht(l):orbitP T x Z k (bareStores S) F q d Y l=orbitP T x Z k (bareStores S) F q b Y l:=by induction l with| zero=> exact hs| succ i h=> exact congrArg _ h -- tune function swing
 unfold liftN; simp only [show Offset.mean T x k _ F q d Y Z= Offset.mean T x k _ F q b Y Z from hs,ht]
lemma film_d(i:Active M.key x M.park)(b:ℝ)(h:Ready T x)(hx:1000 ≤ radiusB x)(hp:S.ratio.parent i.val.val.1∉ M.key.dome ((l+62)*radiusB x)): tape (liftN T x V₀ M.k M.key M.park q d b₀ l) i=tape (liftN T x V₀ M.k M.key M.park q b b₀ l) i:=by
 let H:Monk G S:={M with key:=bareStores S}; let j:Active (bareStores S) x M.park:= ⟨i.val,notChilled S M.park x _⟩; let X:= halo ((l+62)*radiusB x) {S.ratio.parent i.val.val.1}; have he:Beat M H X:=by
    refine ⟨fun k t=> iff_of_false (fun l=> hp (halo_spec.mpr ⟨k,l,(separation_comm ..).trans_le (by obtain ⟨z,u,v⟩:=halo_spec.mp t; exact Finset.mem_singleton.mp u ▸ v)⟩)) ?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩; simp [H,Stores.place,bareStores] -- motive tune ν
 ext p; let E:=M.key; let P(e:ℝ):=liftN T x V₀ M.k M.key M.park q e b₀ l; let W(e:ℝ):=liftN T x H.V H.k H.key H.park q e (H.bush x) l
 have hl(e):P e (i,p)=W e (j,p):=liftN_read h (he.scope (b:=(l+62)*radiusB x) (r:=(l+41)*radiusB x) (by simp_rw [Nat.add_mul]; omega) (Finset.Subset.refl _)) rfl
 change P _ _= P _ _; rw [hl d,hl b,show W d=W b from red_d T x b d _ _ _ V₀ _]
lemma wedge_h(i: Active M.key x M.park)(l':ℕ)(g:0<L)(h:‖M.z‖ ≤ L)(u:0≤Q)(p:MossX n l x M.key M.park T V₀ M.k Q d t q)(pβ:0<β)(e:MossX l' l x M.key M.park T V₀ M.k C s t q)(he:1000≤ radiusB x)(hf:S.ratio.parent i.val.val.1∉ M.key.dome ((l+62)*radiusB x)): let Y:=M.rich x T q d l β; let W:=Push.Uniform.shade G; ‖Y i‖≤ W*(C*t+coupling β*(2^n*Q*L)):=by
 intro Y V; obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈⟩:=e.jumps b₀; obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:=p.jumps b₀; let k:=coupling β; let P:=liftN T x V₀ M.k M.key M.park q d b₀ l; let R:= credW T M.key M.park M.k q d x b₀ l V₀; let H:= tape.symm (M.bell x); let F:=R *ᵥ H; have hz:k≥0:=(coupling_pos pβ).le
 have hW: ‖F‖ ≤2^n*Q*L:=by
    have hh:=airK (show Allows n (fun y:Directions G c=>ranQ (credW T M.key M.park M.k q d x b₀ l (Vmove x V₀ y))) 0 Q from h5) (allows_const 0 (v:=H) ((loomP (M.bell x)).trans ((pi_norm_le_iff_of_nonneg g.le).mpr fun i=> (norm_le_pi_norm M.z i.val.val).trans h))); simpa [Vmove] using hh.value
 let W:= liftN T x V₀ M.k M.key M.park q s b₀ l; have hp:‖W‖≤ C*t:=by simpa only [show Vmove x V₀ 0=V₀ from (by simp [Vmove])] using a₂.value
 have hx:tape P i=tape W i:=film_d i s p.ready he hf
 change ‖tape (P+k • F) i‖ ≤ _; rw [show tape (P+k • F)= tape P + k • (tape F) from ?_,Pi.add_apply,hx]; have ht:0≤V:= (Push.Uniform.shade_pos _).le
 · rw [mul_add,mul_left_comm V (coupling β)]; refine (norm_add_le ..).trans (add_le_add ?_ ?_); exact (norm_le_pi_norm ..).trans ((tintF W).trans (mul_le_mul_of_nonneg_left hp ht)); rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hz]; exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans ((tintF F).trans (mul_le_mul_of_nonneg_left hW ht))) hz
 exact (Next.SectorChange.colors.map_add _ _).trans (congrArg (tape P+·) (Next.SectorChange.colors.map_smul ..))
end YM.CF.Cloak
