import YM.SU5.Silk.Clock.Duty
import YM.SU5.Silk.Clock.Face
import YM.CF.Moto.Wage
import YM.CF.Beau.Blanch
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Salt
variable {Z':Scree.Hub n} {F: InkD n}(s:Sweep n)
local notation "Op"=> Z'.val.1
local notation "mV"=> moveHub s Z'
open Beau Moto
open Tap Hake Hove
abbrev mPath (s:Sweep n): Equiv.Perm (Site n):= Tofu (castX s) n
lemma nodeA(x:Site n): node (mPath s x)=boxA s (node x):= ((castX s).nodex x).trans ((Spire.stir_l s _).trans (sitA ..).symm)
lemma node_inj(n:Side): Injective (@Cube.node n):=fun x y h=> (assembly n).embed_injective (add_right_cancel (show _ +(1:Site (More n))=_+_ from h))
lemma mPath_apply(p:Sweep n)(x:Site n):(castX p).mills n x=mPath p x:=rfl
lemma mPath_seq(s t:Sweep n)(x:Site n):mPath s (mPath t x)=mPath (s*t) x:=node_inj _ (by rw [nodeA,nodeA,nodeA,step_V])
lemma mPath_one(x:Site n):mPath 1 x=x:=by
 apply node_inj n; rw [nodeA,sitA]; change affine 1 ((assembly n).root 0) (node x)=_; rw [map_zero]; simp [affine]
lemma mPath_inv(s:Sweep n): mPath s⁻¹=(mPath s).symm:=by ext1 x; rw [← (mPath s).injective.eq_iff,mPath_seq,mul_inv_cancel,mPath_one,Equiv.apply_symm_apply]
-- all translations allowed. affine shift includes parity lift
lemma across_m (x y:Site n)(p:Signed):∃ s:Sweep n,s.charge=false ∧ s.s=p∧mPath s y=x:=by
 let Q:Sweep n:=⟨p,0,false⟩; let v:=mPath Q y
 let T:Sweep n:=⟨1,x-v,false⟩
 have ht(x u:Site n): mPath (Sweep.mk 1 u false) x=x+u:=by
    apply node_inj n; rw [nodeA,sitA]; change affine 1 ((assembly n).embed u) (node x)=_; unfold Cube.node; simp only [affine,Signed.act_one,map_add, Ratio.root_embed]; abel
 exact ⟨T*Q,rfl,one_mul _,by rw [←mPath_seq,ht]; change v+(x-v)=x; abel⟩
lemma pass_hrap (x:Site n)(k:ℕ) : moveHub s (Φrap n (mPath s x) k)=Φrap n x k:=by
 let Y:= Φrap n (mPath s x) k; apply Subtype.ext; refine Prod.ext ?_ ?_
 · change (boxA s).symm (node _)= _; rw [nodeA,Equiv.symm_apply_apply]
 change actY s (Lattice.halo k {node (mPath s x)})= Lattice.halo k {node x}; rw [nodeA]; ext i; unfold actY; rw [Finset.mem_map_equiv]; simp [halo_spec,sitT]

lemma pay_way (s:Sweep n)(p:s.charge=false)(x:ℂ): Pec.pays s.s x=Spire.payZ s x:=by rw [Pec.complX]; simp [Spire.payZ,wageZ,p]
lemma det_rev(p:Signed): detX p⁻¹=detX p:=by
 have h:=det_p p⁻¹ p; rw [inv_mul_cancel,det_i] at h; cases t:detX p<;>cases v:detX p⁻¹<;>simp_all
lemma pay_rev(s:Sweep n)(x:ℂ):Spire.payZ s⁻¹ x=Spire.payZ s x:=by
 change cSignX (s.charge.xor (detX s.s⁻¹)) _=_; rw [det_rev]; rfl
lemma step_life(s:Sweep n)(p:s.charge=false)(Q:InkD n):Taxi.lifeH (step_F s Q) = Pec.pays s.s ∘ Taxi.lifeH Q ∘ pull s.s ((assembly n).embed s.b):=funext fun V=>by
 change pot ∅ (suit_Y s⁻¹ _) = Pec.pays s.s _; rw [pot_Z, castT]; change Spire.payZ s⁻¹ (pot ∅ (Q (flashA s V)))=_; rw [pay_rev, ← pay_way s p,revoke,p]; rfl
open Averaging
lemma glazed(s:Signed)(i:PlaqAxes):reframe (Averaging.ray (PlaqAxes.transform s i) (G:=SU.group)) s=(levy s i) • Averaging.ray i:=by
 ext1 j; by_cases t:j=i; · subst j; simp [frame_levy,Averaging.ray]
 rw [frame_levy]; simp [Averaging.ray,t,(PlaqAxes.transform s).injective.eq_iff]
private lemma glint (q : PlaqAxes → PlaqAxes → ℝ) (a b : PlaqAxes) (u v : ℝ) :
    AnalyticBridge.VerifiedReset.quad q (u • (Averaging.ray a (G:=SU.group))) (v • Averaging.ray b) = q a b * (u*v) := by
  rw [AnalyticBridge.VerifiedReset.quad, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]; swap
  · intro x _ hx; simp [Averaging.ray,hx]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ _)]; swap
  · intro y _ hy; simp [Averaging.ray,hy]
  simp [Averaging.ray,real_inner_smul_left,real_inner_smul_right,spike_norm Thera.yet_one,mul_comm v u]
private lemma sheen (V:Scree.Hub n)(f : Pot SU.group (More n))(t:(pintK P).Regular V.val.2 f)(o:Site (More n))(i j:PlaqAxes):
 logHessian f ((primitive (Averaging.ray i)).field o) ((primitive (Averaging.ray j)).field o)=AnalyticBridge.VerifiedReset.coeff f o i j:=by
 rw [flux_formula _ Thera.yet_one t]; simpa [AnalyticBridge.VerifiedReset.quad] using glint (AnalyticBridge.VerifiedReset.coeff f o) i j 1 1

lemma boost_face(s:Sweep n)(t:s∈Whirl n)(Z:Scree.Hub n)(p:PressB P (moveHub s Z) F h b)(hn:4≤(More n).val)(hx:0≤h)(hy:Nonwrapping (moveHub s Z).val.2 (moveHub s Z).val.1):
 tooth Z.val.1 P (step_F s F)=localFace s.s (tooth (moveHub s Z).val.1 P F):=by
 let J:=step_F s F; let Q:=moveHub s Z; funext i j; obtain ⟨i,rfl⟩:=(PlaqAxes.transform s.s).surjective i; obtain ⟨j,rfl⟩:=(PlaqAxes.transform s.s).surjective j
 let i':= PlaqAxes.transform s.s i; let j':= PlaqAxes.transform s.s j; let b':=(assembly n).embed s.b; have hJ:=pay_all_F P s Z b t p hx
 let B:= levy s.s i * levy s.s j; change tooth _ _ J i' j'= _; rw [face_p]
 have h(L:ℂ→L[ℝ]ℝ): L (tooth Z.val.1 P J i' j')= L (B • Pec.pays s.s (tooth Q.val.1 P F i j)):=by
    let T:= L ∘L (Pec.pays s.s); rw [map_smul]; change _= B*T _
    let K:=L ∘ Taxi.lifeH J; let U:= T ∘ Taxi.lifeH F
    have hz:K=U ∘ pull s.s b':=by unfold K J; rw [step_life s ((whirl s).1 t).1]; rfl
    let Hv:= (cashR _ Z hJ hx L _ le_rfl).regular; let Hk:= (cashR _ Q p hx T _ le_rfl).regular
    rw [cym P J Z hJ hx, cym P F Q p hx]; suffices h: AnalyticBridge.VerifiedReset.coeff K Z.val.1 i' j' = B*AnalyticBridge.VerifiedReset.coeff U Q.val.1 i j by rw [h,mul_assoc]
    have ht:= flux_hessian_pull s.s b' Q.val.1 Thera.yet_one Hk hy hn (Averaging.ray i') (Averaging.ray j'); rw [← hz, ← show Z.val.1= affine s.s b' Q.val.1 from (Taxi.chart_p s Z).1, flux_formula _ Thera.yet_one Hk, sheen Z K Hv] at ht
    unfold i' j' at *; rw [glazed, glazed] at ht; exact ht.trans ((glint (AnalyticBridge.VerifiedReset.coeff U Q.val.1) i j (levy s.s i) (levy s.s j)).trans (mul_comm ..))
 exact Complex.ext (h Complex.reCLM) (h Complex.imCLM)
end YM.CF.Ione.Clock
