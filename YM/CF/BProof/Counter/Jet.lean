import YM.CF.BProof.Counter.Wilson
import YM.CF.BProof.Floral.Vixen
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.CF.Pso.Solo
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi.Denn
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D' Y Z:Support (More n)}{U:Pane n}
open AnalyticBridge.VerifiedReset Next.Foundations Push.Local PhysicalNext.JointLoad Heir
open Vow Rue Ione Larch Beau Floral
-- `block`=C_o, exact Halo radius 2
abbrev block (x:Skye.Seat n): Scree.Hub n:= ⟨(x,halo 2 {x}), halo_subset _ _ (mem_singleton_self _)⟩
abbrev joined (x z: Skye.Seat n): Scree.Hub n:=⟨(x,(block x).val.2 ∪(block z).val.2), mem_union_left _ (block x).property⟩
lemma block_inj : Injective (block (n:=n)):= fun _ _ h=> congrArg (fun i:Scree.Hub n=>i.val.1) h
abbrev wish (x:Skye.Seat n): Pane n→ℝ := Compass.W x
abbrev W (x:Skye.Seat n)(a:ℝ) : InkD n := moldV n ∘ (a • wish x)
lemma W_le{x':Skye.Seat n}(t:pingS P.threshold {x'} U) : ‖wish x' U‖ ≤ Compass.compassCost SU.group P * P.threshold^2:=by exact AnalyticBridge.VerifiedReset.Bill.norm (Compass.paid P x') (l:=[]) (by simp) (by simp) (ping_le t)
lemma W_flash (s:Sweep n)(o:Skye.Seat n) : wish o (flashA s U)=wish (boxA s o) U:=by
 rw [revoke]; let θ:= Lattice.pull s.s ((assembly n).embed s.b) U; have hs(b:Bool): wish o (polarT b ∘ θ)=wish o θ:= by
    cases b; rfl
    change Compass.W o (Reef.echo θ) = Compass.W o θ; simp only [Compass.W,Compass.around,Compass.compass,Reef.echo_t,Reef.cold];
 rw [hs s.charge]; exact Compass.W_pull ..
lemma W_turn (s:Sweep n)(x:Skye.Seat n)(C:Cipher n→ₐ[ℝ] Cipher n): W ((boxA s).symm x) a (flashA s U)= C (W x a U):=by
 unfold W; simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul,W_flash,Equiv.apply_symm_apply]; symm; change C ((_ :ℝ) • (1:Cipher n))= _; rw [map_smul,map_one]; rfl
lemma block_map(s:Sweep n)(x:Skye.Seat n): block ((boxA s).symm x)=moveHub s (block x):=by
 refine Subtype.ext (Prod.ext rfl (ext ?_)); intro i; change i ∈ Lattice.halo 2 _ ↔i ∈ Finset.map _ (Lattice.halo 2 _); rw [Finset.mem_map_equiv]; simp only [halo_spec,mem_singleton,exists_eq_left]; nth_rw 2 [← Equiv.apply_symm_apply (boxA s) x]; rw [Equiv.symm_symm,sitT] -- tune
lemma joined_map(s:Sweep n)(x y:Skye.Seat n) : joined ((boxA s).symm x) ((boxA s).symm y)= moveHub s (joined x y):=by apply Subtype.ext; apply Prod.ext; rfl; change (block ((boxA s).symm x)).val.2 ∪ (block ((boxA s).symm y)).val.2=(Finset.map (boxA s).symm.toEmbedding ((block x).val.2∪(block y).val.2)); rw [block_map,block_map,map_union]; rfl
lemma mould_map(s:Sweep n)(x:Scree.Hub n): pur (moveHub s x)=moldA s (pur x):=rfl
lemma joined_in(x y:Skye.Seat n)(h:separation x y≤ m)(z)(u:z∈(joined x y).val.2): z∈ Lattice.halo (m+2) {x}:=by
 rcases mem_union.mp u with t|t; exact Corona.halo_mono (by omega) le_rfl t
 obtain ⟨j,p,w⟩:=Lattice.halo_spec.mp t; rw [mem_singleton.mp p] at w; exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle ..).trans (add_le_add h w)⟩
lemma cover_c (P:BudgetPoint)(x:Skye.Seat n)(k:6 ≤ P.B): coverNumber P.B (block x).val.2 ≤ 1:= (Corona.cover_mono (Corona.halo_mono (by omega:2 ≤ P.B) le_rfl) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)
lemma cover_j (P: BudgetPoint)(x y:Skye.Seat n)(h: separation x y≤ m)(k:m+2≤ P.B):coverNumber P.B (joined x y).val.2≤1:= (Corona.cover_mono (Subset.trans (fun _ v=>joined_in x y h _ v) (Corona.halo_mono k le_rfl)) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)
private lemma pressB {F: Pane n→ℝ}{T: Scree.Hub n}(g:P.Regular T.val.2 F)(w:∀ U,pingS P.threshold T.val.2 U→ Signs P T.val.1 (F ∘ increment U) a):PressB P T (moldV n ∘ F) h (‖Complex.ofRealCLM‖*a):=by
 let k:=‖Complex.ofRealCLM‖*a; have he(i) (z:pingS P.threshold T.val.2 i):Signs P T.val.1 ((Complex.ofRealCLM ∘ F) ∘ increment i) k:= Prism.skills ((Prism.skin (w i z)).linear Complex.ofRealCLM le_rfl)
 have ht:= (he 1 (ping_f P T.val.2)).grade; let L:=moldV n
 refine ⟨fun i j p=> congrArg L (g.sites _ _ p),fun i=>?_,L.continuous.measurable.comp g.borel,fun i v'=>?_ , Pi.single ∅ k,fun i=>?_,fun i z j=>?_,?_ ⟩
 · rw [Function.comp_apply,mon_v]; exact Flour.grainE.smul _
 · simp only [Function.comp_apply]; change (_:ℝ) • (1:Cipher n)= _
   change _= paintR false false _ ((_ :ℝ) • (1:Cipher n)); rw [map_smul,map_one,g.symmetry v' i]
 · rw [Pi.single_apply]; split_ifs; exact ht; exact le_rfl
 · by_cases t:j=∅; · subst j; rw [Pi.single_eq_same]; refine Prism.mint (he i z) (Eventually.of_forall fun x=>?_); change (_:ℂ)=Pastry.pane (moldV n (F _)); rw [mon_v, hullB]; rfl
   rw [Pi.single_eq_of_ne t]; refine Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 by rw [norm_zero])) (Eventually.of_forall fun y=>?_ ); change (0:ℂ)= crumb (L (F _)).val j; unfold L; rw [mon_v]; change _=(((_ :ℝ):ℂ) • (1:FC (Dwell n))) j ∅; simp [t]
 apply le_of_eq; simp [Pi.single_apply,Scree.tariff,endL,mul_ite,k]
abbrev TC (P:BudgetPoint)(m:ℕ)(Γ:ℝ):= ‖Complex.ofRealCLM‖*(1+m:ℝ)^(P.power*P.order)*Γ*Compass.compassCost SU.group P
def jet (P:BudgetPoint)(m:ℕ)(Γ a:ℝ):ℝ:= TC P m Γ * |a| * P.threshold^2
lemma W_paid (a:ℝ) (x:Skye.Seat n)(T:Scree.Hub n)(k:(block x).val.2⊆T.val.2)(p:separation T.val.1 x≤ m){Γ:ℝ}(A:DayT P.order Γ) : PressB P T (W x a) h (jet P m Γ a):=by
 let g:= Compass.compassCost SU.group P * P.threshold^2; let v:= Γ*(|a| * g)
 let F:=a • wish x; rw [jet,show TC P m Γ*|a| * P.threshold^2= ‖Complex.ofRealCLM‖*((1+m:ℝ)^(P.power*P.order)*v) from (by unfold TC v g; ring)]; apply pressB (reg_larger (AnalyticBridge.CouplingShape.reg_scale a (Compass.regular P x)) k)
 intro V t; have hv:Signs P x (F ∘ increment V) v:= A _ _ _ _ _ F (AnalyticBridge.VerifiedReset.Bill.mul_left a (Compass.paid P x)) rfl _ (Finset.disjoint_of_subset_left ((halo_subset 2 _).trans k) (ping_le t))
 have hw: spine P.power x T.val.1 ≤ (1+m:ℝ)^P.power:=by unfold spine; rw [separation_comm x]; gcongr
 have hp:0≤ (1+m:ℝ)^(P.power*P.order):=by positivity
 exact ⟨mul_nonneg hp hv.grade,hv.paid,fun i f y t=>(Siete.rise_i i (hv.token i f) y t).trans (mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ (spine_one ..) f).trans ((pow_le_pow_left₀ (spine_pos ..).le hw _).trans_eq (pow_mul ..).symm)) hv.grade)⟩
lemma W_zero(x:Skye.Seat n): W x 0=0:=funext fun i=> (by unfold W; simp)
lemma W_1(x:Skye.Seat n)(a:ℝ): W x a 1=0:=by simp [W,wish]
lemma same_hessian(P:BudgetPoint)(x y:Skye.Seat n)(h:10*(separation x y+2)<(More n).val)(a:ℝ) : Beau.spark x (W y a-W x a):=by
 let X:= joined x y; let U:=a • wish x; let V:=a • wish y; have hu:P.Regular X.val.2 U:=reg_larger (AnalyticBridge.CouplingShape.reg_scale a (Compass.regular P x)) Finset.subset_union_left; have hv:P.Regular X.val.2 V:=reg_larger (AnalyticBridge.CouplingShape.reg_scale a (Compass.regular P y)) Finset.subset_union_right
 rw [show W y a-W x a=moldV n ∘ (V-U) from funext fun i=> (map_sub (moldV n) _ _).symm]
 apply Beau.spark_H (X':=X) (reg_sub hv hu) (by simp [U,V,wish]); apply affine_zero (reg_sub hv hu)
 intro j; rw [hessian_sub hv hu]; change logHessian V (j.field x) _- logHessian U (j.field x) _ = _; rw [show V=a • wish y from rfl,show U=a • wish x from rfl]; unfold wish; rw [Compass.W_diag P Thera.yet_one x j (by rwa [separation_comm y]),Compass.W_diag P Thera.yet_one x j (by rw [separation_self]; omega),sub_self]
end YM.CF.Taxi.Denn
