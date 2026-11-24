import YM.CF.Reine.Aeon
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Reine
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
open Forge
structure Vital (P:Teller G)(Q:Patch)(J:ChartRatio G)(n j l:ℕ)(q:Chi)(w width γ x A B s C D:ℝ) : Prop where
 safe : SafeX P Q J w γ width 0 j n x
 auth : ∀{c f:Side}(S:StepData c f)(T:Tube G S),Cert Q P S T x→∀ b:ℝ,1 ≤ b → Volo S n s D b (covetM G n b C D)
 heat : ∀ β∈ Set.Icc (y G Q.L x/2) (2*y G Q.L x), let t:=fiery G x Q.L; let d:=width*t; let h₀:=B*Scales.p G Q.L x; let L:=shotM J h₀ β;
     0<t ∧ t ≤ s/2 ∧ 0<β∧0 < h₀ ∧ 0<L ∧ wireP G (coupling β) d (A*t) A ≤ h₀ ∧∀{c f:Side}(S:StepData c f)(T:Tube G S),Cert Q P S T x → ∀ M: Monk G S,sizedP G Q P S T M.park→M.key.flags=flags (temp x) M.V→ MossX n l x M.key M.park T M.V M.k A d t q ∧∀ (p p':BudgetPoint),p.threshold=t → p'.threshold=temp x→∀ r:ℕ,(j+110)*radiusB x+10 ≤ r→ let Z(α:ℝ):= tenderU T x M q d l β p p' α; (∀ α:ℝ,L^Fintype.card (Active M.key x M.park)*(Fintype.card S.Choices:ℝ)* Girt.plight T x β q J d l w M*Real.exp (-(Z α))=L^ Fintype.card M.park.Free*yeoman T x M q d l β p p' J w s L r j α) ∧ (PointCharge T x w γ→‖M.z‖ ≤ h₀→∀ i∈blip S M.key r, ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E](z:E→L[ℝ] Directions G c), ‖z‖ ≤ 1 → (∀ u:E, axl M.key.flags (temp x•z u)=temp x • z u) → Allows n (fun u=> treat T x (M.atop (z u) x) q d l β J w s L r j i) 0 (Real.exp (-γ/16*(Scales.p G Q.L x)^2*i.val.shares)))
lemma pack_z(h:Packet O A v)(p:r≤v):Packet O A r:=⟨h.subset_plots,fun i t u=> Disjoint.mono (Corona.halo_mono p (Finset.Subset.refl _)) (Corona.halo_mono p (Finset.Subset.refl _)) (h.2 i t u)⟩ -- tune fields
lemma prismT (P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:4 ≤ j)(hl:l ≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(R:ChartRatio G)(hp:LocalRatio R)(w γ:ℝ)(hw:0<w)(hγ:0<γ):∃ N:ℝ,1≤N∧∀ width≥N,∃ A B s M M':ℝ,0<A ∧0<B∧0<s∧1≤M∧1 ≤ M' ∧ ∀ᶠ x:ℝ in atTop, Vital P Q R n j l q w width γ x A B s M M' :=by
 obtain ⟨N,hN,Hn⟩:=help P Q h hp w γ hw hγ; refine ⟨N,hN,fun width vy=>?_⟩; have hi:0<width:=zero_lt_one.trans_le (hN.trans vy)
 obtain ⟨A,B,C,D,M,L,u,m,K,s,h₁,h₂,hA,hB,hC,hD,hM,hL,hu,hm,hK,hs,hp₁,hp₂,H⟩:= vestaM P Q h n j l hn (by omega) hl W W' q R hp w width γ 0 hw hi
 obtain ⟨D',hv',ht'⟩:= owns P Q q n width hi h
 refine ⟨A,B,s,h₁,h₂,hA,hB,hs,hp₁,hp₂,?_⟩; filter_upwards [H,Hn width vy 0 j n, payer Q n j w width C D M L u m K s hγ hD hL, capable P Q, ht', pauce R hp (γ/16) (by positivity) Q j,(Scales.peak G Q.L).eventually_ge_atTop (1/B), Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel Q +100), eventually_gt_atTop (0:ℝ)] with x hx Hx hx' he ht hp' hv hq hz
 refine ⟨Hx,hx.2.1, fun β v=>?_⟩; intro t d Y L'; obtain ⟨h1,h2,h3,h4,h5⟩:=hx.2.2.wear _ v; have hY':=hp' Y (show 1 ≤ Y from (le_of_eq (by field_simp : (1:ℝ)=B*(1/B))).trans (mul_le_mul_of_nonneg_left hv hB.le)) β v
 refine ⟨h1,hx.1,h2,h3,hY'.1,h4,@fun c f S T p A' F e=>?_⟩; have hW:=h5 S T p; refine ⟨(hW A'.key A'.key A'.park A'.V A'.k F e).1,fun p₁ p₂ ℓ κ r b=>?_⟩; intro a; have hs₀:=ht S T p A'.key A'.park A'.V e A'.k; dsimp only at hs₀; rw [p.got] at hs₀; have hh:t=fiery G x S.patch.L:=by rw [p.got]
 obtain ⟨u',x'⟩:= he _ _ p.got p.funds.1
 constructor
 · intro α; let X:=max 1 SU.group.colorScale; have hp:= hx.2.1 S T p X (le_max_left ..); exact plunge _ _ _ _ _ _ _ p₁ p₂ _ _ R w s L' r j α p (D:=X) (fun i=> (gan _).mono (le_max_right ..)) (by rw [p.got]; omega) hp (hh ▸ h1) (by rw [p.got]; exact hx.1) e hY'.1.ne' b (by unfold taxM Stores.till; have ht:=Nat.mul_le_mul_right (radiusB x) hj; omega) h2 (ℓ.trans hh) κ u' x' (Work.E09.temp_pos hz) (congrFun hs₀.1 _)
 intro Dp h i g E _ _ _ z hz hp; have hI:0 < i.val.shares:= (vase_d S i.val ▸ card_pos.mpr i.property.1)
 let R':=Real.exp (-γ/8*(Scales.p G Q.L x)^2*i.val.shares)
 have hy:Allows n (fun x':E=> (A'.atop (z x') x).pep x T s i.val q d l β w R j) 0 R':=by
    apply Allows.mono ((hW i.val A'.key A'.park A'.V A'.k F e).2 (pack_z (pack S i g) (by simp_rw [Nat.add_mul] at *; omega)) Dp Hx (A'.bush x) (A'.bell x) ((pi_norm_le_iff_of_nonneg h3.le).mpr fun v=> (norm_le_pi_norm A'.z v.val.val).trans h) E z hz hp (latticeFieldEstimates i.val j x) (fun i=> by exact_mod_cast vault j)); exact hx' S p.got A'.key i.val hI A'.park β v
 let t':=trig ((j+100)*radiusB x) i.val; let Q':=t'*L'⁻¹^ Fintype.card (Frozen i.val x A'.park); apply Allows.mono ((hy.smul Q').germ ?_)
 swap
 · apply Eventually.of_forall; intro a; unfold treat; change Q'*_=(_*t')*L'⁻¹^ Fintype.card (Frozen i.val x A'.park); unfold Q'; ring
 exact (mul_le_mul_of_nonneg_right (hY'.2 S p.got A'.park i.val) (Real.exp_pos _).le).trans_eq (by rw [←Real.exp_add]; congr 1; ring) -- tune
end YM.CF.Reine
