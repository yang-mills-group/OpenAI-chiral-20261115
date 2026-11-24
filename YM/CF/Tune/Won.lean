import YM.CF.Tune.Woe
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tune
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
open PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.VerifiedReset Siete Taxi Moto
variable {n m:Side}{E P:BudgetPoint}{S:StepData (More n) (More m)}{T:Tube SU.group S}{q o v x y:ℝ}{k:ℕ}{M:Side}
local notation "XΦ"=> PlaqAxes×PlaqAxes
variable (Z:Skate)(A i:PlaqAxes)(u:Verc Z)(hx:∀ i j, ‖Z i j‖≤v)
variable (Y: Config SU.group (More n) → Config SU.group (More m))(X:Support (More m))(X':Support (More n))(a:Site (More n))
local notation "a0"=> S.ratio.embed a
local notation "Lx"=> (M.val:ℝ)⁻¹
local notation "θ"=> E.threshold
local notation "θ₂"=> P.threshold
variable (h:Tale.Wyth T X Y a E M q)(hk:Lattice.halo 2 {S.ratio.embed a}⊆ X)
local notation "IV"=> increment (1:Pane n)
local notation "ZΦ"=> M--dummy
local notation "HΦ"=> θ^2*Lx^4 / θ₂^2
variable (vP:∀ i j:PlaqAxes, ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) (Tale.quanta Y (S.ratio.embed a) i j) 0)
local notation "E'"=> tangD n
local notation "K"=> ![Tale.clipT E a A,Tale.clipT E a i]
local notation "PΓ"=> kerP a0 P Z
local notation "PS" t:max=> ((Z t.1 t.2)/((2:ℝ)*θ₂^2:ℝ)) -- coerces
local notation "Cκ"=> (Fintype.card XΦ:ℝ)
local notation "Yq" t:max=> (Tale.a_Op (More m) a0 t.1 t.2)
-- plain expansion
local notation "B"=> PlaqAxes
variable(AK: DayT P.order x)(hA:0 ≤ x)(hL:20<(More m).val)
include hk hx AK hA
variable (oX:Scree.Hub m)(p0:oX.val.2=X)(g:oX.val.1=S.ratio.embed a)
include p0 g
lemma mark_m (v0:ℝ)(hu:0 ≤ v0) (p: PressB P oX (plateZ a0 P Z) v0 y) : MotionB P X a0 (PΓ) y:=by
 let W:=plateZ a0 P Z; let F:= kerP a0 P Z; let V(U):=crumb (W U).val ∅; have he:V=F:= funext fun i=> Pastry.hullB _
 have hK:MotionB P oX.val.2 oX.val.1 V y:=by
    refine ⟨fun U v=>eraF W oX p hu U v,oX.property,(by rw [he]; simp [F,kerP,counter,AnalyticBridge.VerifiedReset.quad]),fun i j q=>congrArg Pastry.pane (p.term i j q),fun x U=>?_ ,?_ ⟩
    · change Taxi.lifeH W _= _; unfold W Taxi.lifeH; rw [p.gaugeV]; exact Pastry.center_b ..
    exact ((show Continuous (Pastry.pane (n:=LeanV (Single m))) from mast_cont.comp continuous_subtype_val).measurable.comp p.measureV)
 rw [p0,g,he] at hK; exact hK
omit hx p0 g
local notation "Ta" b:max v:max => (Tale.a_Op (More m) a0 b v)
lemma mote_l (i j:PlaqAxes):MotionB P X a0 (Complex.ofRealCLM ∘ (Tale.a_Op (More m) a0 i j)) (‖Complex.ofRealCLM‖ * (x*(pairBill SU.group P *θ₂^2))):=by
 let F:Pane m→ℝ:=Tale.a_Op _ a0 i j; let Bh:= x*(pairBill SU.group P*θ₂^2); have he:a0∈X:= hk (halo_subset _ _ (mem_singleton_self _))
 have hx:LocalOn X F:=by intro y z p; unfold F Tale.a_Op; simp_rw [petals_reads a0 i _ z (agrees_mono p (Finset.coe_subset.mpr hk)),petals_reads a0 j _ z (agrees_mono p (Finset.coe_subset.mpr hk))]
 refine ⟨fun U u=>?_ ,he,(by simp [Tale.a_Op]),fun i j p=>congrArg Complex.ofReal (hx i j p),fun x U=>?_ ,Complex.ofRealCLM.continuous.measurable.comp ((show Continuous F from ?_).measurable)⟩
 · have hu: Healthy P.threshold {a0} U:= Finset.disjoint_of_subset_left (singleton_subset_iff.mpr he) (ping_le u)
   have hx:Signs P a0 (F ∘ increment U) (x*(pairBill SU.group P*_)):=AK m P _ a0 _ _ (AnalyticBridge.VerifiedReset.pair_paid P a0 i j) rfl _ hu; exact skills ((skin hx).linear Complex.ofRealCLM le_rfl)
 · simp only [Function.comp_apply,Tale.a_Op, petals_gauge,StressFlux.inner_adjoint] -- tune instance ns
 unfold F Tale.a_Op; exact (petals_cont ..).inner (𝕜:=ℝ) (petals_cont ..)
omit hk hA AK
-- before L Price from romant
structure Stance(k:ℕ)(Q:ℝ)(b:ℝ):Prop where
 ge:1 ≤ b
 y_:∀ {n m:Side}{E P:BudgetPoint}{S:StepData (More n) (More m)}{T:Tube SU.group S}{L:Side}{F:Pane n→Pane m}{X:Support (More m)}{X':Support (More n)}{o:Site (More m)}{V:Pane n}, Glow E P T Q k X X' o V F L → Nonwrapping X o → k ≤ P.order → E.order=k → 4≤ (More m).val → ∀ {W:Pane m→ℂ}{z:ℝ},MotionB P X o W z → Signs E (S.ratio.parent o) ((W ∘ F) ∘ increment V) (b*(L.val:ℝ)⁻¹^4*z)
lemma tent(k:ℕ)(v:4 ≤ k)(b:ℝ)(h:1 ≤ b):∃ C:ℝ,Stance k b C:=by obtain ⟨C,v,h⟩:= romant k v b h; exact ⟨C,v,@fun n m E P S T L F X X' o V h0 hu hw i u W y=>h h0 hu hw i u⟩
variable{γ Q:ℝ}(L0:Stance k Q γ)(p:Glow E P T Q k X X' (S.ratio.embed a) 1 Y M)(u_:Nonwrapping X (S.ratio.embed a))(ht: k ≤ P.order)(w:E.order=k)(j:PlaqAxes)
include L0 p ht w u_ hk hL AK hA
lemma flux_S (j':PlaqAxes): ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) (Tale.quanta Y a0 j j') 0:=by
 have he:= mote_l (S:=S) X a hk AK hA j j'; have hx:= (L0.y_ p u_ ht w (by omega) he).paid
 exact Complex.reCLM.contDiff.contDiffAt.comp 0 (hx.of_le (Nat.cast_le.mpr ((by decide:2≤6).trans E.order_ge))) -- tune definal eq
end YM.CF.Tune
