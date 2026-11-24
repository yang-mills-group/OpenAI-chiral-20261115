import YM.SU5.Interaction.Kerosene.KernelBond
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees
open Cadre Ione Bake Stax Vow Larch Sour Rue Trees Mew Rive
variable {I:Type*}[DecidableEq I]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
variable (F:Cusp n)(r: Tape (A:= Seat n))(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h (cipherK m) X D (F X D) (r X D))
variable (K:I→Rinse (Seat n) (Copy n))(C H B:I→Aura n→ℝ)(γ κ:ℝ)
variable (M:I→Orbit n→Aura n→ FC (Dwell n))(G :Finset I) (D:I→ Support (More n))
variable (g: ∀ i∈ G,WickL P h (cipherK m) (K i) (C i) (H i) (M i) (D i))(u:0 ≤ h)
variable (β: Aura n→ℝ)(p:Tour β b)
local notation "R:" t:max => loom_v t 0 β 0
local notation "RU:" t:max => loom_v t 0 (widthK n P.B) 0
section receipts
variable (α δ k c:ℝ) (dα: 0≤ α) (dδ:0<δ)(dγ:0 ≤ γ)(w0: b*c ≤ δ)(b0:0 ≤ b)(c0: 0 ≤ c)(wb:b*γ ≤ δ)
local notation "Y_"=> (R:(α+δ))
local notation "Xtκ"=> (R:(α+δ+δ))
local notation "Bt"=> fun i: I=> C i * Xtκ
include p
lemma tallerβ(z t:ℝ)(h:z≤t) : (R:z) ≤ (R:t) := fun i=> Real.exp_monotone (mul_le_mul_of_nonneg_right (sub_le_sub_right h _) (zero_le_one.trans (p.pos i))) -- tune subtract direction include p
variable (C0:∀ i∈G,0≤C i) (H0:∀ i∈ G,0≤H i)
variable (fee:∀ x:Seat n,nook (∑ i∈G,C i*(loom_v (α+δ+δ+δ) 0 β 0)) x ≤ c)(pay:∀ x:Seat n,nook (∑ i∈G,H i*(loom_v (α+δ) 0 β 0)) x ≤ k)
local notation "Next"=> (maestro (Bt) G (R:α))
include wb C0 p dγ
lemma petrol (i:I)(v:i∈ G) : Cadre.fog Y_ (C i) γ ≤ (Bt) i := by
 intro x; let U:=β x; unfold Cadre.fog; change _ ≤ C i x*_ ; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left; swap; · exact C0 i v x
 unfold loom_v waveL; rw [←Real.exp_add]; apply Real.exp_monotone; have he:= mul_le_mul_of_nonneg_right (p.rate x) dγ; have h0:= mul_le_mul_of_nonneg_right wb (zero_le_one.trans (p.pos x)); nlinarith only [he,h0]
omit wb dγ
include w0 dδ c0 fee
lemma vil_est : Next ≤ Y_ :=by
 let C'(i:I): VX→ℝ:=C i* Xtκ; have ht(i)(v:i∈G)(Z):=tallerβ β p (α+δ+δ) (α+δ+δ+δ) (le_add_of_nonneg_right dδ.le) Z; have hC:∀ i∈G,0≤ C' i:=fun i v X=>mul_nonneg (C0 i v _) (Real.exp_pos _).le
 refine (maestro_salary C' G hC β b p α c c0 (fun i=> le_trans ?_ (fee i))).trans (tallerβ β p _ _ (add_le_add_right w0 _)); refine sum_le_sum fun j _=>?_ ; rw [Finset.sum_apply, Finset.sum_apply]; exact sum_le_sum fun i v=> mul_le_mul_of_nonneg_left (ht i v j) (C0 i v _)
-- initial slack. gamma. No roots. Bring into registry from all kernel data before this lemma.
variable (y t:ℝ)(old:∀ i:Seat n,nook (roofL r 1 * (loom_v (α+δ) 0 β 0)) i ≤ y)(he: y+k+γ*(δ⁻¹*b)*c ≤ γ)
include hF u dα H0 pay old he b0 wb dγ
lemma vigil : SafeBand r 1 H Bt γ (R:α) Y_ G := by
 let C'(i:I): VX→ℝ:=C i* Xtκ; have hstep:=vil_est C G β p α δ c dδ w0 c0 C0 fee -- tune
 have ht (i:VX): (Xtκ i)*(i.val.card:ℝ) ≤ (δ⁻¹*b)* (R:(α+δ+δ+δ)) i:= by
    let t:=α+δ+δ; let x:=β i; have he:x≥1:=p.pos _
    let W:=Real.exp (t*x); let X':=Real.exp ((t+δ)*x); suffices hh: (δ:ℝ)*(W*x) ≤ X' by
       refine (mul_le_mul_of_nonneg_left (p.rate i) (Real.exp_pos _).le).trans ?_; rw [mul_left_comm _ b,mul_comm δ⁻¹,mul_assoc b]; apply mul_le_mul_of_nonneg_left; swap; · exact b0
       apply (le_inv_mul_iff₀ dδ).mpr; unfold loom_v; simpa only [zero_mul,sub_zero] using hh
    unfold X'; rw [add_mul,Real.exp_add,mul_left_comm]; apply mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (δ*x)]) (Real.exp_pos _).le
 have hg:=Fiery.roof r 1 (fun i D p=> (hF i D p).merit.wage u) le_rfl
 refine ⟨fun i=>?_ ⟩; refine le_trans ?_ he
 let A(k:I)(j:Aura n):=H k j* Y_ j; let g(k:I):= shelfR (C' k) i
 have hv :∑ k∈G,πSeat (C' k) (H k) γ Y_ i=(∑ k∈G,nook (H k*Y_) i)+ γ*∑ k∈G,g k:=by unfold πSeat; rw [sum_add_distrib,mul_sum]; simp only [g,mul_comm γ]
 rw [show ∑ k∈G,πSeat (C' k) (H k) γ Y_ i= _ from hv] -- replace
 have hp:(∑ k∈G,nook (H k* Y_) i)≤ k:= by unfold nook; rw [sum_comm]; have hs:=pay i; unfold nook at hs; simp_rw [Finset.sum_apply] at hs; exact hs
 have hu:nook (roofL r 1*maestro C' G (R:α)) i≤ y:= (sum_le_sum (s:=spark i) (fun j _=>mul_le_mul_of_nonneg_left (hstep j) (hg j))).trans (old i)
 have hx:(∑ k∈G,g k)≤ (δ⁻¹*b)* c:=by
    unfold g shelfR; refine le_trans ?_ (mul_le_mul_of_nonneg_left (fee i) (by positivity)); rw [sum_comm]; unfold nook; rw [mul_sum]; refine sum_le_sum fun j _=> ?_; rw [Finset.sum_apply,mul_sum]; refine sum_le_sum fun k p=>?_ ; change C k j*Xtκ j* _≤ (_:ℝ)* (C k j* _); rw [mul_assoc,mul_left_comm (δ⁻¹*b)]; exact mul_le_mul_of_nonneg_left (ht j) (C0 k p j)
 change _≤ _; rw [←add_assoc, mul_assoc γ]; exact add_le_add (add_le_add hu hp) (mul_le_mul_of_nonneg_left hx dγ)
end receipts
local notation "βq"=> widthK n P.B
local notation "ℓ"=> loom_v

section realdata
variable (c y u':ℝ)(l:ℝ)(t:0<d)(w:0 ≤ l)(vp:0 ≤ γ)(p0:3 ≤ P.B)
-- grants. a= regulator exponent's rate? L be target after two decreases. give fees at L+5*d and terms quote_M≤ at L-d.
local notation "αt"=> l+d+d
local notation "βt" => Sour.spanV P.B
local notation "Vt" => (RU:(αt))
local notation "Ht"=> (RU:(αt+d+d))
local notation "Wt"=> (RU:(αt+d))
variable (v0:0 ≤ c)(fee:∀ i:Seat n,tallB (∑ j∈ G,C j) P.B (l+5*d) i ≤ c)(q:∀ i:Seat n,tallB (∑ j∈ G,H j) P.B (l+3*d) i ≤ y)
variable (v: ∀ i:Seat n,tallB (roofL r 1) P.B (l+3*d) i ≤ u')(hS:spanV P.B*c≤d)(hT:spanV P.B*γ ≤ d)(hx:u'+y+ γ*(d⁻¹*Sour.spanV P.B)*c ≤ γ)
lemma lushMarkov (N:Aura n→ℝ)(i:Seat n) (k:ℕ)(x:ℝ): nook (N*ℓ x 0 (widthK n k) 0) i=tallB N k x i:=by rw [←Sour.parse]; simp
lemma lushT (q:I→Aura n→ℝ)(i:Seat n) (k:ℝ): tallB (∑ j∈G,q j) P.B k i=nook (∑ j∈G,q j*(RU:k)) i:=by rw [←lushMarkov,sum_mul]; -- `sum_mul` rewrites?

variable (L':List I)(vL:G=L'.toFinset)(pu:L'.Nodup)(hg:Turf (fun i=> woodBar K L' F i ∅))
include hF u t w vp p0 vL pu g hg v fee q hS hT hx v0
lemma packReservoir : Reservoir h d m P (woodBar K L' F) (woodTariff C H L' r) γ l:= by
 let B':= fun i:I=>C i*Ht; let β:ℝ:=Sour.spanV P.B; let α:=αt; let Z:=woodBar K L' F; let F':=woodTariff C H L' r
 have hb:0≤β:=by positivity -- dsimp
 have hh:=vigor n P.B; have hδ:0≤ αt:=by linarith only [t,w]
 have hv:0≤ Vt:= fun i=> (Real.exp_pos _).le; have hW:WarmStyle Vt:= fun X Y T p=>tier (αt) 0 (widthK n P.B) hh 0 (by linarith) le_rfl _ _ _ ⟨le_rfl,le_rfl⟩ p
 have pC:=fun i v=>(g i v).dice; have hc(i)(v:i∈G):0≤ H i:=fun X=> ((g i v).birth X).merit.wage u
 have he(i:Seat n): nook (∑ j∈G,H j * Wt) i≤ y:=by rw [←lushT, show αt+d=l+3*d by ring]; exact q _
 have hy(i:Seat n): nook (∑ j∈G,C j*(RU:(αt+d+d+d))) i≤ c:=by rw [←lushT, show αt+d+d+d=l+5*d by ring]; exact fee _
 have hq:SafeBand r 1 H B' γ Vt Wt G:= vigil F r hF C H γ G u (widthK n P.B) hh (αt) d y c hδ t vp hS hb v0 hT pC hc hy he u' (fun i=> by rw [lushMarkov,show αt+d=l+3*d by ring]; exact v i) hx -- tune order
 have he:=vil_est C G _ hh (αt) d c t hS v0 pC hy; let ht:= woodCosts F r hF K C H B' γ 1 M G D g u Vt Wt hW hv he vp (fun i v=>petrol C γ G _ hh (αt) d vp hT pC i v) le_rfl L' vL pu hq -- tune order. petrol does include α β. Name price
 refine ⟨escortFray F r hF K C H M G D g u (vL ▸ Subset.refl _),fun i=>?_,hg⟩
 have hp:= (ht.share i); simp only [Finset.sum_empty,add_zero] at hp; change tallB (roofL F' 1) P.B αt i ≤ γ; rw [←lushMarkov]; rw [show maestro B' ∅ Vt=Vt from (by unfold maestro; rw [Finset.sum_empty]; funext X; simp [style, Cadre.contour])] at hp; exact hp
end realdata
end YM.CF.Vow
#print axioms YM.CF.Vow.vigil

#print axioms YM.CF.Vow.packReservoir
