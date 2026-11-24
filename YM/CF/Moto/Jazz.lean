import YM.CF.Moto.Wage
import YM.CF.Moto.Slate
import YM.CF.Oath.Snow
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
open Nor
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> LeanV (Single Kx)
open Hove Oath
local notation "QΦ"=> Rock Kx
variable (Pp: Op (Single (mid N B)))(U':InkD (mid N B))(o:Site (mid N B))(p q:Rock (mid N B))
variable (Xp:BudgetPoint)(u:v>0)(h:ℕ)
local notation "VΦ"=> Φrap (mid N B) o (10*h)
local notation "yΦ"=> (VΦ).val.2
variable (d:ℝ)(w:Fit o Xp.power h d Pp)
local notation "qG"=> node o
local notation "Ξ"=> radiusB x
variable (K₀:ℕ)(Ω:Gala Xp.power k K₀ x 3)(vP:16*h≤ K₀*(1+radiusB x))
local notation "pLine"=> (Feu.lineP Xp qG yΦ (radiusB x))
local notation "QL"=> boxM Pp p q
local notation "T_"=> manifest k Pp p q
-- tariff. incentive actually P.term∥·∥ = h². choose calibr scale 
local notation "Λ"=> VΦ
local notation "SΦ"=> (Λ).val.2
variable (Lh:ℕ) (hv:10*h ≤ Lh*radiusB x)(hu:1 ≤ radiusB x)(qX:Xp.threshold=temp x)(qK:Xp.order=k)(σ:ℝ)
abbrev deck_K(k n L:ℕ):= composeCost k ((k.factorial:ℝ)*1) ((1+(((L+L+1:ℕ)^4:ℕ):ℝ))^n)
open Bake Vow Lilt
local notation "A"=> ∑ i:QΦ,∑ j:QΦ, manifest k Pp i j
local notation "Tq"=> Scree.tariff Xp (node o) σ
-- Sum reexpress. H
local notation "H"=> stakeH k * σ^2
local notation "Ww"=> Hove.paid_M o Pp Xp.power
local notation "Y0"=> yΦ
local notation "Hq"=> Haro.amt Xp.power qG
private lemma heave: joinV Tq (manifest k Pp p q)=(stakeH k *σ^2)*(Hq p q*Oath.bow Pp p q):=by
 let t:=Tq; let G:= stakeH k * σ^2; let E:=Hq
 have hx: joinV t (manifest k Pp p q)=G*(E p q * Oath.bow Pp p q):=by
    let Vu:=γD k * Oath.bow Pp p q; have h(i j:SU.Slot):joinV t (Pi.single (Haro.tray (p,i) (q,j)) Vu)= E p q* σ^2*Vu:=by
        unfold joinV; simp_rw [Pi.single_apply,mul_ite,mul_zero]; rw [sum_ite_eq']; unfold t; rw [if_pos (mem_univ _), show Tq _= _ from Haro.rope Xp.power (node o) p q i j σ Xp rfl]
    unfold manifest; simp_rw [joinVsum]; trans ∑ _ : SU.Slot,∑ _ : SU.Slot,E p q*σ^2* Vu; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>h i j; simp only [sum_const,card_univ,nsmul_eq_mul]; unfold G stakeH flavor Vu; ring
 exact hx
private abbrev κz(p:QΦ):= (1+(separation (node o) (posG p):ℝ))^Xp.power
local notation "W₀"=> κz o Xp
private lemma stage_p: (∑ p:QΦ,∑ q:QΦ,(W₀ p+W₀ q)*Oath.bow Pp p q)= Ww:=by
 let W:= W₀
 unfold Hove.paid_M Tap.paidX; conv_rhs=> rw [Fintype.sum_prod_type]
 let R:=Single (mid N B); let F(i j:R):=(W i.1+W j.1)*‖Pp i j‖
 change _= ∑ i:R, ∑ j:R,F i j
 conv_rhs=> rw [Fintype.sum_prod_type]; arg 2; ext; arg 2; ext; rw [Fintype.sum_prod_type]
 refine sum_congr rfl fun i _=>?_ ; unfold Oath.bow; simp_rw [Finset.mul_sum]; rw [sum_comm (s:=(univ:Finset QΦ)) (t:=(univ:Finset SU.Slot))]
include w
lemma tune_V : joinV (Scree.tariff Xp (node o) σ) (∑ i:QΦ,∑ j:QΦ, manifest k Pp i j)≤ stakeH k * σ^2 * d:=by
 let t:= Tq; let G:= stakeH k *σ^2; have he:0 ≤ G:= by unfold G stakeH flavor γD; have hv:=wheels_p (n:=k); have ht:=Haro.p0; positivity
 let W(p:QΦ):= (1+(separation (node o) (posG p):ℝ))^Xp.power
 let E(p q:QΦ):ℝ:= (1+(max (separation (node o) (posG p)) (separation (node o) (posG q)):ℕ))^Xp.power -- cast tune
 have hz(p q): E p q≤ W p+ W q:=by
    have hk(i):0 ≤ W i:= by unfold W; positivity
    rcases le_total (separation (node o) (posG p)) (separation (node o) (posG q)) with h|h <;> unfold E
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (hk _)
    rw [max_eq_left h]; exact le_add_of_nonneg_right (hk _)
 have hx (i j:QΦ):joinV t (manifest k Pp i j) = G*(E i j * Oath.bow Pp i j):= heave Pp o i j Xp σ -- ordering?
 let Ck(p q:QΦ):= (W p+W q)*Oath.bow Pp p q; change joinV t _ ≤ _
 have hp(i j:QΦ):E i j*Oath.bow Pp i j≤ Ck i j:= mul_le_mul_of_nonneg_right (hz i j) (by unfold Oath.bow; positivity)
 have ht: (∑ i:QΦ,∑ j:QΦ,Ck i j) = Ww:= stage_p Pp o Xp
 have hu: (∑ i:QΦ, ∑ j:QΦ,E i j* Oath.bow Pp i j) ≤ d:=(sum_le_sum (fun i (_:i∈(univ:Finset QΦ))=> sum_le_sum (fun j (_:j∈(univ:Finset QΦ))=>hp i j))).trans (ht.le.trans w.1)
 let Z:=fun i j:QΦ=> E i j*Oath.bow Pp i j; change joinV t _≤ G*d; refine le_trans ?_ (mul_le_mul_of_nonneg_left hu he); change joinV t (∑ p:QΦ,∑ q:QΦ,manifest k Pp p q) ≤ G*(∑ i:QΦ,∑ j:QΦ,Z i j); rw [mul_sum,joinVsum]; apply sum_le_sum; intro i _; rw [mul_sum,joinVsum]; exact sum_le_sum fun j _=>(hx i j).le
include Ω vP hv hu qX qK
lemma pose_K: PressB Xp Λ (pay_Y Pp) σ (deck_K k Xp.power Lh*(stakeH k*σ^2*d)):=by
 let S:=Y0; let p:= pay_Y Pp; have he:= ħ_S Pp o Xp h d w (by omega)
 let M:= deck_K k Xp.power Lh; let V:= A; let A' :=fun i=>M* V i
 have hm:0≤ M:=by unfold M deck_K composeCost; positivity
 have hO(U:Pane Kx):Woody k (fun v:tangD Kx =>(pay_Y Pp (Vmove x U (pLine v))).val) 0 V:=by
    apply (Woody.sumV (S:=(univ:Finset QΦ)) (fun i _=> Woody.sumV (S:=(univ:Finset QΦ)) fun j _=> hoop_P Pp o i j Xp h d w K₀ Ω vP U)).germ; filter_upwards with v; simp only [Finset.sum_apply]; rfl
 refine ⟨fun i j p=>Subtype.ext (he.warm _ _ p),fun i=> he.tax _,(padW _ _ he).measurable,fun U g=>Subtype.ext (he.rotor g U).symm,A',fun i=>mul_nonneg hm ((hO 1).p i),fun U f i=>?_ ,?_ ⟩
 · let W(U:Pane Kx):= crumb (p U).val i; have hp:= Feu.socks Xp _ Y0 (radiusB x) (VΦ).property W qX U (by simpa [Rue.litres] using f) (fun U V _ _ q=> congrArg (fun z=>crumb z i) (he.warm _ _ q)) (qK.symm ▸ (hO U).haveP i); have h':0 ≤ V i:=(hO 1).p i
   have ht: coverNumber (radiusB x) S ≤ (Lh+Lh+1)^4:=by exact (Corona.cover_mono (Corona.halo_mono (X:={node o}) hv (Subset.refl _)) _).trans (Corona.tile _ _ _ hu) -- tune
   refine Prism.high hp ?_; unfold A' M deck_K Feu.brim composeCost; rw [qK]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr ht) _) _) _) _) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (h':0≤V i)))); exact Eq.le (by ring) -- tune
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (tune_V Pp o Xp h d w σ) hm); unfold joinV; rw [mul_sum]; exact sum_le_sum (fun i _=>(mul_left_comm _ M _).le)
end YM.CF.Moto
