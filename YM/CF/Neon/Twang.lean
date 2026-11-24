import YM.CF.Neon.Hick
import YM.CF.Neon.Pluto
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
open Py
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
variable {d e η t_aux z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
local notation "Yκ"=> mid P B
local notation "Xκ"=> mid N B
local notation "Ωp"=> RegBudget (mid P B)
local notation "θp"=> (Y.p)
local notation "HF"=> Scree.Hub (mid P B)
local notation "Пρ"=> S.patch.L.val
local notation "Pr"=> Roc (mid P B)
open Taxi Hope
variable (o: Site (mid P B))(E1:RegBudget (mid P B))(OG:RegBudget (mid P B))(X0:Dome)(Aζ:Skate)(Q:ℝ)(h:ℝ)
local notation "Δo"=> Cube.node o
open Mew
-- process real gauge Yearn to K normalization. rooted support wave. Cost short C.P broad Vv post.Sector. 
variable (F:Pilot)(Z:Pluck R){H:Muster G S x d T}{W:GivenX V U}{q q':Chi}
local notation "ζμ"=> radiusB x
local notation "Px"=> (Φrap (mid P B) o 10)
local notation "κ0"=> ((Px,true):Pr)
local notation "Ωκ"=> (hostX (l:=((H.post+90)*radiusB x)) S κ0)
local notation "XP"=> (X.p)
variable {q0:ℝ}(Tp:Ids (mid N B))(Wt:Aura (mid N B)→ Copy (mid N B))(b v0 v':ℝ)(QΦ:Skate)(Pξ:ℂ)
variable (Vκ:ℝ)(Ψ: DayT X.p.order Vκ)(uc:0 ≤ Vκ)
variable (Υ:Gala X.p.power X.p.order 100 x 3)(hμ:10 ≤ X.p.B)(hK:X.p.B=radiusB x)(hk:X.p.threshold=temp x)(he:1 ≤ radiusB x)(hp:20 < (More (mid N B)).val)(hP:3 ≤ (mid N B).val)
-- stencil size cover
variable (o':Site (mid N B))(tζ:S.ratio.parent (Cube.node o)=Cube.node o')
abbrev KX(l:ℕ):ℕ:= (2*(l+190)+1)^4
include tζ
lemma Ξp_cover (t:H.post=l)(v:0 <radiusB x) : coverNumber (radiusB x) (Ωκ).val ≤ KX l:=by
 let K:=Lattice.halo ((l+190)*radiusB x) {node o'}; have hh:coverNumber (radiusB x) K ≤ KX l:=by unfold KX; rw [two_mul]; exact Corona.tile _ _ _ v -- fix
 apply le_trans ?_ hh; apply Corona.cover_mono; intro i p; unfold hostX Eire.pore at p; change _∈ Lattice.halo _ _ at p; obtain ⟨y,ty,k⟩:= halo_spec.mp p
 obtain ⟨z,p,rfl⟩:= mem_image.mp ty; have hz:z∈ Lattice.halo 12 ((Px).val.2):=Yaw.touchK _ p
 obtain ⟨j,t',hb⟩:= halo_spec.mp hz; have hj:j∈Lattice.halo 10 {node o}:= t'; obtain ⟨k',hq,hu⟩:=halo_spec.mp hj; rw [mem_singleton.mp hq] at hu -- orientation? check
 apply halo_spec.mpr; refine ⟨node o', mem_singleton_self _,?_⟩
 have hσ:=separation_triangle (node o) j z; have hx:= Work.E04.parent_separation S.ratio (node o) z; rw [tζ] at hx; apply (separation_triangle _ _ _).trans (le_trans (Nat.add_le_add le_rfl k) ?_); rw [t]; simp only [Nat.add_mul]; omega
-- principal Tend.S mask exact w Cover.D.Note no lifeH zeros output yet. T Palace Loan support
variable (y:Tune.Yearn (Xs:=X) H Tp ((Φrap (mid P B) o 10,true):Roc (mid P B)) h o' Wt b v0 v' Pξ QΦ)(ht: Turf Wt)(hb:0≤ b)(t:H.post=l)(pL:(KX l)^3<S.patch.L.val)(hv:1 ≤ h)
local notation "dΛ"=> ((Real.exp (X.p.supportExponent*(KX l:ℝ))*b)+v')
local notation "A_η"=> (Δv X.p Vκ*(dΛ))
local notation "F_η"=> (Extr_h S.patch.L.val X.p Vκ*(dΛ))
local notation "χt"=> (hostX (l:=((H.post+90)*radiusB x)) S κ0)
local notation "σA"=> Aura (mid N B)
local notation "σh"=> Scree.Hub (mid N B)
include y ht Υ -- fix
include hb t pL hv Ψ uc hμ hK hk he hp hP
lemma twonk_q:∃ G K Tv GΦ GΨ, Ice (S.patch.L.val) o' X.p h (A_η) (F_η) dΛ (coldE X.p Wt) G K Tv (GΦ,GΨ) ∧ ‖GΦ- Pξ • QΦ‖≤ v0+2*v' ∧ ‖GΨ‖*h^2 ≤ (2*peka_H X.p.power)*v':=by
 let A:= univ.filter (fun j:σA=> (χt).val⊆ j.val); obtain ⟨L,hL,v,Pc,Wc⟩:= y.wave; let J(i:σA):= keep_A (H:=H) (κ0,i); let W(i:σA):InkD (mid N B):= fun z=>Wt i (z,Tp); let C (i:σA):=(if i= Ωκ then b else 0)+L i
 let S':=Ωκ; have hz':S'∈ A:= mem_filter.mpr ⟨mem_univ _,Finset.Subset.refl _⟩
 have hp' (i:σA)(p:i∈ A): J i=tonK (H:=H) κ0 i (mem_filter.mp p).2:= dif_pos (mem_filter.mp p).2
 have hs(i)(p:i∈A): (J i).val.2=i.val:=by rw [hp' i p]
 have hf(i:σA)(p:i∈A):PressB XP (J i) (W i) h (C i):= hp' i p ▸ (v i (mem_filter.mp p).2).1
 have hu(i:σA)(p:i∈A):(J i).val.1=node o':=by rw [hp' i p]; exact tζ
 let Xg:= Real.exp (X.p.supportExponent*(KX l:ℝ))*b; have hV: coverNumber X.p.B S'.val≤ KX l:= hK ▸ Ξp_cover o o' tζ t he -- tune
 have hw: (∑ i∈A,X.p.mass (J i).val.2 (C i))≤ Xg+v':=by
    unfold BudgetPoint.mass C; simp_rw [mul_add,sum_add_distrib]; apply add_le_add; swap; · refine le_of_eq_of_le (Finset.sum_congr rfl fun i p=> by rw [hs i p]; rfl) Wc -- lean meta.Q tune
    rw [sum_eq_single_of_mem S' hz',if_pos rfl, hs S' hz']; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hV) X.p.exponent_pos.le)) hb; intro i _ h; rw [if_neg h,mul_zero]
 let GΦ:= Eφ o' X.p A J W Пρ; let GΨ:= Eκ o' X.p A J W Пρ
 let Zp:= hand_W o' XP h A J W C dΛ hf hu hv hw Пρ Vκ Ψ uc Υ hμ hk he hp hP -- tune
 have heq:pump_I XP A J W=coldE XP Wt:=by
    funext i; unfold pump_I coldE; symm; rw [sum_filter,←sum_filter_add_sum_filter_not (s:=univ) (p:=fun j:σA=> (χt).val⊆ j.val)]; rw [sum_eq_zero (s:= univ.filter (fun j:σA=> ¬((χt).val⊆j.val)))]; rw [add_zero]; refine sum_congr rfl fun j p=> ?_; rw [show lagE (J j)=j from Subtype.ext (hs _ p),show Wt j=oV (W j) from funext fun w=> ht _ _ _]; rfl
    intro ℓ p; rw [y.quiet _ (mem_filter.mp p).2]; split; exact rfl; rfl
 let D:=firth X.p S.patch.L.val A J; have hpV:S'∈ D:=by apply mem_filter.mpr; refine ⟨hz',?_⟩; unfold chose; rw [hs _ hz']; exact lt_of_le_of_lt (Nat.pow_le_pow_left hV _) pL
 have hd:D⊆A:=filter_subset ..; have hΛ(i)(p:i∈A): L i≤ X.p.mass i.val (L i):=by rw [← hs _ p]; exact tonne_ge _ _ _ (hL i)
 have hS(s:Finset σA)(p:s⊆A): (∑ i∈s,L i)≤ v':=(sum_le_sum (fun i w=> hΛ _ (p w))).trans ((sum_le_sum_of_subset_of_nonneg p (fun i p _=>mul_nonneg (Real.exp_pos _).le (hL i))).trans Wc)
 refine ⟨_,_,_,GΦ,GΨ,heq ▸ Zp,?_,?_⟩
 · let T (i:σA):= Moto.tooth (node o') X.p (W i)
   let D':= D.erase S'; have hsY:D'⊆ A:= Subset.trans (erase_subset ..) hd; have hc:GΦ=T S'+∑ i∈D', T i:=(add_sum_erase D T hpV).symm
   have hB:0≤ v0+L S':=(norm_nonneg _).trans (Pc (Classical.arbitrary _) (Classical.arbitrary _))
   have hf0:‖T S'-Pξ • QΦ‖≤ v0+ L S':=by
      refine (pi_norm_le_iff_of_nonneg hB).mpr (fun i=>(pi_norm_le_iff_of_nonneg hB).mpr (fun j=>?_)); have ht(i j):= Pc i j; unfold T; rw [←tζ]; exact ht i j
   have hvL(i:σA)(p:i ∈ D'):‖T i‖≤ L i:=by
      have h:= dia X.p _ _ (hf i (hsY p)) (zero_le_one.trans hv); unfold C at h; rw [if_neg (mem_erase.mp p).1,zero_add,hu i (hsY p)] at h; exact (pi_norm_le_iff_of_nonneg (hL i)).mpr fun j=>(pi_norm_le_iff_of_nonneg (hL i)).mpr fun k=> h j k
   rw [hc,add_sub_right_comm]; apply (norm_add_le ..).trans; have hzL: L S' ≤ v':= (hΛ S' hz').trans ((single_le_sum (f:=fun i:σA=> X.p.mass i.val (L i)) (fun i w=>mul_nonneg (Real.exp_pos _).le (hL i)) hz').trans Wc)
   exact (add_le_add (hf0.trans (add_le_add_right hzL v0)) ((norm_sum_le ..).trans ((sum_le_sum hvL).trans (hS _ hsY)))).trans_eq (by ring) -- tune add_le_add_left lean expectation
 let QΨ(i:σA):= jetsL o' (orbitPH (W i 1)); let K0:=2*peka_H X.p.power; have hk0:0≤K0:= by unfold K0 peka_H κP ξP pruneQ; have h:=Hove.mpe true; have h':= Hove.mpe false; positivity
 have hr:GΨ=∑ i∈D,QΨ i:=rfl; rw [hr]; apply le_trans (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (sq_nonneg _)); rw [sum_mul]; apply le_trans ?_ (mul_le_mul_of_nonneg_left (hS D hd) hk0); rw [mul_sum]; apply sum_le_sum; intro i p; rw [mul_comm]; let g:=hd p; refine (κprice (W i) (J i) o' (hu i g) X.p (hf i g) hv (Nat.le_trans (by decide) X.p.power_ge) (v i (mem_filter.mp g).2).2).trans_eq ?_; unfold K0; ring
end YM.CF.Neon
