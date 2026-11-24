import YM.CF.Sour.Cluck
import YM.CF.Fief.Lucid
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inherited
import YM.CF.Sour.Lead
import YM.CF.Sour.Park
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
-- arena costs P.B; halo.B against Loom.k; permit atOne.
abbrev widthK (n:Side)(k:ℕ)(Y:Aura n):ℝ:= coverNumber k Y.val -- open namespace
abbrev spanV(k:ℕ):ℝ:=((k+k+1)^4:ℕ)
lemma vigor(n:Side)(k:ℕ):Cadre.Tour (widthK n k) (spanV k):=by
 refine ⟨fun i=>by unfold widthK; exact_mod_cast (show 1 ≤ coverNumber k i.val from (Push.AbsoluteSums.Animals.price_pos ..).mpr i.property),fun i=>?_,fun X Y G p=>?_⟩
 · unfold widthK spanV; rw [mul_comm]; exact_mod_cast Corona.pays ..
 obtain ⟨l,u,v⟩:=(drum_p ..).mp p
 suffices w:coverNumber k X.val≤ coverNumber k Y.val+∑ i∈G, coverNumber k i.val by unfold widthK; exact_mod_cast w
 rw [v]; clear l v p; induction G using Finset.induction_on with
 |empty=> simp [Palot.robe]
 |insert i G h ih=>
    have ht:= ih (fun j l=>u j (mem_insert_of_mem l)); obtain ⟨a,p',q'⟩:= Finset.not_disjoint_iff.mp (u i (mem_insert_self ..)); have he:= Corona.meets_sum (mem_union_left (robe G) p') q' k; change coverNumber k (_∪_)≤ _ at he; rw [show robe (insert i G)= i.val∪ robe G from biUnion_insert ..,union_comm _ (robe G), ←union_assoc, sum_insert h]; omega
variable (H:Op (Single n)→ FC (Dwell n))(Z:Single n→Single n→FC (Dwell n))(h:ℝ)(f: Glyph H Z h){δ a v u e:ℝ}{μ:Support (More n)→ Toll (Single n)}{X:Aura n} -- implicit issue change
variable (F:Support (More n)→Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t:∀ S, Suite (badge _) (bail n δ) (bail n δ) S (μ S) (F S))
local notation "B"=>P.B
abbrev αW(k:ℕ)(x:Aura n):=univ.filter fun Z:Support (More n)=> x.val= halo k Z
abbrev noteR (μ: Support (More n)→Toll (Single n))(Y:Aura n):ℝ:=∑ i∈αW P.B Y,Glyph.vest P h (μ i)
abbrev actsF(k:ℕ)(Y:Aura n):=∑ i∈αW k Y,Glyph.cure H p g (F i)
def aimV (k:ℕ)(a L:ℝ):ℝ:=((k+k+1)^4:ℕ) *(Real.exp (L*Fief.tileN 1)*(∑' i:ℕ, Real.exp (-a/2*i)*(Tenant.quota*((i:ℝ)+1)^4))) -- tune precedence
variable {c L t₀:ℝ}(M:Ledger e μ c)(bX: 0<e)(R:0 ≤ L)(w: 2*L*Fief.tileN 1≤ e/2/2*P.B)
open ConnectedActivityE6.Raw
abbrev tact(s:ℝ)(k:ℕ)(X: VX):ℝ:=Real.exp (s*widthK n k X)
include M bX t R w
lemma expF (x:Seat n): Cadre.nook (@noteR _ P h μ *loom_v L 0 (widthK n P.B) 0) x≤ (P.order+1:ℝ)*h^2*aimV P.B e L*c:=by
 let A:=atOne (More n); let V'(X:Support (More n)):=ledgerV (μ X); have hv:0 ≤V':=fun x=>sum_nonneg fun i _=>sum_nonneg fun j _=> (t x).nonn i j
 have hp(Z:Support (More n))(h:V' Z≠0):Branch.Grove (terr _) Z:=by obtain ⟨i,g,p⟩:=exists_ne_zero_of_sum_ne_zero h; obtain ⟨j,l,s⟩:=exists_ne_zero_of_sum_ne_zero p; exact (((t Z).expo i j).triggered s).1
 have hz:0 ≤ Tenant.quota:= le_trans (show (0:ℝ)≤16 by norm_num) quota_bound
 let Q:ℝ:= (∑' i:ℕ, Real.exp (-e/2*i)*(Tenant.quota*((i:ℝ)+1)^4))*c; have hQ:0 ≤ Q:=mul_nonneg (tsum_nonneg (fun i=> by positivity)) M.posP
 let s:=univ.filter fun i:Support (More n)=>i.Nonempty
 have hμ:0 < e/2:=by positivity
 have hα:0<P.B:=P.B_pos
 have he(b:Support (More n)): b.image A.parent=b:=by rw [show A.parent=id from funext fun x=>parent_one x, image_id]
 have ht:= Fief.venture A P.B 1 hα _ L hμ R (by norm_num [A,atOne,scaleOne]; exact w) hv hp s 0 (fun i _=>Nat.zero_le _) (fun i=> Branch.tall (P:=F) (fun j=> (t j).toTicket) M bX (meterQ ..) hz i) hQ x -- tune arguments
 simp_rw [he, one_mul] at ht
 let C0:ℝ:= (P.order+1:ℝ)*h^2; let V(Y:Aura n)(i: Support (More n)):= C0*(V' i*Real.exp (L*coverNumber P.B Y.val)); let A':=s.filter fun Z=> x∈halo P.B Z; let B':=Cadre.spark x
 have hx : Cadre.nook (@noteR _ P h μ *loom_v L 0 (widthK n P.B) 0) x=C0*∑ i∈A',V' i*Real.exp (L*coverNumber P.B (halo P.B i)):=by
    trans ∑ i∈B',∑ j∈αW P.B i,V i j
    · apply sum_congr rfl; intro i _; unfold noteR -- tune
      rw [Pi.mul_apply,sum_mul]; refine sum_congr rfl fun j _=>?_ ; unfold V Glyph.vest V' C0 loom_v widthK; rw [zero_mul,sub_zero]; ring
    rw [mul_sum,sum_sigma']; refine sum_bij (fun i _=>i.2) ?_ ?_ ?_ ?_
    · rintro ⟨i,j⟩ u; obtain ⟨p,t⟩:=mem_sigma.mp u; have he:= (mem_filter.mp t).2; have hx: x∈halo P.B j:=he ▸ (mem_filter.mp p).2; obtain ⟨i,s,v⟩:= halo_spec.mp hx; exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,i,s⟩,hx⟩
    · rintro ⟨i,j⟩ p ⟨x,y⟩ q rfl; rw [show i=x from Subtype.ext ((show i.val=halo P.B j from (mem_filter.mp (mem_sigma.mp p).2).2).trans (show x.val=halo P.B j from (mem_filter.mp (mem_sigma.mp q).2).2).symm)];
    · intro i h; have hx: x∈halo P.B i:= (mem_filter.mp h).2; exact ⟨⟨⟨halo _ _,x,hx⟩,i⟩,mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,rfl⟩
    intro i h; unfold V; rw [show i.1.val= _ from (mem_filter.mp (mem_sigma.mp h).2).2] -- V unfold
 rw [hx]; apply (mul_le_mul_of_nonneg_left ht (by unfold C0; positivity)).trans_eq; rw [show A.count.val=1 from rfl,one_pow,mul_one]; unfold C0 aimV Newt.tollE; simp only [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul,mul_assoc]

end YM.CF.Sour
