import YM.CF.Vow.Year
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
variable (V:Orbit n) (X:Aura n)
abbrev lordD (x:Force n): Aura n:=⟨x.val.1.val.2,⟨_,x.val.1.property⟩⟩
abbrev extraD (x:Force n): Support (More n):=x.val.2
abbrev bassH (x: Aura n) : ℝ := (x.val.card:ℝ)⁻¹
def budgetR (K:Cusp n): ForceBudget n:=fun x=> bassH (lordD x) • K (lordD x) (extraD x)
abbrev motV (i:Aura n)(U:Support (More n)): Finset (Force n):= univ.filter fun j=>lordD j=i∧extraD j=U
variable(x: Support (More n))
lemma countV (u:D∈fullD X): (motV X D).card=X.val.card:=by
 let L:=motV X D; let f (i:Force n):= i.val.1.val.1
 have ht:Set.InjOn f L:=fun a h b v i=> by
    obtain ⟨p,q⟩:=(mem_filter.mp h).2; obtain ⟨y,w⟩:= (mem_filter.mp v).2
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext i (congrArg Subtype.val (p.trans y.symm)))) (q.trans w.symm)) -- tune order projections
 have hp: L.image f=X.val:=by
    obtain ⟨a,t⟩:=(mem_filter.mp u).2; ext j; constructor; rintro p; obtain ⟨i,v,rfl⟩:= mem_image.mp p; rw [←(mem_filter.mp v).2.1]; exact i.val.1.property
    intro p'; let i:Force n:=⟨(⟨(j,X.val),p'⟩,D),a,t⟩; exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,Subtype.ext rfl,rfl⟩,rfl⟩
 exact (card_image_of_injOn ht).symm.trans (congrArg Finset.card hp)
variable {K:Cusp n} {C: blazeK n} (p:ArmsK P K C h) (x':Force n)
lemma bassT :0≤ bassH X:=by unfold bassH; positivity
abbrev rentH (P:BudgetPoint)(C:blazeK n)(x:Force n):ℝ:= fareX P.B P (lordD x).val*(bassH (lordD x)*C (lordD x) (extraD x))
include p
lemma hardy(t:0≤h): ForceB P x' (budgetR K x') h (rentH P C x'):=by
 obtain ⟨y,v⟩:= x'.property; let x:=lordD x'; let g:=p.price x _ y v; let w:=p.claim x _ y v; have hp:=g.rum (bassH x); rw [Real.norm_of_nonneg (bassT x)] at hp; apply hp.preserves _ t P.B
 constructor
 · intro b; rw [show K _ _=_ from w.readV b]; exact smul_zero _
 exact fun i z=> w.litK i fun l=> z (by simp [l]) -- tune
lemma scales(t:0 ≤h)(k:Seat n)(a:ℝ)(hw:0 < a) : (∑ i:Force n, if k∈ i.val.1.val.2 then P.mass i.val.1.val.2 (rentH P C i) else 0) ≤ Nor.reserveT P.power P.order P.B a * tallB (hymn C) P.B (P.supportExponent+a) k:=by
 let KQ(i: Force n):=rentH P C i; let TV (i:Aura n):=∑ y: Force n with lordD y=i,P.mass y.val.1.val.2 (KQ y); let R:=Nor.reserveT P.power P.order P.B a
 have hp(X:Aura n)(D: Support (More n))(i: Force n)(v: i∈motV X D):KQ i=fareX P.B P X.val*(bassH X*C X D):=by obtain ⟨a,t⟩:= (mem_filter.mp v).2; unfold KQ rentH; rw [a,t]
 have hr(X:Aura n)(D: Support (More n))(v:D∈ fullD X):(∑ i∈motV X D,P.mass i.val.1.val.2 (KQ i)) ≤ R*(C X D*currency P.B (P.supportExponent+a) X.val):=by
    rw [sum_congr rfl (fun j u=> show P.mass j.val.1.val.2 (KQ j)=P.mass X.val (fareX P.B P X.val*(bassH X*C X D)) from (by rw [hp _ _ j u,(show j.val.1.val.2 = X.val from congrArg Subtype.val (mem_filter.mp u).2.1)])),sum_const, countV X v,nsmul_eq_mul]
    have hx: (X.val.card:ℝ)≠0:=by exact_mod_cast (card_pos.mpr X.property).ne'
    rw [show (X.val.card:ℝ)*P.mass X.val _= Trees.currency P.B P.supportExponent X.val* C X D*fareX P.B P X.val from (by unfold BudgetPoint.mass bassH Trees.currency; field_simp <;> ring)] -- tune
    apply le_trans (mul_le_mul_of_nonneg_left (Nor.coinPay P X.val a hw) (mul_nonneg (Real.exp_pos _).le ((p.price X _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2).wage t))); unfold R Trees.currency; rw [add_mul,Real.exp_add]; exact le_of_eq (by ring)
 have hv(X:Aura n): TV X ≤ R * (hymn C X * currency P.B (P.supportExponent+a) X.val):=by
    unfold TV hymn; rw [←sum_fiberwise_of_maps_to (s:=univ.filter (lordD ·=X)) (g:=extraD) (t:=fullD X) ?_,sum_mul,Finset.mul_sum]; swap; · intro i h; rw [←(mem_filter.mp h).2]; exact mem_filter.mpr ⟨mem_univ _,i.property⟩ -- tune h implicit
    refine sum_le_sum fun i g=>?_ ; rw [filter_filter]; exact hr X i g
 rw [←sum_filter, ←sum_fiberwise_of_maps_to (t:= (univ.filter fun i:Aura n=> k∈i.val)) (g:=lordD) ?_]; swap; · intro i p; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2⟩
 unfold tallB; rw [mul_sum]; refine sum_le_sum fun i p=>?_ ; apply le_trans _ (hv i); apply le_of_eq; unfold TV; apply sum_congr _ (fun _ _=>rfl); ext j; simp only [mem_filter, mem_univ, true_and,and_iff_right_iff_imp]; intro g; change k∈ (lordD j).val; rw [g]; exact (mem_filter.mp p).2 -- tunes co lift
end YM.CF.Vow
