import YM.CF.Hype.Migrate
import YM.CF.Oath.Chili
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
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
variable {X D Y Z:Support (More n)}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees Lilt Vow
variable {F G: Pax n}{K:Cusp n}{f g: Copy n}
variable (U: Orbit n)
open Oath Haro
-- tract.Separation local.PAZ anchor. k,m.
variable (Tq:Aura n)(WQ:Finset (Rock n)→Prop)
local notation "Pt"=> (Rock n)
local notation "Bv"=> (Support (More n))
abbrev sock_A(o:Site (More n))(k:ℕ): Finset (Rock n):= univ.filter fun j=> posG j ∈ Lattice.halo k {o}
abbrev ball_v(k:ℕ):ℕ:= (k+k+1)^4*(Fintype.card SpinIdx)
lemma term_p (o:Seat n)(k:ℕ) : (sock_A o k).card ≤ ball_v k:=by
 let A:= sock_A o k; let H(i:Pt):= (posG i,i.2); let W:= halo k {o}; have hh: Injective (@node n):= fun x y h=> (assembly n).embed_injective (add_right_cancel (show _ + (1:Site (More n))=_+_ from h)); -- syntax
 have hx : Injective H:=by rintro ⟨u,v⟩ ⟨f,g⟩ t; obtain ⟨p,q⟩:= Prod.mk.inj t; exact Prod.ext (hh p) q
 have hU:A.image H⊆ W ×ˢ (univ: Finset SpinIdx):= image_subset_iff.mpr fun i v=> mem_product.mpr ⟨(mem_filter.mp v).2,mem_univ _⟩
 apply le_trans (show A.card≤ (W ×ˢ (univ: Finset SpinIdx)).card from ?_); · rw [card_product, card_univ]; exact Nat.mul_le_mul_right _ ((Corona.halo_size {o} k).trans_eq (by simp))
 rw [← card_image_of_injective A hx]; exact card_le_card hU
-- Payroll tensor.Art Bind E.N certification.M.
variable {ι τ:Type*}[DecidableEq ι][Fintype ι][Fintype τ][DecidableEq τ]
variable (C_:ι→Finset τ) (o:ι→Seat n)(Dκ:Finset (ι×τ× (Prism.Rock n) × (Prism.Rock n)))
variable (dC:∀ y∈Dκ,y.2.1∈C_ y.1)(qP:∀ y∈Dκ,y.2.2∈ ((sock_A (o y.1) k)×ˢ(sock_A (o y.1) k)))(Aq:ι→τ→ℝ)(h_:∀ i,∀ j∈ C_ i,0 ≤ Aq i j)
include dC h_ qP
lemma rim_W(x:Seat n): ∑ i∈Dκ with o i.1=x,Aq i.1 i.2.1 ≤ (ball_v k:ℝ)^2*(∑ i∈univ with o i=x, ∑ j∈ C_ i,Aq i j):=by
 let X:= sock_A x k; let Z:= X×ˢ X; let V:= univ.filter (fun i=>o i=x); let J(i):= C_ i ×ˢ Z
 let W:= univ.filter fun i:ι×τ× (Prism.Rock n) × (Prism.Rock n)=> i.1∈ V∧ i.2∈J i.1
 have hMem(i:ι×τ× (Prism.Rock n) × (Prism.Rock n)): (i∈W) ↔ (i.1∈V∧ i.2∈J i.1):=by unfold W; rw [mem_filter,and_iff_right (mem_univ _)]
 let K:= Dκ.filter fun i=>o i.1=x; have hh: K⊆ W:= by
    intro i v; obtain ⟨u,l⟩:=mem_filter.mp (show i∈ K from v)
    apply (hMem i).mpr; refine ⟨?_,?_⟩; · unfold V; exact mem_filter.mpr ⟨mem_univ _,l⟩
    unfold J Z X; exact mem_product.mpr ⟨dC i u, l ▸ qP i u⟩ -- tune rw inside x.
 apply (sum_le_sum_of_subset_of_nonneg (f:=fun j=>Aq j.1 j.2.1) hh (fun i v _=> h_ _ _ (show i.2.1∈ C_ i.1 from (mem_product.mp (show i.2∈ J i.1 from ((hMem i).mp v).2)).1))).trans; rw [show (ball_v k:ℝ)^2*_ =_ from (Finset.mul_sum ..)] -- tune
 rw [←sum_fiberwise_of_maps_to (g:=Prod.fst) (t:=V) (fun i v=>((hMem i).mp v).1)]
 refine sum_le_sum fun i v=>?_
 let g(j:τ× (Prism.Rock n) × (Prism.Rock n)):= (i,j); have hz:(W.filter (fun t=>t.fst=i))=(J i).image g:=by
    ext ⟨l,t⟩; unfold W; simp only [mem_filter,mem_univ,true_and,mem_image,g,Prod.mk.injEq]; constructor; · rintro ⟨⟨u,q⟩,rfl⟩; exact ⟨t,q,rfl,rfl⟩
    rintro ⟨p,h,rfl,rfl⟩; exact ⟨⟨v,h⟩,rfl⟩
 have hg:Injective g:=fun a b t=>Prod.mk.inj t|>.2
 rw [hz,sum_image (fun i _ j _ v=>hg v),show (J i)=(C_ i)×ˢ Z from rfl, sum_product,mul_sum]; refine sum_le_sum fun j t=> ?_; dsimp only [g]; rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (h_ i j t); change (Z.card:ℝ)≤_; rw [show Z.card=X.card^2 from (by unfold Z; rw [card_product,sq]), Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (term_p (n:=n) x k)) _
end YM.CF.Larch
