import Gingham.Ruff.Thimble
import Gingham.Ruff.Envelope
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry


variable {N:Side}
def wisp (p:BudgetPoint):Finset Cover:=ore (p.B+8) 0
def flash(p:BudgetPoint):Set PairsC:={x|pingC p.B 0 p x.1}

lemma hoop_zero(b:ℕ):
 region (ore b 0) N= hoop 0 b:=by
 rw [ore_same, map_zero,hoop,bouton, ←Ratio.root_embed,map_zero]
 
lemma pass_ore(p:BudgetPoint){j:Face ℤ}(y:¬Disjoint (toe_l j) (ore p.B 0)): toe_l j ⊆ wisp p:=by
    rw [wisp,←show p.B+4+4=p.B+8 from rfl]
    exact toe_up _ 0 j (toe_back p.B 0 j y)

lemma passes (p:BudgetPoint)(S:Finset Cover)(v:wisp p⊆S)(h:Hosp S N)(x:PairsC):
   replant S N x∈zone 0 p ↔ x∈flash p:=by
 let X:=graft S N x.1
 change pingS p.threshold (hoop 0 p.B) X ↔ pingC p.B 0 p x.1
 rw [hoop, bouton,←Ratio.root_embed,map_zero,←map_zero (wrap (More N)),←ping_lift]
 have t:=tacked S N h x.1
 have g (j:Face ℤ)(y:¬Disjoint (toe_l j) (ore p.B 0)): faceValue (onC N X) j=faceValue x.1 j:=by
    apply travel_local
    have ht:=Subset.trans (pass_ore p y) v
    exact fun i a b=>t _ (ht (List.mem_toFinset.mpr a)) (ht (List.mem_toFinset.mpr b))
 exact ⟨fun k j y=>by rw [←g j y];exact k j y, fun k j y=>by rw [g j y];exact k j y⟩

lemma pass(p:BudgetPoint)(h: Hosp (wisp p) N)(x:PairsC):
 replant (wisp p) N x∈zone 0 p ↔ x∈flash p:=passes p _ (Subset.refl _) h x

lemma maskalo(p:BudgetPoint): beagle 0 p ⊆ region (wisp p) N :=by
 rw [wisp,hoop_zero]; exact Corona.halo_mono (by omega) le_rfl

lemma readalo(p:BudgetPoint): belle 0 p.B ⊆ region (wisp p) N:=by
 rw [wisp,hoop_zero]; exact Corona.halo_mono (by omega) le_rfl

variable (S:Finset Cover)
def aliquot(S:Finset Cover):ℝ:= S.card * (Fintype.card Axis:ℝ)
lemma ali_nonneg : 0≤aliquot S:=by unfold aliquot; positivity
abbrev TabL (S:Finset Cover):= (↥S × Axis) → Bool →Twig

def porcelain (S:Finset Cover) (x:PairsC): TabL S:=
 fun i b=> if b then Tulip.brand (x.1 (i.1.val,i.2)) else star (Tulip.brand (x.1 (i.1.val,i.2)))
lemma TeaSet(x:PairsC): ‖porcelain S x‖ ≤1:=by
 refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=>(pi_norm_le_iff_of_nonneg zero_le_one).2 fun b=>?_
 unfold porcelain;split
 · exact (brand_norm _).le
 rw [norm_star,brand_norm]

lemma aliquots (h:Hosp S N) (x y:PairsC):
     fare (region S N) (profile (replant S N x).1) (profile (replant S N y).1)
       ≤ aliquot S * ‖porcelain S x-porcelain S y‖:=by
 let D:=region S N
 have v:leaks D ⊆ D ×ˢ (univ:Finset Axis):=
     fun i p=>mem_product.mpr ⟨(mem_filter.mp p).2.1,mem_univ _⟩
 unfold fare
 refine le_trans (sum_le_sum_of_subset_of_nonneg v (fun _ _ _=>norm_nonneg _)) ?_
 refine (sum_le_card_nsmul _ _ ‖porcelain S x-porcelain S y‖ ?_).trans ?_
 swap
 · rw [nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   rw [aliquot,card_product,card_univ]
   have hm:D.card≤ S.card:=card_image_le
   norm_cast
   gcongr
 intro i w
 obtain ⟨s,p,r⟩:=mem_image.mp (mem_product.mp w).1
 let a:S:=⟨s,p⟩
 have g(z:PairsC):profile (replant S N z).1 i=porcelain S z (a,i.2):= by
    have e:(replant S N z).1 i=z.1 (s,i.2):=
       (by rw [←Prod.eta i,←r]; exact ((onC_spec N _ (s,i.2)).symm.trans (Satin.tail S N h z.1 (s,i.2) p)))
    funext b;rw [profile,e];rfl
 rw [g,g]
 exact norm_le_pi_norm (porcelain S x-porcelain S y) _

