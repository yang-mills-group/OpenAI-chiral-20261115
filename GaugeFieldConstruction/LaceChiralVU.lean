import GaugeFieldConstruction.FanaticLeftVU
set_option synthInstance.maxSize 4800
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice.curvΝ
open Phys Calibration Cauchy Row Wick Raster Gap Function MeasureTheory Set Filter Mirror Flux.One
open Floor Flavor Finset
open Matter (Generation Slot Sheet)
open YM.Maxwell (normal Green normal_pos)
open scoped BigOperators Topology Classical
namespace LeftVU
local notation "K" => (32*(normal:ℂ))
local notation "L" => (4*(normal:ℂ))
local notation "A" => (prism 0 apex ((2:ℝ) • apex))
-- all charges in true UV directions of Loft.Span. Build slot normal
open Yacht
local instance igPLeftVU (d:Floor) : AddCommGroup (UF d):= @Submodule.addCommGroup ℂ (J Row.f) _ _ _ (SF d)
local instance ixPLeftVU (d:Floor) : AddCommGroup (UV d):= inferInstanceAs (AddCommGroup (Prod ℂ _))
abbrev AccountCh (k:Axis)(s:Sheet)(l:Generation):=∑ a:Spin,∑ b:Spin,Hij k a b • LedgerL1 s l a b
private lemma joinVou (s:Sheet)(l:Generation)(a b:Spin):LedgerL1 s l a b= (LinearMap.inr ℂ ℂ _ ∘ₗ LinearMap.inr ℂ _ _ ∘ₗ LinearMap.inl ℂ _ _) (sD (l,s) (l+1,s) (times' (C a 0) (C b 0))):=by unfold sD; rw [straps]; rfl
private def ΩCoastL : J Spair→ₗ[ℂ]Book:=LinearMap.inr ℂ ℂ _ ∘ₗ LinearMap.inr ℂ _ _ ∘ₗ LinearMap.inl ℂ _ _
private lemma joinΩVou (s:Sheet)(l:Generation)(a b:Spin):LedgerL1 s l a b= ΩCoastL (sD (l,s) (l+1,s) (times' (C a 0) (C b 0))):= joinVou s l a b
private lemma χWise (k:Axis)(s:Sheet)(l:Generation):AccountCh k s l=ΩCoastL (sD (l,s) (l+1,s) (Row.B k)):=by
 unfold AccountCh Row.B; simp only [map_sum,map_smul,joinΩVou]
private lemma Loom_alpha (m: Matter.FlavorIndex)(x y:Slot): Phys.alpha m x y = if x.2=y.2∧(tagged x.2,x.1,y.1)=m then 1 else 0:=by
 rw[show Phys.alpha m x y=_ from Flavor.wear (Pi.single m 1) x y,ite_and]; split_ifs <;> first|rfl|(simp_all [Pi.single_apply]) -- tune
private lemma Tapeα_leftVu(i: Matter.FlavorIndex)(v:J Row.f): tiap i v=∑ s:Sheet, if tagged s=i.1 then sD (i.2.1,s) (i.2.2,s) v else 0:=by
 rcases i with ⟨x,y,z⟩
 simp only [tiap,LinearMap.sum_apply,LinearMap.smul_apply,Loom_alpha, Matter.Slot,CF.SU.Slot,Fintype.sum_prod_type,ite_smul,one_smul,zero_smul]
 have ho (s:Prop)[Decidable s](l:Module.End ℂ (J f)): (if s then l else 0) v=(if s then l v else 0):=by split_ifs <;> rfl
 have hu (s:Prop)[Decidable s](l:J f→ₗ[ℂ] J Spair): (if s then l else 0) v=(if s then l v else 0):=by split_ifs <;> rfl
 rw[Finset.sum_comm]
 refine sum_congr rfl (fun i u=>?_)
 by_cases g:tagged i=x
 · simp [hu,ite_and,g,sum_ite_irrel]
 simp [hu,g]
private lemma Pilotsα(i:Axis)(k:ClanZN): dress (shells three (FamilyZN i k))= ΩCoastL (tiap (transitionΦN k) (Row.B i)):=by
 refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
 · exact Calibration.RawBank.cold _ _ rfl
 · rw [dressF]; unfold FamilyZN; rw[show ∀ (B:J Spair),(ΩCoastL B).2.2.1=B from fun _=>rfl]
   unfold graph_f; rw [LinearMap.sum_apply,Finset.sum_eq_single_of_mem (transitionΦN k) (mem_univ _)]
   · simp only [LinearMap.comp_apply,shells,LinearMap.prodMap_apply,LinearMap.proj_apply,mv_at,Pi.single_eq_same,Submodule.subtype_apply,CauchyAxisN]
   intro b hb h; simp only [LinearMap.comp_apply,shells,LinearMap.prodMap_apply,LinearMap.proj_apply,mv_at,Pi.single_eq_of_ne h,map_zero]
 exact Calibration.RawBank.cand _ _ rfl -- tune
lemma Treadα(i:Axis)(k:ClanZN): dress (shells three (FamilyZN i k))=∑ s∈ univ.filter (fun s:Sheet=>tagged s=k.2),AccountCh i s k.1:=by
 rw [Pilotsα,Tapeα_leftVu,map_sum,sum_filter]; refine sum_congr rfl fun s _=>?_ ; split_ifs with h p <;> first|exact (χWise i s k.1).symm|exact map_zero _|exact False.elim (h p)|exact False.elim (p h)
abbrev indL1 (c:Bool):Finset Sheet:=univ.filter fun s=>tagged s=c
lemma countsα(b:Bool):(indL1 b).card=(if b then 10 else 5):=by cases b <;> decide
-- tune
#print axioms Treadα
end LeftVU
end YM.GaugeFieldConstruction.Invoice.curvΝ
end
