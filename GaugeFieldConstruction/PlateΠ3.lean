import GaugeFieldConstruction.Pelerine3
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
variable (P:BudgetPoint)
namespace Argos
open Roots.Connect
section clip
variable {I J A E T:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J] -- A E are universes? dues requires Type
variable {B U V:Type} {n:Side}(σ:I→ Seat n) (r: Seat n → J)(pr:Injective r) (b:Bool)(x:Key I)
variable [NormedAddCommGroup A][NormedSpace ℂ A] [CompleteSpace A] [DecidableEq U]
def Reflect3 (t:Key J): Key I:=fun i=> x i * cSignX b (t (r (σ i)))
local notation "ιT"=> Reflect3 σ r b x
-- sign ring involution
def ρ3(b:Bool): ℂ →+* ℂ:=if b then (starRingEnd _) else RingHom.id _
lemma sign3 (w:ℂ):cSignX b w=ρ3 b w:=by cases b<;>rfl
lemma sigh (w:ℂ):ρ3 b (ρ3 b w)=w:=by cases b <;> simp [ρ3] -- tune
-- erase seat
abbrev blank3 (x:Seat n)(z:Key I):Key I:=fun i=>if σ i=x then 0 else z i
variable (i:I)(j:U)
lemma repeatζ (t:Key J)(l:List I): ρ3 b (carR (Reflect3 σ r b x t) l)=ρ3 b (carR x l)* carR t (l.map (r∘σ)):=by
 induction l with
 |nil=>simp [carR]
 |cons a l ih=>
    let p:=ρ3 b; change p (Reflect3 σ r b x t a*carR _ l)=p (x a*carR x l)* (t _ * carR t _) -- is defeq? 
    unfold p; rw[map_mul,ih,Reflect3,sign3]; simp only [map_mul,sigh, Function.comp_apply]; ring
lemma repeatμ (l:List I) (h:ψS σ (i::l)) (z:Key I) :carR z l=carR (blank3 σ (σ i) z) l:=by
 obtain ⟨d,e⟩ := (show σ i ∉ l.map σ ∧ (l.map σ).Nodup from List.nodup_cons.mp h)
 unfold carR; congr 1; apply List.map_congr_left; intro j t; exact (if_neg (fun p=>d (List.mem_map.mpr ⟨j,t,p⟩))).symm
end clip
section
variable {I J A U E:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n:Side}(σ:I→Seat n)(r: Seat n→J)(pr:Injective r)(x:Key I)(b:Bool)
variable [Fintype U][DecidableEq U][AddCommGroup E][Module ℂ E][NormedAddCommGroup A][NormedSpace ℂ A][CompleteSpace A](R:E→+A)(p:∀ s:ℂ,∀ t,R (s • t)=ρ3 b s • R t)
variable (F:G)(j:U)
local notation "κ"=> Reflect3 σ r b x
-- precision: upstream Key mask **ignores same-group coordinates**
include pr p
lemma clipGear (i:U)(F:E)(l:List I)(k:I) : Kin (id:J→J) (fun t=> R (Canz σ E (clipK σ i (k::l) F) (Reflect3 σ r b x t) j)) (fun t=>R (if j=i then ((Reflect3 σ r b x t k)* carR (blank3 σ (σ k) (Reflect3 σ r b x t)) l) • F else 0)):=by
 have hy(t:Key J): Canz σ E (clipK σ i (k::l) F) (κ t) j= if ψS σ (k::l)∧j=i then carR (κ t) (k::l) • F else 0:= can_single σ _ _ _ _ _; simp_rw [hy]; have hm(t:Key J): R ((κ t k* carR (blank3 σ (σ k) (κ t)) l) • F)= (carR t ((r (σ k)):: (l.map (r∘σ)))) • (ρ3 b (x k* carR (blank3 σ (σ k) x) l) • R F):=by
    have hz: blank3 σ (σ k) (κ t)= Reflect3 σ r b (blank3 σ (σ k) x) t:=funext fun i=>by by_cases h:σ i=σ k<;>simp [Reflect3,blank3,h] -- notation in simp issue
    rw [hz,p,map_mul,map_mul,repeatζ]; change _ • _=(t _*carR t _) • _ -- tune
    unfold Reflect3; rw[map_mul,sign3,sigh,mul_smul]; rw [smul_smul, smul_smul] -- tune
    congr 1; ring
 by_cases h:i=j; swap
 · simp only [Ne.symm h,and_false,↓reduceIte,map_zero]; exact Kin.refl id (zeroR _)
 subst j; simp only [and_true,↓reduceIte,hm]; let L:= (r (σ k))::l.map (r ∘σ)
 let V₀:=ρ3 b (x k * carR (blank3 σ (σ k) x) l) • R F; by_cases q:ψS σ (k::l); swap
 · have he:¬ψS id L:=fun h=> q (List.Nodup.of_map r (show ((k::l).map σ |>.map r).Nodup from by change (L.map id).Nodup at h; simpa [L,List.map_map] using h))
   simp only [if_neg q,map_zero]; refine ⟨zeroR _,arc0 _ _,fun s u=> (tip_0 _).trans (noStem (id:J→J) L s he u V₀).symm⟩
 simp_rw [if_pos q]; change Kin id (fun t=> R (carR (κ t) _ • _)) (fun t=> carR t L • V₀)
 rw [show (fun t=> R (carR (κ t) (k::l) • F))=(fun t=> carR t L • V₀) from (funext (fun t=>by change R ((κ t k * carR (κ t) l) • F)=_; rw [repeatμ σ k l q]; exact hm t))]; exact Kin.refl id (arc0 _ _)
lemma canH (V:dues I U→E): Hatch (id:J→J) A univ (fun t=>R (Canz σ E V (Reflect3 σ r b x t) j)):=by
 simp_rw [Canz,map_sum]; apply Hatch.sum; intro i v
 have h:Hatch (id:J→J) A univ (fun t=>R (Mew.pine i (κ t) • V (i,j))):=by
    let L:= Cue I i; let t:= L.map (r ∘ σ)
    have hp:L.Nodup:=sort_nodup ..; have hx:Set.InjOn σ i:=(mem_filter.mp v).2
    have he:Set.InjOn (r ∘ σ) i:=fun a s i₁ b h=>hx s b (pr h)
    let V':=ρ3 b (Mew.pine i x) • R (V (i,j)); let H:=i.image (r ∘ σ); have g(z:Key J): R (Mew.pine i (κ z) • V (i,j))=Mew.pine H z • V':=by
        rw[p]; have e:Mew.pine H z= ∏ j∈i,z (r (σ j)):=by unfold Mew.pine H; rw[prod_image]; rfl; exact he
        have hu:ρ3 b (Mew.pine i (Reflect3 σ r b x z))=ρ3 b (Mew.pine i x)*∏ j∈i,z (r (σ j)):=by
           unfold Reflect3 Mew.pine; simp_rw [map_prod,map_mul,sign3,sigh]; rw [prod_mul_distrib]
        rw[hu,e, mul_comm,mul_smul]
    simp_rw[g]; exact Hatch.mon H ⟨fun _ _ _ _ e=>e,fun _ _=>mem_univ _⟩ V'
 exact h
omit pr p
lemma stemEq {g f:Key J→ A}(hf:Hatch id A univ f)(hg:Hatch id A univ g)(u:Kin (id:J→J) f g):f=g:=by
 apply Eq.trans (Hatch.cost id _ hf); apply Eq.trans _ (Hatch.cost id _ hg).symm; unfold palm_R; funext z; apply sum_congr rfl; intro i t; change Mew.pine i _ • tipI f (Cue J i)=_; rw [u.queen _ (show ψS id _ from by unfold ψS; rw[List.map_id]; exact sort_nodup ..)]
#print axioms canH
#print axioms clipGear
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
