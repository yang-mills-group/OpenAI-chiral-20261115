import Velour.Ispahan.Turn
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} (S:Semigroup H timeAxis)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {S}
variable {κ:Type}(L:S.Livery κ)
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "D"=>S.muslin
local notation "Ω"=>L.Ω
local notation "Y"=>L.Y
local notation "U"=>S.liftL
local notation "τ"=>κ × Test4
local notation "ℙ"=>List (κ × Test4)

open Mink Mink.Lorentz YM.Motifs

open YM.Damask Spectral Measure

def linked (l:ℙ)(g:Lorentz):=S.ℚmeasure.diagonal (L.gem (throng g l)).val
instance (l:ℙ)(g:Lorentz): IsFiniteMeasure (L.linked l g):= S.ℚmeasure.finite _
def spun (l:ℙ)(g:Lorentz):=(L.linked l g).map (act (g.dual)⁻¹)
instance (l:ℙ)(g:Lorentz): IsFiniteMeasure (L.spun l g):=by unfold spun; infer_instance

lemma fleck (l r:ℙ) (m:∀g,S.Faces (L.line_ (throng g l)) (L.line_ (throng g r)))
 (g:Lorentz)(p:E4):
 charFun (L.spun l g) p=L.song (throng g (r++parade p l)):=by
  let x:= L.gem (throng g l)
  have y:charFun (L.spun l g) p=inner ℂ x.val (S.liftL (act g p) x).val:=by
    change _=inner ℂ _ (S.unit.translation _ _)

    have w: MeasurableEmbedding (⇑(act g.dual⁻¹)):=g.dual.sends.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [← S.joint, charFun_apply,charFun_apply,spun,w.integral_map]
    have e(v:E4):inner ℝ (act g.dual⁻¹ v) p=inner ℝ v (act g p):=by
       rw [real_inner_comm,← dual_sent g, undoes,real_inner_comm]
    simp_rw [e];rfl
  rw [y,song,throng,List.map_append, gem, line_append,Module.End.mul_apply]
  change _= inner ℂ _ (L.line_ (throng g r) (L.gem (throng g (parade p l)))).val
  rw [← parade_throng,L.parade_vac,← m]
  rfl

def shekel (l:ℙ)(f:Test4)(g:Lorentz):ℂ:=pref E4 • ∫p, f p ∂L.spun l g
lemma medallion (h:L.Blithe)(l:ℙ)(f:Test4):
 Pattern (L.shekel l f):=by
 obtain ⟨r,_,e⟩:=L.looking h.fray l
 intro g b
 obtain ⟨d,v⟩:=L.trellis h l r b g
 refine ⟨d,Grows.of_raised ?_⟩
 intro t
 let a(y):= L.spun l (scroll b y*g)
 let z(i):= hoops d (Damask.raised d) (risen t) i
 have j(p):charFun (a t) p * hat f p=
   ∑ i,z i*(charFun (a (levy d i)) p * hat f p):=by
    simp_rw [a,L.fleck l r e]
    rw [v p t,Finset.sum_mul]; simp only [z, mul_assoc]
 dsimp only [shekel]
 rw [← wave_integral]
 conv_lhs => change (∫p,charFun (a t) p*hat f p); rhs; ext p; rw [j]
 rw [integral_finsetSum]
 · refine Finset.sum_congr rfl fun i _=>?_
   rw [integral_const_mul, ← wave_integral]
 intro i _
 let m:=a (levy d i)
 apply Integrable.const_mul
 exact ((hat f).integrable.const_mul ((m.real univ):ℂ)).mono
    (measurable_charFun.mul (hat f).continuous.measurable).aestronglyMeasurable
    (ae_of_all _ fun p=>by
       rw [norm_mul,norm_mul,norm_real]
       exact mul_le_mul_of_nonneg_right ((norm_charFun_le _).trans (le_abs_self _)) (norm_nonneg _))
#print axioms medallion



def pend (g:Lorentz)(x:E4):ℝ:= (act g (General.walk reverseL x)) timeAxis
lemma pend_at(g:Lorentz)(x:E4):pend g x= act g.dual x timeAxis:=by
 change _=YM.time (General.walk reverseL (act g (General.walk reverseL x)))
 rw [reversing, time_position];rfl

lemma shunted(p:E4)(i:p ∉ Mink.cone):∃V:Set E4,p∈V∧ IsOpen V ∧
 ∃k∈lobes,∀ᶠ g in 𝓝 k,∀x∈V,pend g x<0:=by
 obtain ⟨m,q⟩:∃m:Lorentz,(act m.dual p) timeAxis<0:=by
    rw [from_half] at i; push Not at i; exact i
 obtain ⟨k,y,t,j,rfl⟩:= filigree m
 have z:pend k p<0:=by
    have e:= (pin_iff t).mp j (act k (General.walk reverseL p))
    change YM.time _ < 0
    rw [←e]
    rwa [←pend_at] at q
 have u:Continuous (fun t:Lorentz × E4=>pend t.1 t.2):=by unfold pend;fun_prop
 obtain ⟨R,R0,W,f,g⟩:=mem_prod_iff.mp (((u.tendsto (k,p)).eventually (gt_mem_nhds z)).filter_mono
    (show (𝓝 k) ×ˢ (𝓝 p) ≤ _ by rw [←nhds_prod_eq]))
 exact ⟨interior W,mem_interior_iff_mem_nhds.mpr f,isOpen_interior,k,y, Eventually.mono R0
         fun _ r x a=>g (show (_,x)∈R×ˢW from ⟨r,interior_subset a⟩)⟩


lemma twigs (h:L.Blithe)(l:ℙ)(p:E4)(i:p∉Mink.cone):
 ∃V:Set E4,p∈V∧IsOpen V ∧ (L.spun l 1) V=0:= by
 obtain ⟨V,m,o,k,r,x⟩:=shunted p i
 refine ⟨V,m,o,(picker _ o).mpr fun f _ j=>?_⟩
 have t:L.shekel l f 1=0:=by
    have z:Motifs.Pattern (fun _=>0):=by
      intro _ _
      exact ⟨0,Grows.of_raised (g:=fun _=>0) (by simp)⟩
    refine enthroned (L.medallion h l f) z k r ?_
    filter_upwards [x] with g u
    unfold shekel spun
    have w: MeasurableEmbedding (⇑(act g.dual⁻¹)):=g.dual.sends.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [w.integral_map]
    rw [integral_eq_zero_of_ae _,smul_zero]
    unfold linked
    filter_upwards [S.bright (L.gem (throng g l)).val] with q v
    change f (act g.dual⁻¹ q)=0
    by_contra e
    have a:=u _ (j (subset_tsupport _ e))
    rw [pend_at,undoes] at a
    exact not_lt_of_ge v a
 exact (smul_eq_zero_iff_right prepos.ne').mp t

lemma spun_down (l:ℙ): L.spun l 1=S.ℚmeasure.diagonal (L.gem l).val:=by
 have e: dual 1=1:=Lorentz.ext _ _ (fun _=>by simp [dual,Lorentz.act])
 unfold spun linked
 rw [throng_1,e,inv_one,(show ⇑(act 1)=id from rfl),Measure.map_id]

local notation "𝓓"=>S.ℚmeasure
local notation "N"=>S.nursery Y Ω

lemma pepper(h:L.Blithe)(l:ℙ):(𝓓).region (Mink.coneᶜ) (L.gem l).val=0:=by
 apply ((𝓓).null_pair Mink.closed_cone.isOpen_compl.measurableSet _).mp
 rw [←spun_down]; refine measure_mono_null ?_ Measure.measure_compl_support
 intro p i e
 obtain ⟨a,t,o,x⟩:=L.twigs h l p i
 exact ((Measure.mem_support_iff_forall p).mp e a (o.mem_nhds t)).ne' x

theorem basin(h:L.Blithe){v:H}(t:v∈N):
 (𝓓).region Mink.coneᶜ v=0:=by
 let P x:= (𝓓).region Mink.coneᶜ x=0
 have y(x:D)(i:x∈S.sprout Y Ω): P x.val:=by
    refine L.seedlings (P:=fun x=> (𝓓).region Mink.coneᶜ x.val=0) ?_ ?_ 
       (fun _ _=>L.pepper h _) _ i
    · simp only [Submodule.coe_add, map_add]
      exact fun _ _ t u=>by rw [t,u,zero_add]
    intro v r c
    rw [Submodule.coe_smul_of_tower,map_smul,r,smul_zero]

 refine (show (N:Set H.space) ⊆ {v|P v} from
          closure_minimal ?_ (isClosed_eq ((𝓓).region _).continuous continuous_const)) t
 rintro _ ⟨x,a,rfl⟩
 exact y x a
#print axioms basin



