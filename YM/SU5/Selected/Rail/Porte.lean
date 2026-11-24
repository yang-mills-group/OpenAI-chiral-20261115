import YM.SU5.Selected.Rail.Fjord
import Mathlib.MeasureTheory.Integral.Pi
/-! # Integrals in the AP parity. hill × td.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset
variable {V:Type*}[TopologicalSpace V]
def harbor (p:Bin): Coast:= fun i=> ↑(p i)
@[fun_prop] lemma harbor_c : Continuous harbor:=by unfold harbor; exact continuous_pi fun i=> (AddCircle.continuous_mk' _).comp (continuous_apply i) -- tune name conflict Airy.harbor already
lemma harbor_join(x:Facet3)(t:ℝ): harbor (Ε x t)= Ε (road x) (t:roundC):= by ext1 i; cases i using Fin.lastCases <;> simp [harbor,Ε,road]
lemma promenade (x:Coast): ∃ y:Bin,y∈stemGuard∧ x=harbor y:=by
 choose f p g using fun i=>cueDeck (x i); refine ⟨f,?_,funext g⟩; apply stemG.mpr; exact (pi_norm_le_iff_of_nonneg pi_pos.le).mpr (fun i=> abs_le.mpr ⟨(p i).1.le,(p i).2⟩)
lemma allPeer {x y:Bin}(p:harbor x= harbor y):∃ w:Cover, y=x+ stem w:=by
 have e(i:Axis): ((y i-x i:ℝ):roundC)=0:=by rw [AddCircle.coe_sub]; exact sub_eq_zero.mpr (congrFun p i).symm
 choose w h using fun i=> AddCircle.coe_eq_zero_iff (p:=φ)|>.mp (e i); refine ⟨w,?_⟩; ext1 i; rw [Pi.add_apply,stem]; simp_rw [zsmul_eq_mul] at h -- stem may mul
 linarith only [h i]
lemma global {F:Bin→V}(h:ContinuousOn F stemGuard)(e:∀ x w,F (x+stem w)=F x): ∃ g:Coast→ V, Continuous g∧∀ x,g (harbor x)= F x:=by
 choose v p f using promenade; let g:= F ∘ v; have hp(x):g (harbor x)=F x:=by obtain ⟨t,u⟩:= allPeer (f (harbor x)); unfold g; rw [Function.comp_apply,u,e];
 let T:stemGuard → Coast:=fun x=> harbor x.val; have he:Continuous T:= harbor_c.comp continuous_subtype_val; have hf:Surjective T:= fun x=> ⟨⟨v x,p x⟩,(f x).symm⟩; haveI:CompactSpace stemGuard:=isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
 refine ⟨g,(he.isClosedMap.isQuotientMap he hf).continuous_iff.mpr ?_,hp⟩; have hT: g ∘ T= F ∘ ((↑): stemGuard→ Bin):= funext (fun x=> hp x.val); rw [hT]; exact continuousOn_iff_continuous_restrict.mp h
-- period of beat all x
lemma keeps_F (k:ℕ)(u:Bin)(v:Cover):beat k (u+stem v)=beat k u:=by
 unfold beat finale; rw [Airy.regime]; unfold fleece fade; rw [Pi.add_apply]; congr 2; rw [show u 3+stem v 3= turn (u 3) (v 3) from rfl]; congr 1; simpa only [Int.cast_one] using surge_periodic 1 (v 3) (u 3) -- int cast
lemma keep_F (k:ℕ)(h:3≤k):∃ f:Coast→Op SpinIdx, Continuous f∧∀ x,f (harbor x)=beat k x:= global (beating h) (keeps_F k)
local notation "D" => Set.Icc (-π) π
lemma econ : volume.restrict (D)=volume.restrict deck:= Measure.restrict_congr_set (Ioc_ae_eq_Icc).symm -- lemma namespace
abbrev ferry4:= hammerLand.prod (volume.restrict (D))
def rent':= (φ:ℝ) ^ (4:ℕ)
lemma rent_pos : 0<rent':=by unfold rent'; positivity
instance :IsFiniteMeasure ferry4:=inferInstanceAs (IsFiniteMeasure (hammerLand.prod _))
def view (f:Bin→ℂ):ℂ:= ∫ x, f (joinBin x) ∂ferry4
def perch (f:Coast→ℂ):ℂ:= (↑rent':ℂ)⁻¹ * view (f ∘ harbor)
-- totals exact pure modes
lemma oath (w:ℤ): (∫ x in deck, fourier w (x:roundC)) = if w=0 then (↑(φ:ℝ):ℂ) else 0:= by
 simp_rw [soldier]; rw [← intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos])]
 by_cases p:w=0; · subst w; simp [surge,Complex.real_smul]; ring
 let c:=Complex.I * (w:ℂ); have hp(t:ℝ): surge w t= Complex.exp (c*(t:ℂ)):=by unfold surge c; push_cast; congr 1; ring
 have h: Complex.exp (c*(π:ℂ))=Complex.exp (c *((-π:ℝ):ℂ)):=by rw [←hp,←hp, ←surge_periodic w 1 (-π),show turn (-π) 1=π by unfold turn; push_cast; ring]
 simp_rw [hp]; rw [if_neg p,integral_exp_mul_complex (show c≠0 from mul_ne_zero Complex.I_ne_zero (by exact_mod_cast p)),h,sub_self,zero_div]
lemma hill_pi:hill=Set.univ.pi fun _:Fin 3=> (D):=by
 ext1 i; constructor; exact fun p j _=> hillv p j
 exact fun p=> hill_mem.mpr ((pi_norm_le_iff_of_nonneg pi_pos.le).mpr fun j=> abs_le.mpr (p j (Set.mem_univ j)))
lemma hang (k:Cover): (perch (prefixG k))= if k=0 then 1 else 0:=by
 let Y:FaceL:=fun i=> k i.castSucc; let j:=k 3; have hk: Ε Y j=k:=Fin.snoc_init_self _
 let T (i:Fin 3)(x:ℝ):= fourier (Y i) (x:roundC); let d(x:Facet3):= grappa Y x
 have he(x:Facet3 × ℝ): ((prefixG k) ∘ harbor) (joinBin x)=d x.1 * fourier j (x.2:roundC):=by unfold comp joinBin; rw [harbor_join,←hk,tintMono]; rfl
 have hp: (∫ x:Facet3,d x∂hammerLand)= ∏ i:Fin 3, (if Y i=0 then (↑(φ:ℝ):ℂ) else 0):=by
    rw [hammerLand,hill_pi]; change (∫ x:Facet3,∏ i,T i (x i) ∂ (Measure.pi (fun _:Fin 3=> (volume : Measure ℝ))).restrict _) =_; rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod T]; exact prod_congr rfl fun i _=> econ.symm ▸ oath (Y i) -- tune
 unfold perch view; simp_rw [he]; unfold ferry4; rw [integral_prod_mul d (fun x:ℝ=> fourier j (x:roundC)),hp,econ,oath] -- lemma args
 by_cases p:k=0
 · simp only [Y,j,p,Pi.zero_apply,if_true,prod_const,card_univ,Fintype.card_fin]; rw [show (↑rent':ℂ)=(↑(φ:ℝ):ℂ)^ (3:ℕ)* (↑(φ:ℝ):ℂ) by unfold rent'; rw [Complex.ofReal_pow,pow_succ]]; apply inv_mul_cancel₀; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast piRank.ne')) (by exact_mod_cast piRank.ne')
 rw [if_neg p]; by_cases u:j=0; swap; · simp [u];
 have hv: Y≠0:=by intro e; apply p; rw [←hk,e,u]; ext1 i; cases i using Fin.lastCases <;> simp [Ε]
 obtain ⟨i,h⟩:= Function.ne_iff.mp hv; rw [Finset.prod_eq_zero (mem_univ i) (if_neg (show Y i≠0 from h)),zero_mul,mul_zero]

end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms global
#print axioms oath
#print axioms keeps_F
#print axioms hang
