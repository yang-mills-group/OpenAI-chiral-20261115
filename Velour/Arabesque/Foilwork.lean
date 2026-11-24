import Velour.Arabesque.Recess
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

open YM.Damask

variable {S}{H':Hilbert}{b:Axis}{T:Semigroup H' b}
variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
   (h:a≠b)(A:S.Tiles h)(B:T.Tiles (Ne.symm h))
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "R"=>L.penny h A u X
local notation "Q"=>J.penny h.symm B u X

-- Integrating meter in the b-clear region
def roll(g:σ):Points n ≃ₗᵢ[ℝ] Points n where
 toFun x:=points (x.ofLp ∘ g)
 invFun x:= points (x.ofLp ∘ g.symm)
 left_inv x:=PiLp.ext fun i=>congrArg _ (g.apply_symm_apply i)
 right_inv x:=PiLp.ext fun i=>congrArg _ (g.symm_apply_apply i)
 map_add' _ _:= rfl
 map_smul' _ _:=rfl
 norm_map' x:= by
    change ‖points _‖=‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [PiLp.norm_sq_eq_of_L2 _ (points _),PiLp.norm_sq_eq_of_L2 _ x]
    exact Equiv.sum_comp g (fun i=> ‖x i‖ ^ 2)
lemma inspect_work (f:Fin n→Test4)(g:σ)(x:Points n):
 Joint.materialize n (f ∘ g) (roll g x)=Joint.materialize n f x:=by
 rw [Joint.material_at,Joint.material_at]
 exact Equiv.prod_comp g (fun i=> f i (x i))


lemma transferring(g:σ)(x:Points n)(d:ℓ)(t:StrictMono (d∘g)):
 L.penny h A u x.ofLp g (initβ (clockV a x) d I) (soaked (clockV b x))
 = L.gemK h A (u ∘ g) (soaked (d∘g)) 0 (roll g x):=by
 let w:=clockV a x; let v:=clockV b x
 have y: points (posed h (x.ofLp ∘ g) (w ∘ g) (v ∘ g))= roll g x:=by
    ext1 i; exact sheer_self ..
 have p:Radial (soaked (d∘g)) 0:= by
   rw [show (0:Fin n→ℂ)=soaked 0 by ext; simp [soaked]]
   exact (wet _ _).mpr t
 have j:= L.gems h A (u ∘g) (x.ofLp ∘g) (w ∘ g) (v ∘ g)
   (soaked (d∘g)) 0 p
 have e:spill (soaked (d ∘ g)) (w ∘ g)=initβ (w ∘g) (d∘g) I:=by
     ext i; dsimp only [spill,soaked,initβ]; unfold sideways; ring
 have z:spur 0 (v ∘ g)=soaked (v ∘g):=by ext; simp [spur,soaked]
 rw [y,e,z] at j; exact j


variable (f:Fin n→Test4)
local notation "F"=>Joint.materialize n f
def scrollG(g:σ)(k:ℕ)(x:Points n):=
 F x * L.penny h A u x.ofLp g (initβ (clockV a x) (chosenHeight g k) I)
    (soaked (clockV b x))
local notation "M"=> L.scrollG h A u f

def recital(g:σ)(k:ℕ):Points n→ℂ:=
 concert S L.Ω.val L.Ω.val (L.spunG (u∘g))
    (L.risers h A (u∘g) (soaked (hymns n k)) 0) (f∘g)
lemma rollG(g:σ)(k:ℕ):M g k=L.recital h A u f g k ∘ roll g:=by
 funext x
 dsimp only [scrollG,recital,concert, comp_apply]; rw [transferring,tallness,inspect_work]
 rw [tallness]; exact hymnsP n k

lemma unitM(g:σ)(k:ℕ): Integrable (M g k):=by
 rw [L.rollG h A u f g k]
 exact ((roll g).measurePreserving.integrable_comp_emb
     (roll g).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (billI ..)

lemma dues(g:σ): Tendsto (fun k=>∫x,M g k x) atTop (𝓝 (L.brim (u ∘g) (f∘g))):=by
  have t(q:ℕ): (∫x,M g q x)=∫x,L.recital h A u f g q x:=by
     rw [L.rollG]
     exact (roll g).measurePreserving.integral_comp
        (roll g).toHomeomorph.toMeasurableEquiv.measurableEmbedding _
  simp_rw [t]
  apply L.recaps (u ∘g) (silk h) A (fun k=>soaked (hymns n k)) (fun _=>0)
  · intro i
    rw [show (0:ℒ)=soaked 0 by ext; simp [soaked]]
    exact (wet _ _).mpr (hymnsP ..)
  · intro i; simpa [Function.comp_def,soaked] using (continuous_ofReal.tendsto _).comp (hymnsL n i)
  exact fun _=>tendsto_const_nhds

structure Insular (a b:Axis)(f:Fin n→Test4) :Prop where
 gap:∃d:ℝ,0<d∧∀x:Points n,Joint.materialize n f x≠0→ amid (clockV a x) (clockV b x) d

include A B
theorem yes (g j:σ)(p:Insular a b f)(r:Pact L J):
 L.brim (u ∘ g) (f ∘ g)= L.brim (u ∘j) (f ∘j):=by
 obtain ⟨d,z,w⟩:=p.gap
 let K:=Joint.materialize n f
 have l:Integrable (⇑K) volume:=SchwartzMap.integrable K
 obtain ⟨c,y,v⟩:= L.rebate J h A B u r d z

 have high(t:σ)(i:ℕ)(x:Points n):
     ‖M t i x‖ ≤ ‖K x‖*c:=by
     unfold scrollG; rw [norm_mul]
     by_cases H:F x=0
     · simp [K,H]
     exact mul_le_mul_of_nonneg_left 
       (v _ t _ _ (chosenHeight t i) (w x H) (by rw [tallness]; exact hymnsP ..))
       (norm_nonneg _)
 let E(i:ℕ)(x:Points n):=M g i x-M j i x
 have e(x):Tendsto (fun i=>E i x) atTop (𝓝 0):=by
     unfold E scrollG
     by_cases k:F x=0
     · simp [k]
     have T:=w x k
     obtain ⟨q,a⟩:=amidst z T
     have ee(t):=(L.freePenny J h A B u x.ofLp r _ _ t q _ z T a).const_mul (F x)
     simpa only [sub_self] using (ee g).sub (ee j)
 have one: Tendsto (fun i=>∫x,E i x) atTop (𝓝 (∫_:Points n,(0:ℂ))):=by
     apply tendsto_integral_of_dominated_convergence
       (fun x=> ‖K x‖*c+‖K x‖*c)
     · exact fun i=>((L.unitM h A u f g i).sub (L.unitM h A u f j i)).aestronglyMeasurable
     · exact (l.norm.mul_const c).add (l.norm.mul_const c)
     · exact fun i=>ae_of_all _ fun x=>(norm_sub_le ..).trans (add_le_add (high _ _ _) (high _ _ _))
     exact ae_of_all _ e
 rw [integral_zero] at one
 apply sub_eq_zero.mp
 exact tendsto_nhds_unique_of_eventuallyEq ((L.dues h A u f g).sub (L.dues h A u f j))
    one (Eventually.of_forall fun i=>(integral_sub (L.unitM h A u f g i) (L.unitM h A u f j i)).symm)
#print axioms yes
