import Merino.Brooch.Era

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

open Dial Vow

open Salt Tenant Tap RG

variable (s:Sweep N){P W:SOp N}{X:SOp N}{K:Scree.Loom N}{q l m:ℕ}
variable {p:BudgetPoint}{a b c d h t u v z:ℝ}
variable {o:Site N}
local notation "post"=> node o
local notation "G"=> Fence P W K p q l ((boxA s) post) h z


def paneMask(p:BudgetPoint)(x:Site N)(mask:Bool)(F:LatticeFieldEstimates N):LatticeFieldEstimates N:=
  if mask then ({V|pingS p.threshold (offsetMask p.B x) V}:Set (Pane N)).indicator F else F

lemma scene_mask (S:Scree.Loom N)(x:Site N)(F:LatticeFieldEstimates N):
 scene0 s S (paneMask p x true F)=
    houseK p (Lattice.halo p.B {boxA s (node x)}) (scene0 s S F):=by
 funext i
 let A:Set (Pane N):={V|pingS p.threshold (offsetMask p.B x) V}
 let U:=back s i.1
 let T:=Lattice.halo p.B {boxA s (node x)}
 have e:i∈pingMask p T ↔ U∈A:=by
    have zz:actY s {(boxA s) (node x)}={node x}:=by simp [actY]
    change pingS p.threshold T i.1↔pingS p.threshold (halo p.B {node x}) (flashA s i.1)
    nth_rw 1 [← zz]; rw [walkA,glowA]


 unfold houseK
 by_cases g: U∈A
 · rw [Set.indicator_of_mem (e.mpr g)]
   change move s (A.indicator F U _)=_
   rw [Set.indicator_of_mem g]; rfl
 rw [Set.indicator_of_notMem (mt e.mp g)]
 change move s (A.indicator F U _)=_
 rw [Set.indicator_of_notMem g]
 change tourP (actSpin s) (actB s) (actR s) 0=0
 unfold Spire.tourP; cases actR s <;> cases actB s <;> simp [windX,theta_zero]
-- old aperture
variable (hm:p.B+2*m≤l*p.B)
include hm
lemma perkOf (x:Site N)(g:separation o x ≤ m):
    Lattice.halo p.B {(boxA s) (node x)}⊆grooveB l p (boxA s post):=by
 intro i f; obtain ⟨j,a,hx⟩:=halo_spec.mp f
 rw [mem_singleton.mp a] at hx
 exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle _ (boxA s (node x)) _).trans (by
   have e:separation (boxA s post) (boxA s (node x))≤2*m:=by
      rw [sitT,Hove.ζdist];omega
   omega)⟩


lemma pane_fee {x:Site N}(g:separation o x ≤ m)(C F:ℝ)
   (Y:LatticeFieldEstimates N)(k:G (scene0 s K Y) C F)
   (e:Bool) : G (scene0 s K (paneMask p x e Y)) C F:=by
  cases e; exact k
  rw [scene_mask];exact k.aft (perkOf s hm x g)

abbrev boom(p:BudgetPoint)(o x:Site N)(Y:SOp N)(e:Bool):=paneMask p x e (metal (co_Ψ x o Y))
def perWave(p:BudgetPoint)(o:Site N)(m:ℕ)(Y:Axis→SOp N)(e:Bool):LatticeFieldEstimates N:= ∑i,(boom p o (o+gapPlus i m) (Y i) e - -- parser
    boom p o (o-gapPlus i m) (Y i) e)

def stretch (a:ℝ)(m:ℕ)(v:ℝ):=Real.exp (a*(4*(2*(m:ℝ))+1))*(Tenant.quota^2*v)
abbrev oneWave(l m:ℕ)(p:BudgetPoint)(z h a c v:ℝ):=foFee l p z h a c (stretch a m v)
abbrev warFee(l m:ℕ)(p:BudgetPoint)(z h a c v:ℝ):=8*oneWave l m p z h a c v

variable (D:DockPulse p K t d a h z l q)
variable (H:Solo a c P d)(Q:Solo a c W d)
include D H Q
local notation "S"=> oneWave l m p z h a c v


lemma boom_sale(x:Site N)(e:Bool)(r:separation o x ≤ m)(i:Soak post X a v d):
 G (scene0 s K (boom p o x X e)) S S:=by
 have l₁:=soak_tr (o':=post) (co_Ξ x o (x:=rfl) i) D.hint.le
 refine pane_fee s hm r _ _ _ (act_metal s D H Q (lift_U l₁ ?_)) e
 unfold stretch
 apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (mul_nonneg (sq_nonneg _) (soakCostNN i))
 apply mul_le_mul_of_nonneg_left _ D.hint.le
 have e:separation (node x) post ≤2*m:= by rw [Hove.ζdist,separation_comm]; omega
 exact add_le_add_left (mul_le_mul_of_nonneg_left (by exact_mod_cast e) (by positivity)) _

lemma wave_sale {J:Axis→SOp N}(j:∀i,Soak post (J i) a v d)(e:Bool):
  G (scene0 s K (perWave p o m J e)) (warFee l m p z h a c v) (warFee l m p z h a c v):=by
 rw [perWave,call_sum]
 simp_rw [call_less]
 rw [show warFee l m p z h a c v=∑ _:Axis, (S+S) from ?_]; swap; · simp [warFee];ring -- fix parentheses
 exact Fence.sumF _ _ _ _ (fun i _=> (boom_sale s hm D H Q _ e (stopBeam o i m).1 (j i)).sub
                                   (boom_sale s hm D H Q _ e (stopBeam o i m).2 (j i)))


def shank (m:ℕ)(o:Site N):LatticeFieldEstimates N := metal (fun _=>voidΛ N m o) - strike (fun _=> tickA N*voidΛ N m o)
def barFee(l m:ℕ)(p:BudgetPoint)(z h a c:ℝ):=foFee l p z h a c (wζ a m)+
   txFee l p z h (2*(Tap.wingRent Fir.Aop a*wζ a m))
local notation "Bf"=> barFee l m p z h a c

omit hm in
lemma buybar:G (scene0 s K (shank m o)) Bf Bf:=by
 have y:Soak post (fun _=>voidΛ N m o) a (wζ a m) d:=by
    convert windmillCost (d:=d) o m D.hint.le using 1
    rw [List.length_ofFn]
 rw [shank,call_less]
 exact (act_metal s D H Q y).sub
     (act_trace s (P:=P) (W:=W) D (aura_Y y (Tap.soil_tick a d) D.hint.le))

/-- View of short YY unscaled -/
def leanLatticeFieldEstimates (p:BudgetPoint)(o:Site N)(m:ℕ)(Y:Axis→SOp N)(X:SOp N):LatticeFieldEstimates N:=
 paneMask p o true (strike X-shank m o)+perWave p o m Y true
def tailLatticeFieldEstimates (p:BudgetPoint)(o:Site N)(m:ℕ)(Y:Axis→SOp N)(X:SOp N):LatticeFieldEstimates N:=
 strike X+perWave p o m Y false
def bright(l m:ℕ)(p:BudgetPoint)(z h a c b:ℝ):= (txFee l p z h b+barFee l m p z h a c)+warFee l m p z h a c b


def dull(l m:ℕ)(p:BudgetPoint)(z h a c v:ℝ):= txFee l p z h v+warFee l m p z h a c v
local notation "ttm"=> dull l m p z h a c v
local notation "bbm"=> bright l m p z h a c b

variable {Y X':Axis→SOp N}{T:SOp N}

lemma slim (x:Soak post X a b d)(y:∀i,Soak post (Y i) a b d):
 G (scene0 s K (leanLatticeFieldEstimates p o m Y X)) bbm bbm:=by
 rw [leanLatticeFieldEstimates,call_plus]
 refine Fence.arc (pane_fee s hm (by simp) _ _ _ ?_ true)
    (wave_sale s hm D H Q y true)
 rw [call_less]
 exact (act_trace s D x).sub (buybar s D H Q)
lemma thick (x:Soak post T a v d)(y:∀i,Soak post (Y i) a v d):
 G (scene0 s K (tailLatticeFieldEstimates p o m Y T)) ttm ttm:=by
 rw [tailLatticeFieldEstimates,call_plus]
 exact (act_trace s (P:=P) (W:=W) D x).arc (wave_sale s hm D H Q y false)
end YM.CF.Merino.Brooch

