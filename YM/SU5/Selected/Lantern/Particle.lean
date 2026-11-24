import YM.SU5.Selected.Lantern.Bolts
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
open Stencil
variable {n:Side}
-- mark algebra straightforward, retain detailed interlacing separate properties for Bolt geometry.
set_option synthInstance.maxSize 25000
local notation "μρ"=> Stencil.rho
def Hearth (S:Finset (Seat n)): Subalgebra ℂ (Buffered.Mark n) where
 carrier := {A|AtSupport false S A}
 add_mem' x y := AtSupport.addM x y
 mul_mem' x y := AtSupport.mulM x y
 algebraMap_mem' z:=by rw [Algebra.algebraMap_eq_smul_one]; exact (AtSupport.oneM S).smulM _
abbrev Floor (S:Finset (Seat n)) := ↥(Hearth S)
instance (S:Finset (Seat n)): CommRing (Floor S) where
 mul_comm x y:= Subtype.ext (funext (fun i=> fineWise (Window.fine_enlarge (subset_univ _) ((show AtSupport _ _ _ from x.property).allV i)) (Window.fine_enlarge (subset_univ _) ((show AtSupport _ _ _ from y.property).allV i)))) -- maybe orientation defeq not hp

def flickH (S:Finset (Seat n))(x:Fields n): Floor S →ₐ[ℂ] FC (Single n):= (Pi.evalAlgHom ℂ (fun (_:Fields n)=>FC (Single n)) x).comp ((Hearth S).val) -- tune
lemma shinesH (S:Finset (Seat n))(x:Fields n)(p:Floor S): flickH S x p= p.val x:=rfl
-- exact foil at color group count. Standard list from finiteness instance. Need weaving `L.map column`. W & labels. General `q→ V`, g support. 
variable {d r:Type}[Fintype d][DecidableEq d] [Fintype r][DecidableEq r]
local notation "τ₀"=> (univ:Finset r).toList
structure Station (q:Finset (Seat n))(d r:Type)[Fintype d][Fintype r][DecidableEq r] where
 -- first patch aperture separated & CT support requirements carried elsewhere. FOR pressure just AtSupport broad for **all** integrated F at a given t. later narrower projection path & Σχ statements.
 low : d→Bool→ Fields n→ WRect (Single n) r -- X* raw remove
 high : d→Bool→Fields n→WRect (Single n) r -- Y+ visible partner
 sealed_ (i: d)(t:pulseNode) :
    AtSupport false q (fun x:Fields n=> -(tape true (mixt_a t (low i true x) (low i false x))* tape false (mixt_b t (high i true x) (high i false x))))
variable {S T:Finset (Seat n)} (H:Station S d r) (i:d)
namespace Station
def fLow (t:pulseNode)(x:Fields n):= mixt_a t (H.low i true x) (H.low i false x)
def fHigh (t:pulseNode)(x:Fields n):= mixt_b t (H.high i true x) (H.high i false x)
def roster (t:pulseNode): Floor S:= ⟨fun x=> -(tape true (H.fLow i t x)* tape false (H.fHigh i t x)),H.sealed_ i t⟩
lemma pore (p:Fintype.card r=10)(x:Fields n) :
 flickH S x (tonality μρ (H.roster i))= -(((10:ℂ)⁻¹ • countOne (H.low i true x) (H.low i false x) true) * countOne (H.high i true x) (H.high i false x) false):=by
 rw [tonality,map_sum]; simp_rw [map_smul]; simp_rw [show ∀ c, flickH S x (H.roster i c)= _ from (fun c=> (rfl : _= -(tape true (H.fLow i c x)* tape false (H.fHigh i c x)))),smul_neg, sum_neg_distrib]; unfold fLow fHigh; exact congrArg Neg.neg (cubature (b:=false) _ _ p) -- tune order
-- each attached t choices as chosen simultaneously; bake enters angular moment. Allow independent root *basis* rotations after pointwise gauge-fix used to compare model. $δ,ε$ w inner halo only on renter. 
variable (δ τ ξ η R : ℝ) (w t j k:ℕ) (M:Tulip.Male)(T)
abbrev suffix(i:d): r → d×r:=Prod.mk i
def pierG (i:d):Finset (d×r):=univ.image (fun t=>(i,t))
def aloft (i:d):List (d×r):= (τ₀).map (fun a=>(i,a))
def chamber : Cab n:= ⟨S,T,false, ((ballet k univ (polar μρ (roster H)): Floor S): Mark n)⟩
local notation "Y"=>H.chamber T k -- parameter order maybe
#print chamber
abbrev portionG (X:WRect (Single n) (d×r))(i:d):Matrix (Single n) r ℂ:= @HMul.hMul _ _ (Matrix (Single n) r ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X (mask (fun a:r=>(i,a)))
structure Turnout (V:Station S d r) (F:Fields n)(f:d→pulseNode)(X Z:WRect (Single n) (d×r)): Prop where
 size:QModel F M j R η ξ false T X Z
 can (i:d):∃ A B:Op r, A.det=1∧ B.det=1∧portionG X i = (V.fLow i (f i) F) * A ∧ above (portionG Z i) (Tset n) false=(V.fHigh i (f i) F) * B
variable {M j δ R τ ξ η w t T}
#print Turnout.mk
private lemma lists(X Z:WRect (Single n) (d×r))(i:d): markedArc false (aloft (r:=r) i) (Tset n) X Z=markedArc false (τ₀) (Tset n) (portionG X i) (portionG Z i):=by
 have h(X:WRect (Single n) (d×r))(a:r): col (portionG X i) a= col X (i,a):=by apply PiLp.ext; intro x; simp only [col_val]; exact mask_mem ..
 unfold markedArc aloft foil; rw [List.map_map]; apply congrArg List.prod; congr 1; funext t; simp only [Function.comp,Pi.sub_apply,Pi.one_apply,rootLetter,h]
private lemma nights (p:Fintype.card r=10) (F:Fields n)(f:d→pulseNode){X Z:WRect (Single n) (d×r)} (e:Turnout T ξ η R j M H F f X Z):(flickH S F) (H.roster i (f i))=markedArc false (aloft i) (Tset n) X Z:=by -- placeholders
 obtain ⟨A,B,h,g,t,z⟩:=e.can i; symm; rw [lists]; exact pathCombine (portionG X i) (portionG Z i) (Tset n) false (show _ from (by unfold portionG; rw [←Matrix.mul_assoc,e.size.pitch])) p _ _ h g _ _ t z
private lemma dancing (p:Fintype.card r=10) (u:0<k)(t':Fintype.card d=10*k)(F:Fields n)(g:∀ f:d→pulseNode,∃ X Z, Turnout T ξ η R j M H F f X Z) :
    Blend (Marquee F M j R η ξ false T (d×r) k) ((2^(22:ℕ)*(3^(10:ℕ))^ (10:ℕ)*(∑ i, ‖μρ i‖)^ (10:ℕ))^k)
      ((Y).frame F):=by -- tune
 choose X Z w using g; let U(f:d→pulseNode)(a:d×r):= rootLetter (X f) (Z f) false (Tset n) a; -- paths
 apply monthly μρ (roster H) (flickH _ F) U (pierG (d:=d)) _ k _ _ rho_unit u t' ?_ ?_ ?_ (by norm_num) le_rfl -- orientation order
 · intro i a v; apply disjoint_left.mpr; intro c h t; obtain ⟨x,h,rfl⟩:= mem_image.mp h; obtain ⟨y,h,t⟩:=mem_image.mp t; exact v (Prod.mk.inj t).1.symm
 · intro f i; rw [map_sub, map_one,nights H i p _ f (w f)]; have hv:pierG (r:=r) i= (aloft (r:=r) i).toFinset:=by unfold aloft pierG; ext; simp
   rw [hv]; exact arc_blend _ (Finset.nodup_toList _ |>.map (fun a b h=> (Prod.mk.inj h).2)) (by rw [List.length_map]; exact rung_len p) _ _ _
 intro f A t; obtain ⟨V,h,_,t,rfl⟩:=t; exact ⟨X f,Z f,V,(w f).size,t,h,rfl⟩
private lemma fares(V:ℝ)(p:0<k)(q:Fintype.card d=10*k)(F:Fields n)(v:1 ≤ V)(g:∀ i, ‖(flickH S F) (tonality μρ (roster H i))‖≤ V) : ‖(Y).frame F‖ ≤ ( ((2:ℝ)^(13:ℕ)* V^(10:ℕ))^k ):=
 loads_dirty (flickH S F) (polar μρ (roster H)) p v (card_univ.trans q) (fun i _=> g i)

def tollK (V:ℝ):= max ((2:ℝ)^(22:ℕ)*(3^(10:ℕ))^ (10:ℕ)*(∑ i, ‖μρ i‖)^ (10:ℕ)) ((2:ℝ)^ (13:ℕ)* V^ (10:ℕ))
#print tollK
theorem ships (W:ℝ)(p: Fintype.card r=10) (q:Fintype.card d=10*k)(u: 0<k)(e: S.Nonempty)(z:T ⊆ S)(g:Distant w (Sᶜ) T)
    (ω:1 ≤ W)(v:∀ F:Fields n,∀ i, ‖(flickH S F) (tonality μρ (roster H i))‖≤ W) (hf:∀ F:Fields n,(Y).feels F t τ → Agrees S F.1 F.2 → Guard F.2 δ → ∀ f:d→pulseNode, ∃ X Z, Turnout T ξ η R j M H F f X Z):
       Lounge M j w t τ η ξ (tollK W) R δ (d×r) k (Y):=by
 refine ⟨e,(show (ballet _ _ (_): Floor S).val∈ Hearth S from (ballet k univ (polar μρ (roster H)): Floor S).property),z,g,fun x=>?_,fun x a b c=>?_⟩
 · exact (fares (T:=T) H k W u q x ω (v x)).trans (pow_le_pow_left₀ (by positivity) (le_max_right ..) k)
 apply (dancing H k p u q x (hf x a b c)).extendsTo
 exact pow_le_pow_left₀ (by positivity) (le_max_left ..) k

end Station
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Station.ships
#print axioms Station.pore
