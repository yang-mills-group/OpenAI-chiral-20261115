import GaugeFieldConstruction.Enmity
import GaugeFieldConstruction.Quail
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
variable {N:Side}{I Z D E : Type}[Fintype I][LinearOrder I][Fintype Z] [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
-- generalized `Book Cornea`.
structure Cornea (Z D E:Type)[NormedAddCommGroup E][NormedSpace ℂ E](N:Side) where
  Φ : Z →  Support N
  valid: Z → D →  Prop -- measurement domain.
  Lux : Z →  (D →  E)  →  ℝ  →  Prop
  posG(x:Z)(g:D → E)(r:ℝ)(p:Lux x g r):0≤ r
  zero(x:Z)(g:D → E)(u:∀ y,valid x y → g y=0): Lux x g 0
  add(x:Z)(g h:D →  E)(r s:ℝ)(p:Lux x g r)(q:Lux x h s):Lux x (g+h) (r+s)
  coin(x:Z)(g:D →  E)(r:ℝ)(p:Lux x g r)(z:ℂ): Lux x (z • g) (‖z‖*r)
  widen(x:Z)(g:D →  E)(r s:ℝ)(p:Lux x g r)(q:r≤ s) : Lux x g s
  inert(x:Z)(g h:D →  E)(p:∀ y, valid x y → g y=h y)(r:ℝ)(p₀:Lux x g r): Lux x h r
variable (X: Cornea Z D E N)
-- Note W items Turf claim independent of Ω.No projection.Tips pass on valid.
abbrev ShelfK (U:Z → D →  E)(p:ℕ)(a V:ℝ): Prop:= ∃ C:Z →  ℝ,(∀ i,X.Lux i (U i) (C i))∧∀ x: Site N,(∑ i∈ univ.filter (fun i=>x∈X.Φ i), dra_k p a (X.Φ i)*C i) ≤ V
abbrev BookT (U: Finset I → Z → D → E)(p:ℕ)(J:Finset (Finset I))(a r V:ℝ) :Prop:= ∃ F: Finset I → Z → ℝ,(∀ i∈J,∀ x,X.Lux x (U i x) (F i x))∧∀ x:Site N,(∑ i∈J,r^i.card* (∑ y∈ univ.filter (fun y=>x∈X.Φ y),dra_k p a (X.Φ y)*F i y)) ≤ V
variable {b:ℕ}{a r V:ℝ}
lemma Shelf_zero {U:Z → D → E}(p:∀ i y,X.valid i y  →  U i y=0):ShelfK X U b a 0:= ⟨0,fun i=>X.zero _ _ (p _),fun _=>by simp⟩
lemma Shelf_sal {U:Z → D →  E}{e:ℝ}(p:ShelfK X U b a V)(x:V≤e): ShelfK X U b a e:=by obtain ⟨C,h,u⟩:=p; exact ⟨C,h,fun i=> (u i).trans x⟩
lemma Shelf_adapt {U V:Z →  D →  E}{p:ℝ}(e:∀ i t,X.valid i t →  U i t=V i t)(h:ShelfK X U b a p):ShelfK X V b a p:=by obtain ⟨C,q,Z⟩:=h; exact ⟨C,fun i=>X.inert _ _ _ (e _) _ (q _),Z⟩
lemma Shelf_link {U T: Z → D →  E}(p:ShelfK X U b a V)(q:ShelfK X T b a r): ShelfK X (U+T) b a (V+r):=by
 obtain ⟨C,u,Z⟩:=p; obtain ⟨W,g,A⟩:=q; refine ⟨C+W,fun i=>X.add _ _ _ _ _ (u _) (g _),?_⟩; intro i; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (Z i) (A i)
lemma Shelf_coin {U:Z → D →  E}(p:ShelfK X U b a V)(z:ℂ):ShelfK X (z • U) b a (‖z‖*V):=by
 obtain ⟨C,u,W⟩:=p; refine ⟨‖z‖ • C,fun i=>X.coin _ _ _ (u _) z,?_⟩; intro i; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖z‖, ←mul_sum]; exact mul_le_mul_of_nonneg_left (W i) (norm_nonneg _)
lemma Shelf_σ {K:Type*}(S:Finset K){U:K → Z → D →  E}{V:K → ℝ}(p:∀ i∈ S,ShelfK X (U i) b a (V i)) : ShelfK X (∑ i∈S,U i) b a (∑ i∈S,V i):=by
 induction S using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact Shelf_zero _ (fun i y v=>rfl)
 | @insert i s u ih=> rw [sum_insert u,sum_insert u]; exact Shelf_link _ (p i (mem_insert_self ..)) (ih fun j v=>p j (mem_insert_of_mem v))
variable (σ: I → Site N)(C:I →  I → ℂ){Y: List I → Z → D → E}
abbrev ColLim (σ:I → Site N)(C:I →  I → ℂ)(m:ℝ): Prop:=∀ i,(∑ j∈ pipe_ζ σ i, ‖C j i‖) ≤ m
abbrev SnowPack (s:List I)(U:List I → Z → D →  E):Z →  D → E:=fun i y=> Roots.snow σ C (fun j=>U j i y) s
lemma LensBudget (p: ColLim σ C r)(v:0 ≤ r)(q:0≤V)(s:List I)(u:∀ l:List I,l.map σ=s.map σ  →  ShelfK X (Y l) b a V) : ShelfK X (SnowPack σ C s Y) b a (r^s.length*V):=by
 induction s generalizing Y with
 | nil=>rw [List.length_nil,pow_zero,one_mul]; exact u [] rfl -- defeq?
 | cons i s ih=>
    let T (j:I):=SnowPack σ C s (fun l=> Y (j::l)); let S:=pipe_ζ σ i; have he(j)(x:j∈S): ShelfK X (C j i • T j) b a (‖C j i‖*(r^s.length*V)):=by
       apply Shelf_coin; exact ih fun l h=>u _ (by rw [List.map_cons,List.map_cons,h,(mem_filter.mp x).2])
    have hx: SnowPack σ C (i::s) Y= ∑ j∈S,C j i • T j:=by funext y x; unfold SnowPack; rw [Roots.snow]; simp only [Finset.sum_apply]; rfl
    rw [hx]; refine Shelf_sal _ (Shelf_σ X S he) ?_; rw [←sum_mul,List.length_cons,pow_succ]; exact (mul_le_mul_of_nonneg_right (p _) (by positivity:0 ≤ r^s.length*V)).trans_eq (by ring)
abbrev Strain (σ:I → Site N)(U:Key I → Z →  D →  E): Prop:=∀ i y,X.valid i y →  (River (fun z=>U z i y))∧Hush σ (X.Φ i) (fun z=> U z i y)
abbrev Boats (σ:I → Site N)(C:I →  I → ℂ)(V:Key I →  Z → D →  E)(L:Finset I):Z → D →  E:=fun i y=>streamArc (fun z=>V z i y) σ C L
abbrev Ledges (σ:I → Site N)(V: Finset I → Z → D →  E): Prop:=∀ i y,X.valid i y → TidyK σ (X.Φ i) (fun l=> V l i y)
lemma Leads {U:Key I → Z →  D → E}(p:Strain X σ U): Ledges X σ (Boats σ C U):=fun i y u=> stream_A σ C _ _ (p i y u).1 (p i y u).2
lemma BeetK {U:Key I → Z → D →  E} (h:Strain X σ U)(P: Finset I)(hx:P∈ realm_C σ)(k:ColLim σ C r)(v:0≤ r)(q:0≤ V)(d:∀ l:List I,ψS σ l →  l.length=P.card  →  ShelfK X (fun i y=> tipI (fun z=> U z i y) l) b a V) : ShelfK X (Boats σ C U P) b a (r^P.card*V):=by
 let S:= Mew.Cue I P; let L(l:List I)(i:Z)(y:D):= tipI (fun z=> U z i y) l; have hu:= Ūm σ hx; have hz:S.length=P.card:=length_sort ..
 rw [←hz]; apply Shelf_adapt (U:=SnowPack σ C S L) X (fun i y p=> Eq.symm (fluid_Z σ C _ ((h i y p).1) _ hx))
 refine LensBudget X σ C k v q S (fun l z=>d l ?_ ?_)
 · unfold ψS; rw [z]; exact hu
 exact ((List.length_map (f:=σ) (as:=l)).symm.trans (by rw [z,List.length_map])).trans hz -- tune
-- aggregate in K3. using `snow` 
variable {G:Finset I →  Z → D → E}{η κ Cκ:ℝ}{m:ℕ}{S:Finset (Finset I)} {c:Site N}
variable (h:Ledges X σ G)(u:S⊆realm_C σ)(P:∀ i∈S,ShelfK X (G i) b (a+1/8) (η^i.card*V))(p:0≤Cκ)(pk:1 ≤Cκ*η)(p₀:0<η)(hv:lamp_B (cape_B b) b m σ)(ρ: Apex (cape_B b) b σ)(hq: Nice_B b m (Cκ*η) (1/32))(Hb:8 ≤ b)(Ht:0≤V)
include h u P
private lemma Pledge :∃ F: Finset I →  Z →  ℝ,(∀ i∈S,∀ j,X.Lux j (G i j) (F i j)) ∧(∀ i∈S,∀ j,F i j≠0  →  i∈realm_C σ ∧ poke_F σ (X.Φ j) i)∧(∀ i∈S,∀ x:Site N,(∑ j∈ univ.filter (fun y=>x∈X.Φ y), dra_k b (a+1/8) (X.Φ j)*F i j) ≤ η^i.card * V):=by
 choose! W A q using P
 let F(i:Finset I)(j:Z):= if (∀ y,X.valid j y →  G i j y=0) then 0 else W i j; refine ⟨F,?_,?_,?_⟩
 · intro i t j; unfold F; split
   · next e=>exact X.zero j _ e
   exact A i t j
 · intro i r j x; refine ⟨u r,?_⟩; have hv:¬∀ y,X.valid j y  →  G i j y=0:=fun p=>x (if_pos p); push Not at hv; obtain ⟨y,v,z⟩:=hv; exact (h j y v i z).2 -- push
 intro i x j; apply le_trans _ (q i x j); apply sum_le_sum; intro s _; refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le; unfold F; split; exact X.posG _ _ _ (A _ x _); exact le_rfl
-- general with two (`keep silent outside reservoir`). aggregate Kraft nonzero counts.
omit h u P
variable {F:Finset I →  Z → ℝ}(y:∀ i∈S,∀ j,F i j≠0 → i∈realm_C σ ∧ poke_F σ (X.Φ j) i)
variable (q: ∀ i∈ S,∀ j,X.Lux j (G i j) (F i j)) (t:∀ i∈S,∀ x:Site N,(∑ j∈univ.filter (fun y=>x∈X.Φ y),dra_k b (a+1/8) (X.Φ j)*F i j) ≤η^i.card * V) (x:Site N)
abbrev reshape_Q (F: Finset I → Z → ℝ)(x:Site N)(y:ℝ)(i:Finset I)(j:Z):= if x∈ X.Φ j then (F i j)/(y^i.card) else 0
include p₀ q
lemma Shape_pos (i:Finset I)(w:i∈ S) : 0 ≤ reshape_Q X F x η i:=by intro j; unfold reshape_Q; split; exact div_nonneg (X.posG _ _ _ (q _ w j)) (by positivity); exact le_rfl
include y
lemma Shape_on (i:Finset I)(w:i∈ S)(j:Z)(t:reshape_Q X F x η i j≠0) : x∈ X.Φ j ∧ poke_F σ (X.Φ j) i:=by
 unfold reshape_Q at t; split at t
 · next hv=> exact ⟨hv,(y i w j (fun v=>by rw [v,zero_div] at t; exact t rfl)).2⟩
 exact False.elim (t rfl)
omit y
include t
lemma Shape_paid (i: Finset I)(w:i∈ S) : ∑ j:Z,dra_k b (a+1/8) (X.Φ j)*reshape_Q X F x η i j ≤ V:=by
 unfold reshape_Q; simp_rw [mul_ite,mul_zero, ←mul_div_assoc,←Finset.sum_filter]; rw [←Finset.sum_div _ _ _,div_le_iff₀ (by positivity),mul_comm V]; exact t _ w x
include p h u P pk hv hq Hb Ht
omit t q
section
omit p h u P pk hv hq Hb Ht
lemma Shape_price (F:Finset I →  Z → ℝ)(a r:ℝ)(x:Site N)(b:ℕ)(i: Finset I) :r^i.card* (∑ y∈ univ.filter (fun y=>x∈X.Φ y),dra_k b a (X.Φ y)*F i y)= (r*η)^i.card*(∑ j:Z,dra_k b a (X.Φ j)*reshape_Q X F x η i j):=by
 unfold reshape_Q; simp_rw [mul_ite,mul_zero, ←mul_div_assoc,←Finset.sum_filter]; rw [←Finset.sum_div _ _ _,mul_pow]; field_simp
end
include ρ
lemma Book_many (e:∀ i∈ S,1 < i.card): BookT X G b S a Cκ (hope_E b V):=by
 obtain ⟨F,A,q,k⟩:= Pledge X σ h u P; refine ⟨F,A,fun x=>?_⟩; simp_rw [Shape_price X p₀] -- tune order
 exact manyτ σ x X.Φ _ S (Shape_pos X p₀ A x) (Shape_on X σ p₀ q A x) pk Hb ρ hv hq V (Shape_paid _ p₀ A k x) Ht (fun i p=> (mem_filter.mp (u p)).2) e -- order
omit ρ
lemma Book_single (e:∀ i∈ S,i.card=1): BookT X G b S a Cκ (m*(Cκ*η)*V+hope_E b V):=by
 obtain ⟨F,A,q,k⟩:=Pledge X σ h u P; refine ⟨F,A,fun x=>?_⟩; simp_rw [Shape_price X p₀]; exact tinyτ σ x X.Φ _ S (Shape_pos X p₀ A x) (Shape_on X σ p₀ q A x) pk Hb hv hq V (Shape_paid _ p₀ A k x) Ht e
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
