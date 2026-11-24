import YM.SU5.FiniteGaugeData.Cirrus.Braise
import YM.SU5.FiniteGaugeData.Cirrus.Muque
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J:Set ι)
local notation "D"=> G.Model S Ω
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Ω₁"=>G.focus S Ω []
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (T:H.Op) (A B:Effort S Ω G) (Pn:Boundary.Action H)(L:G.Arrival S Ω Pn)
local notation "T₂"=> DualR S Ω G
local notation "W"=> actionAt S Ω G Pn L
open Metric
lemma globe (p:A∈ Hull S Ω G J univ) : ∃ r:ℝ,0<r∧A∈ Kₐ J (ball 0 r):= by
 have he(r s:ℝ)(p:r ≤ s): Kₐ J (ball 0 r)≤ Kₐ J (ball 0 s):= regi S Ω G J J _ _ (_root_.subset_refl _) (ball_subset_ball p)
 refine Algebra.adjoin_induction (p:=fun A _=> ∃ r:ℝ,0<r∧ A∈ Kₐ J (ball 0 r)) ?_ ?_ ?_ ?_ p
 · rintro a ⟨t,v,rfl⟩; obtain ⟨r,h⟩:= v.2.1.isBounded.subset_ball (0:E4); exact ⟨max r 1,zero_lt_one.trans_le (le_max_right _ _),seeds S Ω G J _ _ ⟨v.1,v.2.1,_root_.subset_trans h (ball_subset_ball (le_max_left ..))⟩⟩
 · intro r; exact ⟨1,zero_lt_one, (Kₐ J _).algebraMap_mem _⟩
 · rintro x y _ _ ⟨v,p,h⟩ ⟨t,q,z⟩; exact ⟨v+t,add_pos p q,(Kₐ J _).add_mem (he _ _ (by linarith) h) (he _ _ (by linarith) z)⟩
 rintro x y _ _ ⟨v,p,h⟩ ⟨t,q,z⟩; exact ⟨v+t,add_pos p q,(Kₐ J _).mul_mem (he _ _ (by linarith) h) (he _ _ (by linarith) z)⟩
local notation "S₁"=> Hull S Ω G Set.univ Set.univ
-- operator vacuum weak irreducible core.B evaluates ACTUAL W's
abbrev weakR :Prop:= ∀ A B:Effort S Ω G, A∈ Hull S Ω G Set.univ Set.univ→ B∈ Hull S Ω G Set.univ Set.univ→ DualR S Ω G A B→ ∀ x y: D,inner ℂ (E (A x)) (T (E y))=inner ℂ (E x) (T (E (B y)))
variable (hΩ:∀ x:E4,M S x Ω.val=Ω.val)
variable (v:weakR S Ω G T)
include v L
local notation "P₀"=> T Ω.val
lemma fixing (p:A∈ S₁) (x:E4) : inner ℂ (E (A Ω₁)) (M S x (T Ω.val))=inner ℂ (E (A Ω₁)) (T Ω.val):=by
 obtain ⟨B,q,u⟩:= reserve S Ω G _ _ A Pn L p
 let z:= T Ω.val; let f(A:X):H:=G.lens S Ω (A (G.focus S Ω [])); let F:= f A; let G':= (innerSL ℂ Ω.val).comp T; let y(_ :X):H:= E (B Ω₁)
 refine palindrome S (innerSL ℂ F) G' z (y B) Pn L.time ?_ x
 intro a; let Q:= Poincare.translation (-a); let g:= actW S Ω G Pn L Q; let R:= W Q
 have he(T:X) : M S (-a) (f T)= f (R T):=by rw [← L.time]; apply (L.respect Q (T Ω₁)).trans; exact congrArg (G.lens S Ω) (show g (T Ω₁)= (R T) Ω₁ from (pitchAct S Ω G T Pn Q L Ω₁).symm.trans (congrArg (fun x=>W Q T x) (vω S Ω G Pn Q L)))
 have hp(T:X)(p:T∈ Hull S Ω G univ univ): R T∈ S₁:= regi S Ω G _ _ _ _ (_root_.subset_refl _) (Set.subset_univ _) (climbs S Ω G _ _ T Pn Q L p)
 change inner ℂ F (M S a z)= inner ℂ Ω.val (T (M S (-a) (f B))); rw [tboth,he]; rw [he]; exact v _ _ (hp A p) (hp B q) (inherits S Ω G A B Pn Q L u) Ω₁ Ω₁
include hΩ
variable (h:∀ x:H.space,(∀ p:E4,M S p x=x)→∃ z:ℂ,x=z• Ω.val)
include h
lemma scalarB : ∃ c:ℂ,T = c • 1:=by
 let Z:=(Hull S Ω G Set.univ Set.univ); let F:= Sales S Ω G Set.univ Set.univ; let k:= blessed S Ω G Set.univ Pn L hΩ isOpen_univ Set.univ_nonempty; have he(p:E4):M S p (T Ω.val)=T Ω.val:= k.eq_of_inner_right ℂ fun A=> fixing S Ω G T A.val Pn L v A.property p
 obtain ⟨s,t⟩:= h _ he; use s; let P:H.Op:= s•1; apply DFunLike.coe_injective; apply k.equalizer T.continuous P.continuous; funext A; obtain ⟨B,q,y⟩:= reserve S Ω G _ _ _ Pn L A.property; apply L.dense.eq_of_inner_right ℂ; intro x; change inner ℂ (E x) (T (F A))=inner ℂ _ (s • (F A)); rw [← show inner ℂ (E (B x)) (T Ω.val)= inner ℂ (E x) (T (F A)) from v B A.val q A.property (twoSide S Ω G A.val B y) x Ω₁,t, inner_smul_right,inner_smul_right, ←show inner ℂ (E x) (F A)= inner ℂ (E (B x)) Ω.val from ((twoSide S Ω G A.val B y) x Ω₁).symm];
#print axioms globe
#print axioms scalarB
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
