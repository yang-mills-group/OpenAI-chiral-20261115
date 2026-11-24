import YM.SU5.Reconstruction.Based.Reports
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
set_option quotPrecheck false
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
open SlabMark Finset Fock Lat Laurent Cube Spire Vale Pastry Peaks Dial Phase Lifted Skye Tenant Rush Tulip Girt Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
namespace LineCharge
open Rooted
variable (s:ℕ)(j:Axis)(C: ∀ j,Arena Y H G.history.circuit j 0 false)
variable (χ:displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ]ℂ)
variable (p q:Cover) (S:Finset Cover)(z:SU.Slot)(o:Cover)(u d:ℕ)
variable (f:Marks (tent Y H) true)(δ:ℝ)
local notation "κ" => sameRead Y H V G j (C j) χ s
local notation "J" => Multiset Cover
local notation "Z" => fromStrict f
local notation "R" => rect S
local notation "W" => booty o d u
local notation "lp" => FirstWindows.leg («J»:=tent Y H) j p -- J macro
local notation "rq" => reposition (tent Y H) q
local notation "S₁" => reflectedBox j 0 (streetBox (tent Y H) p (rect S))
local notation "S₂" => streetBox (tent Y H) q (rect S)
local notation "C₁" => bufferedHull Λ l s (reflectedBox j 0 (streetBox (tent Y H) p (rect S)))
local notation "C₂" => bufferedHull Λ l s (streetBox (tent Y H) q (rect S))
-- Analyst; keep the queries in actual epoch. Strong gauge identity on y.
lemma actor_roll {g:Marks (tent Y H) true}(h:g.val∈ Filigree K (Window.family z) (booty o d u) S):
    ∃ (A:Finset (Multiset Cover))(a:Multiset Cover→Dome (tent Y H)), fromStrict g=∑ x∈ A,a x∧ ∀x∈ A, Digest z W S x (a x):= by
 obtain ⟨A,p⟩:= exists_profiles (tent Y H) (Window.family z) W h
 have ht(x) := (FilTest (visible K _ _ x _ (p.1 x))).widen
 let a(x:Multiset Cover): Dome (tent Y H):=⟨_,aux_test (ht x)⟩
 refine ⟨A.support,a,?_,fun x v=> paid_digest z W S (p.1 x) (Finsupp.mem_support_iff.mp v) (paying_single (tent Y H) (Window.family z) _ p ?_ x)⟩ -- g type? explicit `g : S strict` implies
 · apply Subtype.ext; change g.val=(screenHall K).val _; rw [map_sum]; exact p.2.symm
 exact (marksSpec true _).2 rfl
-- Budget at receipt. In detector witnesses: only assert positions specified. WOT etc as CP1 ff.
noncomputable def same_frame(a b:Dome (tent Y H)):ℂ:= κ (FirstWindows.twin j p q a b)
local notation "Tw"=>same_frame Y H V G s j C χ p q
structure Funds (f g:Dome (tent Y H)):Prop where
 paidDist : ∀ i: Axis, PhysicalHush (Λ:=Λ) (l:=l) s i (reflectedBox j 0 (streetBox K p (rect S))) (streetBox (tent Y H) q (rect S)) δ
 regions : IsCompact (C₁) ∧ IsCompact (C₂) ∧ Disjoint (C₁) (C₂) ∧ ∀ i:Axis, ∀ x∈ C₁,∀ y∈ C₂,x i+δ ≤ y i
 represents: lp f ∈ insideAt Λ l K true (C₁) s ∧ rq g ∈ insideAt Λ l K true (C₂) s
 actual_mul (t:ℕ) (p':s≤ t): spreadTo Y H G s t (lp f*rq g)=spreadTo Y H G s t (lp f)*spreadTo Y H G s t (rq g) ∧
   spreadTo Y H G s t (lp f)∈insideAt Λ l K true (C₁) t∧ spreadTo Y H G s t (rq g)∈insideAt Λ l K true (C₂) t ∧
    sameRead Y H V G j (C j) χ t (spreadTo Y H G s t (lp f)*spreadTo Y H G s t (rq g))= Tw f g
 entire_books: ∀ᶠ n in atTop,∀ t,PhaseChoice.FullDistances (volumeAround Λ l t (S₁∪ S₂)) (Journey.side Y (i (G.rows n)) (s+t))
variable {f' g:Dome (tent Y H)}
lemma afforded (h:∀i:Axis,PhysicalHush (Λ:=Λ) (l:=l) s i (reflectedBox j 0 (streetBox K p S)) (streetBox K q S) δ)(v:Housed Y H G S s j p q f')(w:Housed Y H G S s j p q g): Funds Y H V G s j C χ p q S δ f' g:=by -- order guard
 have ht:= distinct Λ K s j p q h; let r:= separated_disjoint Λ l s S₁ j (ht j)
 have u(t:ℕ)(pf:lp f' ∈ insideAt Λ l K true C₁ s): spreadTo Y H G s t (lp f' * rq g)= _ := spreadTo_separated Y H G pf w.bills_right r
 refine ⟨ht,⟨compact_hull ..,compact_hull ..,r,fun i _ a _ b=>separated_hulls Λ l s S₁ i (ht i) a b⟩, ⟨v.bills_left,w.bills_right⟩, fun t p' => ⟨u t v.bills_left, v.holds_left t p', w.holds_right t p',?_⟩, ((V.pick.grow_i.comp G.history.growsA).tendsto_atTop.eventually (unwrapped Y H s _))⟩
 rw [← u t v.bills_left]; unfold same_frame FirstWindows.twin sameRead; simp only [os_ticket_val]; exact oneAt_spread Y H V G j (C j) χ p' _

structure ValueTag(f g:Dome (tent Y H))(μ ν:Multiset Cover)(N:ℕ): Prop where
 weight: 1/32 ≤ (N:ℝ)^2*‖same_frame Y H V G s j C χ p q f g‖
 supplementary: ∃ ζ:Cover,∀ᶠ m in atTop, let n:= i (G.rows m); let d':=k (G.columns m); Addressable Y H s j ζ (lp f) (rq g) n d' ∧ armTruth Y H (booty o d u) s j p q μ ν f g n d' ζ
 fails : ∃ a b g g', NoDecompose Y H V G j (C j) χ s p q z u d S o a b g g' ∧ bareHop z W S μ a∧bareHop z W S ν b

noncomputable def ChargedCase : Prop:= ∃ (A:Finset (Multiset Cover))(a:Multiset Cover→Dome (tent Y H)), fromStrict f=∑ x∈ A,a x∧ (∀ i∈ A, Digest z (booty o d u) S i (a i) ∧ Housed Y H G S s j p q (a i))∧
    (∀ i∈ A,∀ k∈ A, Funds Y H V G s j C χ p q S δ (a i) (a k)) ∧ κ (lp (fromStrict f)*rq (fromStrict f))=(∑ i∈A,∑ k∈ A, Tw (a i) (a k)) ∧ 1/32 ≤ ‖(∑ i∈A,∑ k∈ A, Tw (a i) (a k))‖ ∧ ∃ μ∈ A,∃ ν∈ A,ValueTag Y H V G s j C χ p q S z o u d (a μ) (a ν) μ ν A.card

/- The WHOLE prescription: every term of this exact sum located in the persistent
physical H₀,H₁ spacing budget, using a WILSON CONNECTION between EACH CHI pair's
annih & EACH of its creation sites as requested. (See Proof note for meaning. Only one
hub choice at a time!) At least one pair of profile pieces also truly produces signal in χ,
and needs nonfactorizing gauge vs matter accounting already on those specific profiles. -/
lemma pay_from_link (h:LinkCheck Y H V G j (C j) χ s p q S z o u d f δ): ChargedCase Y H V G s j C χ p q S z o u d f δ:=by
 obtain ⟨A,a,H₀,t⟩:= actor_roll Y H S z o u d h.base.link.mark_mem
 have u'(i)(w:i∈ A):= housing Y H G z W S s j p q (t i w)
 have Hp:κ (lp (fromStrict f)*rq (fromStrict f)) = ∑ i∈ A,∑ k∈A,Tw (a i) (a k):=by
    rw [H₀]; unfold LineCharge.same_frame FirstWindows.twin sameRead; simp_rw [os_ticket_val]; simp only [map_sum,Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm
 have hK: 1/32 ≤ ‖(∑ i∈A,∑ k∈A,Tw (a i) (a k))‖:=Hp ▸ h.answer -- tune
 let Zz(x:J × J):= Tw (a x.1) (a x.2)
 have hv:(∑ x∈ A ×ˢ A,Zz x) = (∑ i∈ A,∑ k∈ A,Tw (a i) (a k)):= sum_product A A Zz
 obtain ⟨⟨μ,ν⟩,e,v⟩:= Segregate.magnitude (S:=A×ˢ A) Zz (1/32 :ℝ) (by norm_num) (hv.symm ▸ hK)
 have hl: 1/32 ≤ (A.card:ℝ)^2* ‖Tw (a μ) (a ν)‖:=by simpa only [card_product,Nat.cast_mul,sq,Zz] using v
 have hh:Tw (a μ) (a ν)≠0:= fun e => not_le.mpr (lt_of_eq_of_lt (show (A.card:ℝ)^2*‖Tw (a μ) (a ν)‖=0 from (by rw [e,norm_zero,mul_zero])) (by norm_num : (0:ℝ)<1/32)) hl
 obtain ⟨hμ,hν⟩:=(show μ∈ A∧ ν∈ A from mem_product.mp e); let R' := t μ hμ; let X' := t ν hν; let a' := h.base.link.anchor_inj
 refine ⟨A,a,H₀,fun i p=> ⟨t i p,u' i p⟩,fun i hi k p=>afforded Y H V G s j C χ _ _ S δ h.life.shelf.span_positions (u' _ hi) (u' _ p),Hp,hK, μ,hμ,ν,hν,⟨hl, exposure Y H V G z W S s j C χ p q a' hh R' X', bare_no_decompose Y H V G z S s j (C j) χ p q o u d R'.raw_origin X'.raw_origin hh a' (detached_disjoint h.life.shelf.structured)⟩⟩
end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LineCharge.pay_from_link
