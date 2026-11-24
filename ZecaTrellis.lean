import YM.SU5.FiniteGaugeData.Maypole.Vagabond
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Vp.Folio
variable {H:Hilbert}(S:OS.Semigroup H timeAxis)
    {α:Type}(A:α→H.Op)(ν:α→ℕ)(Ω:H.space)(hΩ:∀x:E4,M S x Ω=Ω)
    (s t:ℝ)(u: Item α)(L:List (Item α))

local notation "a"=>timeAxis
local notation "τ"=>timesA timeAxis
local notation "C"=>leanX S
local notation "F"=>legis S A ν
local notation "φ"=>face S Ω A ν
local notation "ψ"=>role S Ω A ν

omit Ω hΩ A ν in
lemma combineP (x y:ℝ)(p:0<x)(q:0<y)(m n:ℕ) : leanX S x m * leanX S y n = leanX S (x+y) (m+n) := by
  have k:= invest (S:=S) (n:=m) (k:=n) p (le_refl 0) q
  rw [Real.toNNReal_zero,S.eZero,show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl,mul_one,add_zero] at k
  exact k

include hΩ
lemma frontTicket (q:τ u < t)(l:LaneE a t L):
 φ s (u::L)= (C (τ u-s) (ν u.1) * stamps S A u * C (t-τ u) (ν u.1))
     (φ t L):= by
 rw [face, Front, budgetFoot, zero_add]
 cases L with
 | nil=>
   rw [legis,solitary]
   exact (congrArg (C (τ u-s) (ν u.1)*stamps S A u)
        (earnO S Ω hΩ (t-τ u) (n:=ν u.1) (sub_pos.mpr q)).symm)
 | cons j L=>
   rw [face, Front, budgetFoot,zero_add]
   let X:=C (t-τ u) (ν u.1); let Y:=C (τ j-t) (ν j.1)
   have he:X*Y=gapK S ν u j:=by
     unfold X Y;rw [combineP S _ _ (sub_pos.mpr q) (sub_pos.mpr (l.2 j List.mem_cons_self)),
                show t - τ u + (τ j-t)=τ j-τ u by ring];rfl
   rw [←show F [u]=stamps S A u from solitary ..,
       show F (u::j::L) = F [u]*gapK S ν u j*F (j::L) from joiningF _ _ [] L u j, ←he]
   simp only [mul_assoc]; rfl

lemma backTicket (q:t<τ u)(l:BackE a t L):
 ψ s (L++[u])= star (C (τ u-t) (ν u.1) * stamps S A u * C (s-τ u) (ν u.1)) (ψ t L):= by
 rw [role, Back, budgetBack, add_zero]
 induction L using List.reverseRecOn with
 | nil=>
   rw [List.nil_append,legis, solitary]
   rw [mul_assoc (C (τ u - t) _),star_mul (C (τ u - t) _),
       show star (C (τ u - t) (ν u.1))= C (τ u - t) (ν u.1) from warm_a S _ (sub_pos.mpr q)]
   rw [show ψ t []=Ω from (by change (star (1 * 1:H.Op)) Ω=Ω;rw [one_mul,star_one];rfl)]
   exact congrArg ((star (stamps S A u * C (s-τ u) (ν u.1)) : H.Op)) (earnO S Ω hΩ _ (n:=ν u.1)
        (sub_pos.mpr q)).symm
 | append_singleton L j ih=>
   rw [role, Back,budgetBack,add_zero]
   let X:= C (τ u-t) (ν u.1);let Y:=C (t-τ j) (ν j.1)
   have he:Y*X=gapK S ν j u:=by
     unfold Y X;rw [combineP S _ _ (sub_pos.mpr (l.2 j (by simp))) (sub_pos.mpr q),
                    show t - τ j+(τ u-t)=τ u-τ j by ring];rfl
   rw [←show F [u]=stamps S A u from solitary .., show F ((L++[j])++[u])= _ from joiningF _ _ L [] j u,←he]
   rw [←show (F (L++[j])*Y)*(X*F [u]* C (s-τ u) (ν u.1))= F (L++[j])*(Y*X)*F [u]*C (s-τ u) _ from (by simp only [mul_assoc]),star_mul];rfl

lemma frontHot (r:s<t)(k:LaneE a t L):
 φ s L= S.E (t-s).toNNReal (φ t L):= by
   have h:0<t-s:=sub_pos.mpr r
   cases L with
   | nil=>exact (shed S Ω hΩ _).symm
   | cons j L=>
     have he:leanX S (t-s) 0=S.E (t-s).toNNReal:=S.roots_heat (Real.toNNReal_pos.mpr h)
     rw [face,face,Front,Front,budgetFoot,budgetFoot,zero_add,←he]
     change C (τ j-s) _ (_)=C (t-s) 0 (C (τ j-t) (ν j.1) _)
     have v:=combineP S _ _ h (sub_pos.mpr (k.2 j List.mem_cons_self)) 0 (ν j.1)
     rw [show t-s+(τ j-t)=τ j-s by ring,zero_add] at v
     exact (DFunLike.congr_fun v _).symm
