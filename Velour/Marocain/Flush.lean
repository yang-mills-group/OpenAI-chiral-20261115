
import Velour.Marocain.Verge
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe

variable {n:ℕ}


local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight
local notation "𝓧" => Fin n → H.Op
local notation "𝒦" => Fin n → ℕ
local notation "𝓕" => Fin n → Test4
local notation "𝓑" => Module.End ℂ D
local notation "𝓗" => H.space

local notation "G!" => S.heatL
local notation "E!" => S.E
local notation "𝓛" => Fin n → ℝ≥0
local notation "𝓣" => Fin n → S.Detector
local notation "𝓠" => Fin n → ℝ≥0 → H.Op

open Velour

def weightedTuple (k:𝒦)(Y:𝓧):= fun i=> S.wrapW (k i) (Y i)
lemma banner_valid (k:𝒦)(Y:𝓧):
   S.banners Y= S.coaches k (S.weightedTuple k Y):=
  (S.banner_invites Y).unique (inviting _ _ (fun _=> LinearMap.ext fun _=>(S.hatch_given ..).symm))

lemma banner_warm (k:𝒦)(Y:𝓧)(l r:𝓛):
 S.banners (S.withWarm Y l r)=
     S.coaches k (S.withWarm (S.weightedTuple k Y) l r):=by
 have e(i:Fin n): S.labelled (S.withWarm Y l r i) =
       S.hatch (S.withWarm (S.weightedTuple k Y) l r i) (k i):=by
    ext1 f
    unfold withWarm weightedTuple
    rw [S.hatch_heat,S.hatch_given,S.heat_right_label,S.heat_left_label]
 exact (S.banner_invites _).unique (inviting _ _ e)


variable {S} {Q:Fin n→ℝ≥0→H.Op} {Y:Fin n→ℕ→H.Op}
     {t:Fin n→S.Detector} {X:Fin n→H.Op} {b:Fin n→ℕ} {A:Fin n→ℝ}

def wingSpan {n:ℕ} (a:Axis)(b:Fin n→ℕ)(p:ℕ)(A:Fin n→ℝ)(F:Joint n):=
    lash a (festers n (easter n b p)) F * (∏i,A i)




lemma warm_coach_cost (h:∀i,‖X i‖≤A i)(b:𝒦)
  (l r:𝓛)(F:Joint n)(p:ℕ)(v:D):
   ‖B p (S.coaches b (S.withWarm X l r) F v)‖ ≤
      wingSpan a b p A F * ‖B (sheaf b+p) v‖:= by
 refine (S.coach_cost ..).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun i _=> le_trans ?_ (h i))
            (lash_price (festers n (easter n b p)) F)) (norm_nonneg _))
 exact ((norm_mul_le ..).trans
    (mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _))).trans
    ((norm_mul_le ..).trans
      (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)))

lemma cortege_cost (h:toasted t)
  (e:∀i,t i=S.hatch (X i) (b i))(w:∀i,‖X i‖≤A i)
  (l r:𝓛)(F:Joint n)(p:ℕ)(v:D):
   ‖B p (cortege h l r F v)‖ ≤ wingSpan a b p A F * ‖B (sheaf b+p) v‖:=by
 rw [cortege_coach h _ _ e]
 exact warm_coach_cost w .. -- first param S implicit? maybe S not inferable

abbrev widths (Y:Fin n→ℕ→H.Op)(k:𝒦):= fun i=>Y i (k i)



lemma wings_width (g:∀i,S.Ribs (Y i) (Q i) (b i) (A i) (X i))
   (l r:𝓛)(k:𝒦)(F:Joint n)(p:ℕ)(v:D):
 ‖B p (S.banners (S.withWarm (widths Y k) l r) F v)‖ ≤
    wingSpan a b p A F * ‖B (sheaf b+p) v‖:=by
 rw [S.banner_warm b]
 exact warm_coach_cost (fun i=> (g i).spent _) ..

theorem surge_ribs (g:∀i,S.Ribs (Y i) (Q i) (b i) (A i) (X i))
   (h:toasted t)(e:∀i,S.Instates (Q i) (t i))
   {L U':ℕ→Fin n→ℝ≥0} {l r:𝓛}
   {k:ℕ→Fin n→ℕ}(p:∀j,Tendsto (fun i=>k i j) atTop atTop)
   (v:Tendsto L atTop (𝓝 l))(u:Tendsto U' atTop (𝓝 r))
   {V:ℕ→Joint n}{F:Joint n}(f:Tendsto V atTop (𝓝 F)):
 S.Surges atTop (fun i=>S.banners (S.withWarm (widths Y (k i)) (L i) (U' i)) (V i))
    (cortege h l r F):=by
 simp_rw [S.banner_warm b,cortege_coach h l r fun j=>(g j).exacts (e j)]
 exact S.coaches_surge (fun j=>
          ((Gleams.warm S (tendsto_pi_nhds.mp v j)).mul 
           ((g j).rattle.glints (p j))).mul (Gleams.warm S (tendsto_pi_nhds.mp u j))) _ f
#print axioms surge_ribs

