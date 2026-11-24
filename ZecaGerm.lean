import YM.SU5.FiniteGaugeData.Poin.Andine
import ZecaSeed
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin
section
variable {H K:Hilbert}(S:OS.Semigroup H timeAxis)(T:OS.Semigroup K timeAxis)
  (f:H.space→L[ℂ] K.space)(w:Weld S T f) (x:H.space)
  {n:ℕ}(p:Points n)
  (A:Fin n→H.Op)(B:Fin n→K.Op)(h: ∀ i (y:H.space), f (A i y)= B i (f y))(d:Fin n→ℕ)
include w h
lemma Weld.film (L:List (Fin n))(g:ProofOrder p timeAxis L):
    f (Film (fun i=>coreSp S (p i) (A i)) (rho S d (clockV timeAxis p)) L x) =
      Film (fun i=> coreSp T (p i) (B i)) (rho T d (clockV timeAxis p)) L (f x):=by
 induction L with
 | nil=>rfl
 | cons i L ih=>
   have v(y:H.space) : f (coreSp S (p i) (A i) y)=coreSp T (p i) (B i) (f y):=by
      change f (M S _ (A i (M S _ _)))=M T _ (B i (M T _ _))
      rw [w.trans, h,w.trans]
   rw [Film_step, Film_step]
   refine (v _).trans (congrArg _ ?_)
   have r := List.pairwise_cons.mp g
   
   change _= clip (rho T d (clockV timeAxis p)) i L (Film (fun i=> coreSp T (p i) (B i)) (rho T d (clockV timeAxis p)) L (f x))
   rw [← ih r.2]
   cases L with
   | nil=>rfl
   | cons j L=>
      exact w.par (dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr (r.1 _ List.mem_cons_self)))) _ _

end
variable {H:Hilbert}{ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:Bench S)
 (hΩ:∀x:E4,M S x Ω.val=Ω.val)
local notation "J"=> Cove S G Ω.val
local notation "T"=> springs S G Ω.val
local notation "N"=> chapel S G Ω.val
local notation "q"=> pilgrimV S G Ω.val

include hΩ
lemma safer (x:E4): M (springs S G Ω.val) x q=q:=Subtype.ext
 ((crystalline S G Ω.val).trans x q|>.trans (hΩ x))

abbrev saint (hΩ:∀x:E4,M S x Ω.val=Ω.val):Bench T:=
 ⟨q,(bench T q).2 fun n=>⟨q,keepO _ _ (rlock T _ (safer S G Ω hΩ)) n⟩⟩
local notation "φ"=>saint S G Ω hΩ

lemma pilgrims_quote {n:ℕ}(x:Points n)(w:Fin n→G.Chip)(L:List (Fin n))(l:ProofOrder x timeAxis L):
    Canopy.Sr N T (saint S G Ω hΩ) x w L=Canopy.Sr G S Ω x w L:=by
  have u:=Weld.film T S _ (crystalline S G Ω.val) q x ((N).senses w) (G.senses w) (fun _ _=>rfl) (G.credit w) L l
  exact congrArg (inner ℂ Ω.val) u

lemma pilgrims_paid (p:Canopy.Tile G S Ω):Canopy.Tile N T (saint S G Ω hΩ):=
 ⟨fun n V x w L L' l r u v=>
     ((pilgrims_quote S G Ω hΩ x w L u).trans (p.turn _ V x w L L' l r u v)).trans
       (pilgrims_quote S G Ω hΩ _ _ _ v).symm⟩
#print axioms pilgrims_paid