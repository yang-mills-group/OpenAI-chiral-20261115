import YM.CF.BProof.Shore.Score
-- commission. retained iff ALL good in support. punctured edges via one-shot console.
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Metric Finset Lattice Wilson Nest Stave Gallery
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
open Wool
variable {T:Tray (Floor q) ε}{F:Drum (rollup q T) (Floor q)}
variable {A:Score n q}(U:Config SU.group n)(W:Writ q T s l u a b δ d θ F)(B:Seal A s l b a)
local notation "𝓖"=>T.house (Fin q)
local notation "hΨ"=>team s l u T A U
local notation "Ω"=>A.cur.native A.orderC U
local notation "Hκ"=> sound s l u U
local notation "Τ"=> tagger s l u T A U
local notation "ζF"=>caught s l u A U
local notation "ξμ"=>Key T A U
include B
lemma both_size{x y:Sκ}(h:separation x y ≤1){i:Sκ}(u:i∈ A.fine.both x y): separation x i ≤ Z*l+1:=by
 obtain p|p:=mem_union.mp u; exact le_trans (B.mi.mom x i p) (by omega); apply (separation_triangle x y i).trans; have g:= B.mi.mom y i p; omega
lemma together{x y:Sκ}(h:separation x y ≤ 1): Set.InjOn (Key T A U) (A.fine.both x y):=fun i hi j hj p=> B.mi.distinct x y h hi hj (congrArg Prod.fst p)
lemma union_map{x y:Sκ}(h:separation x y≤1): (𝓖).adm (team s l u T A U x y):=by
 intro i hi j hj p; obtain ⟨i,(v:i ∈ (A.fine.both x y).filter Hκ),rfl⟩:=mem_image.mp (show i∈hΨ x y from hi); obtain ⟨j,w,rfl⟩:=mem_image.mp (show j∈hΨ x y from hj)
 exact congrArg (Key T A U) (B.mi.distinct x y h (mem_filter.mp v).1 (mem_filter.mp w).1 p)
lemma pose_cost {i:Sκ} : Like ε ((𝓖).car (Key T A U i)) (A.cur.native A.orderC U i):= Like.starts (T.budget _ _ (Wool.frame A.orderC U B.ch _)).le -- tune
include W
lemma march_g {x y:Sκ}(h:separation x y≤ gapR l)(g:sound s l u U x):Like (θ-2*ε) (Ω x) (Ω y):= (Wool.chargeMat B.ch A.orderC U W.hC B.small W.hδ.le W.err x y h g).weaken W.fees
lemma glue0{x y:Sκ}(h:separation x y≤1){i j:Sκ}(p:i∈ A.fine.both x y)(q:j∈ A.fine.both x y)(g:sound s l u U i): Like θ ((𝓖).car (Key T A U i)) ((𝓖).car (Key T A U j)):=by
 have hm:=both_size B h p; have hz:=both_size B h q; have hv:separation i j ≤ gapR l:=by apply (separation_triangle i x j).trans; unfold gapR; rw [separation_comm i x]; omega
 exact (((pose_cost U B).trans (march_g U W B hv g)).trans (pose_cost U B).symm).weaken (le_of_eq (by ring))
lemma challenge{x y:Sκ}(h:separation x y≤1): (𝓖).tonic θ (team s l u T A U x y):=by
 constructor; exact union_map U B h; intro i hi j hj; obtain ⟨i,v,rfl⟩:= mem_image.mp hi; obtain ⟨j,w,rfl⟩:= mem_image.mp hj; exact glue0 U W B h (mem_filter.mp v).1 (mem_filter.mp w).1 (mem_filter.mp v).2
omit W
lemma contest{x y:Sκ}(h:separation x y≤1)(p: ¬(ζF x∧ζF y)): (hΨ x y).card ≤4:=by
 apply Finset.card_image_le.trans (_ : ((A.fine.both x y).filter Hκ).card≤4); have t:=B.mi.mar x y h; have u: #((A.fine.both x y).filter Hκ)< #(A.fine.both x y):=by
    apply card_lt_card ⟨filter_subset .., ?_⟩; intro g; exact p ⟨fun i hi=> mem_filter.mp (g (mem_union_left _ hi))|>.2, fun i hi=>mem_filter.mp (g (mem_union_right _ hi))|>.2⟩
 omega
lemma pool_tap(x y:Sκ): Fuse (hΨ x y) (Τ x) ∧ Fuse (hΨ x y) (Τ y):=by
 unfold team tagger; constructor
 · convert! traffic ((B.mi.deals x).mono (T:=A.fine.both x y) subset_union_left) Hκ ξμ using 1; congr!
 convert! traffic ((B.mi.deals y).mono (T:=A.fine.both x y) subset_union_right) Hκ ξμ using 1; congr!
lemma spark_flow{x y:Sκ}(p:separation x y≤1): dist (Τ x) (Τ y)≤a:=by
 let X:= A.fine; have h : dist (X.wheel x) (X.wheel y) ≤ a:= (dist_pi_le_iff (le_trans (abs_nonneg _) (B.mi.decal x y p x))).mpr (fun i=>B.mi.decal _ _ p i)
 apply flows ((B.mi.deals x).mono (T:=A.fine.both x y) subset_union_left) ((B.mi.deals y).mono (T:=A.fine.both x y) subset_union_right) h (together U B p)
include W
lemma stand{x y:Sκ}(p:separation x y≤1)(h:¬(ζF x∧ζF y)): Like d (dummy F (Τ x)) (dummy F (Τ y)):= Like.starts (W.gleam _ (challenge U W B p) (contest U B p h) _ _ (pool_tap U B x y|>.1) (pool_tap U B x y|>.2) (spark_flow U B p)) -- tune
lemma ray0{x y:Sκ}(p:separation x y≤1)(h:ζF x)(v: # (hΨ x y)≤4): Like (θ+d) (lower (Ω x)) (dummy F (Τ x)):=by
 have hm:tome (Τ x)=1:=depot (B.mi.deals x) _ h; obtain ⟨i,g⟩:=(B.mi.deals x).nonempty
 have hi:Fuse _ (Τ x):= (pool_tap (T:=T) U B x y).1; have he : Sim (hΨ x y) (Τ x):= ⟨hi.pos,hi.ht,hm⟩; have hu : ξμ i∈hΨ x y:=mem_image_of_mem _ (mem_filter.mpr ⟨mem_union_left _ g,h i g⟩)
 have ht:= W.book.kit _ (challenge U W B p) v; rw [marker hm]; have hn:=W.pe.le
 refine Like.pad (((march_g U W B (x:=i) (y:=x) (by have hh:=B.mi.mom x i g; rw [separation_comm]; unfold gapR; omega) (h i g)).symm.trans ((pose_cost U B).symm.trans (ht.fee he _ hu))).weaken ?_); linarith
omit W
lemma commissioned{x:Sκ}(h:ζF x) : Clear u (Wool.saved s) U x:=by obtain ⟨i,g⟩:=(B.mi.deals x).nonempty; exact clear_m (h i g) ((separation_comm ..).trans_le (B.mi.mom _ _ g)) (by unfold Radius gapR palm; omega) -- uses W? δ u implicit.
end Score
end YM.CF.BProof.Mesh.Shore
