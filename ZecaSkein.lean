import ZecaTrellis
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Vp.Folio
variable {H:Hilbert}(S:OS.Semigroup H timeAxis){α:Type}(A:α→H.Op)(ν:α→ℕ)(Ω:H)
 (hΩ:∀ x:E4,M S x Ω=Ω)
local notation "χ"=> Item α
local notation "F'"=> face S Ω A ν
local notation "B'"=> role S Ω A ν
local notation "ψ"=> wordValue S Ω A ν
local notation "t"=>timeAxis

include hΩ
lemma part₀ (L R:List χ)
 (k:BackE t 0 L)(r:LaneE t 0 R) :
 ψ (L++R)= inner ℂ (B' 0 L) (F' 0 R):=by
 have v:=rho_join S Ω hΩ A ν 0 L R (le_refl _) k r
 rw [show (0:E4) t=(0:ℝ) from rfl, Real.toNNReal_zero,map_zero, S.eZero,
     show shifted 0 R=R from ?_, S.uZero] at v
 · exact v.symm
 unfold shifted shift; simp
omit hΩ in lemma junction {a:Axis}(s:ℝ)(L R:List χ)
    (k:BackE a s L)(r:LaneE a s R) : ahead a (L++R):=
 List.pairwise_append.mpr ⟨k.1,r.1,fun u h v p=>lt_trans (k.2 _ h) (r.2 _ p)⟩

lemma partcut (s:ℝ)(L R:List χ)(k:BackE t s L)(r:LaneE t s R) :
 ψ (L++R)= inner ℂ (B' s L) (F' s R):=by
 let p:= -s • basis t
 have e:s+p t=0:=by simp [p]
 have w:M S (SEP t p).val=1:= by rw [show (SEP t p).val=0 from (by change p-p t • basis t=0; simp [p]),tini]
 have v:=vfront S Ω hΩ A ν p s R r
 have u:=vlatter S Ω hΩ A ν p s L k
 rw [e,w] at v u
 have h:=junction s L R k r
 rw [←originIn S Ω hΩ A ν p (L++R) h,show shifted p (L++R)=shifted p L++shifted p R from List.map_append,
   part₀ S A ν Ω hΩ _ _ (e ▸ tailL' p s L k) (e ▸ headL' p s R r), v,u];rfl
local notation "τ"=>timesA
omit hΩ in lemma flyTail (a:Axis)(s c:ℝ)(L:List χ)(u:χ)
    (k:BackE a c L)(p:c<τ a u)(q:τ a u<s): BackE a s (L++[u]):= by
 refine ⟨LastX L u ⟨k.1,fun x h=>lt_trans (k.2 _ h) p⟩,fun x h=>?_⟩
 rcases List.mem_append.mp h with v|v
 · exact lt_trans (k.2 x v) (lt_trans p q)
 exact (List.mem_singleton.mp v) ▸ q

omit hΩ in lemma flyHead (a:Axis)(s d:ℝ)(R:List χ)(u:χ)
    (r:LaneE a d R)(q:s<τ a u)(p:τ a u<d): LaneE a s (u::R):= by
 refine ⟨List.pairwise_cons.mpr ⟨fun x h=>lt_trans p (r.2 _ h),r.1⟩,fun x h=>?_⟩
 rcases List.mem_cons.mp h with v|v
 · exact v ▸ q
 exact lt_trans (lt_trans q p) (r.2 x v)
abbrev TwoPlus (L R:List (Item α))(u v:Item α):= (L++[u])++(v::R)
structure SpaceFor (a:Axis)(c d:ℝ)(L R:List χ)(u v:χ):Prop where
 prefix_ok: BackE a c L
 suffix_ok: LaneE a d R
 before': c<τ a u
 gap': τ a u<τ a v
 after': τ a v<d

omit hΩ in lemma SpaceFor.sprint {a:Axis}{c d:ℝ}{L R:List χ}{u v:χ}(g:SpaceFor a c d L R u v): ahead a (TwoPlus L R u v):= by
  have p:=g.gap'; let i:=(τ a u+τ a v)/2
  have w: τ a u < i :=by unfold i; linarith only [p]
  have z: i<τ a v:=by unfold i; linarith only [p]
  exact junction i _ _ (flyTail a _ _ L _ g.prefix_ok g.before' w)
      (flyHead _ _ _ R _ g.suffix_ok z g.after')

local notation "C"=>leanX S
local notation "K"=>stamps S A

lemma partpair (c d:ℝ)(L R:List χ)(u v:χ)(p: SpaceFor t c d L R u v):
 ψ (TwoPlus L R u v)= inner ℂ (B' c L)
     ((C (τ t u-c) (ν u.1) * K u * C (τ t v-τ t u) (ν u.1+ν v.1) * K v * C (d-τ t v) (ν v.1))
         (F' d R)):=by
 obtain ⟨k,r,g,w,e⟩:=p
 let i:=(τ t u+τ t v)/2
 have β: τ t u < i :=by unfold i; linarith only [w]
 have γ: i<τ t v:=by unfold i; linarith only [w]
 unfold TwoPlus
 rw [partcut S A ν Ω hΩ i _ _ (flyTail _ _ _ L u k g β) (flyHead _ _ _ R v r γ e),
   backTicket S A ν Ω hΩ _ _ _ _ g k, frontTicket S A ν Ω hΩ _ _ _ _ e r,
    show τ t v-τ t u= i-τ t u+(τ t v-i) by ring,←combineP S _ _ (sub_pos.mpr β) (sub_pos.mpr γ)]
 exact ContinuousLinearMap.adjoint_inner_left ..
#print axioms partpair
