import ZecaJasper
import YM.SU5.FiniteGaugeData.Poin.Sonic
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Fresco
open Poin Vp.Folio Vp.Tufa Mink General Lorentz 
variable {H:Hilbert}{ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:Bench S)
 (hΩ:∀ x:E4,M S x Ω.val=Ω.val)
 (D:G.Tile S Ω) (k:Celeritas.Cinema S)
 (b:Axis)(h:b≠timeAxis)(p:SO)(r:Reigns p b)
local notation "Z"=>Ω.val
local notation "τ"=>timeAxis
local notation "χ"=>Item G.Chip
local notation "ψ"=> wordValue S Z G.dep G.grade
variable (u v:G.Chip)(L R:List (Item G.Chip))(d:ℝ)(s δ:ℝ≥0)
local notation "A"=>G.dep u
local notation "B"=>G.dep v
local notation "m"=>G.grade u
local notation "n"=>G.grade v
local notation "Φ"=>face S Z G.dep G.grade
local notation "Β"=>role S Z G.dep G.grade
local notation "X"=> Β (-2) L
local notation "Y"=> Φ 2 R
variable (q:E4)(w:ℝ)(z:ℂ)


open Boundary
local notation "tm" t:max=> t • basis timeAxis
include hΩ h in lemma extraL(k:BackE τ 0 L)(p:BackE b (-1) L):
   ∃ L', BackE τ (-2) L' ∧ BackE b (-1) L' ∧ Β (-2) L'=Β 0 L:=by
 refine ⟨shifted (tm (-2:ℝ)) L, ?_,?_,?_⟩
 · have g:=tailL' (tm (-2:ℝ)) 0 L k
   rw [zero_add,clock_a] at g; exact g
 · have g:=tailL' (tm (-2:ℝ)) (-1) L p
   rw [show (tm (-2:ℝ)) b=0 by simp [h],add_zero] at g;exact g
 have g:=vlatter S Z hΩ G.dep G.grade (tm (-2:ℝ)) 0 L k
 rw [zero_add,clock_a,clock_sep] at g
 exact g.trans (DFunLike.congr_fun (tini S) _)
include hΩ h in lemma extraR(k:LaneE τ 0 R)(p:LaneE b d R):
   ∃ R', LaneE τ 2 R' ∧ LaneE b d R' ∧ Φ 2 R'=Φ 0 R:=by
 have g:=clock_face S G Z hΩ 2 0 R k
 rw [zero_add] at g
 refine ⟨_,g.1,?_,g.2⟩
 have o:=headL' (tm (2:ℝ)) d R p
 rw [show (tm (2:ℝ)) b=0 by simp [h],add_zero] at o; exact o

variable (fl:Filled S G Ω.val)(e:0<s)(a:0<δ)(f g:Test4)
include hΩ D fl h e a
lemma mural₀(i:∀ q∈tsupport g,Segment b d s δ q)(x y:Bench S):
     DotComm S A B 0 g m n x y:=by
  let k:=petals S G Ω hΩ fl D
  obtain ⟨p,r⟩:=InMeets b
  apply arriere S A B _ _ _ _ _ _ _ _
    (southWest S G Z hΩ b h (-1) k fl) (southRise S G Z hΩ b h d k fl)
  rintro _ ⟨L,l',l,rfl⟩ _ ⟨R,g',g₁,rfl⟩
  obtain ⟨L',t,t',α⟩:=extraL S G Ω hΩ b h L l' l
  obtain ⟨R',q,q',β⟩:=extraR S G Ω hΩ b h R d g' g₁
  rw [←α,←β]
  exact agate S G Ω hΩ D k b h p r u v L' R' d s δ
       ⟨t,q⟩ ⟨t',q'⟩ e a g i

lemma mural (T:ℝ) (i:tsupport f ×ˢ tsupport g ⊆ Mint.PriceX b s δ T):
     (ℑ S A f m).comp (ℑ S B g n)=(ℑ S B g n).comp (ℑ S A f m):=by
  apply Eff
  intro o u' x y
  apply yank S A B _ _ _ _ _ _ o
  rw [sub_self];intro x y
  apply mural₀ S G Ω hΩ D b h u v (T-o b+(s:ℝ)+δ) s δ fl e a
  intro q hq

  have t:q+o∈tsupport g:=by simpa using route (-o) g hq
  have α:(s:ℝ)+(δ:ℝ)<(q+o) b-o b:=(i (Set.mk_mem_prod u' t)).2.1
  have β:(q+o) b<T:=(i (Set.mk_mem_prod u' t)).2.2.1
  have γ:|o τ-(q+o) τ|<(s:ℝ):=(i (Set.mk_mem_prod u' t)).1
  rw [PiLp.add_apply] at α β γ
  rw [abs_sub_comm,add_sub_cancel_right] at γ; rw [add_sub_cancel_right] at α
  exact ⟨α.le,by linarith only [β],γ⟩
omit h e a
lemma fresco : G.Loom S Ω:=by
 constructor
 intro u v f g b s δ T h e a i
 have k:=mural S G Ω hΩ D b h u v s δ fl e a f g T i
 ext1 x
 exact Subtype.ext (DFunLike.congr_fun k x.val)
#print axioms fresco
