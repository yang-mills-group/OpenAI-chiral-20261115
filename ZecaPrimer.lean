import ZecaSpin
import ZecaSkein
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


abbrev axisZero(q:E4):E4:=(SEP timeAxis q).val
abbrev fling(q:E4)(w:ℝ):E4:= (w • basis timeAxis)+axisZero q
lemma flingTime:fling q w τ=w:=by rw [fling,PiLp.add_apply, show axisZero q τ=0 from (SEP τ q).property];simp
lemma flingCast: SEP τ (fling q w)=SEP τ q:= by apply Subtype.ext; change ((fling q w)-(fling q w τ) • basis _)=axisZero q; rw [flingTime,fling]; abel
include h in
lemma zeroSide:(axisZero q) b=q b:=by change (q-(q τ) • basis τ) b=_;simp [Ne.symm h,h]
include h in
lemma flingSide:(fling q w) b=q b:=by simp [fling,h,h.symm,zeroSide b h]
lemma fling_null: stamps S G.dep (u,(0:E4))=A:=by unfold stamps coreSp;rw [map_zero]; change optx S A (0:E4)=A;rw [optx,neg_zero,tini,one_mul,mul_one]
lemma fling_price: stamps S G.dep (v,fling q w)=coreSp S q B:=by unfold stamps coreSp; rw [flingCast]

structure Blast (L R:List χ):Prop where
 aus:BackE timeAxis (-2) L
 al: LaneE timeAxis 2 R
abbrev Pplus (w:ℝ):=TwoPlus L R (u,0) (v,fling q w)
abbrev Pminus (w:ℝ):=TwoPlus L R (v,fling q w) (u,0)
variable (g:Blast G L R)

include g
lemma movesPos(a:0<w)(a':w<2): SpaceFor τ (-2) 2 L R (u,0) (v,fling q w) :=
 ⟨g.aus,g.al,show (-2:ℝ)<0 by norm_num,show (0:ℝ)<(fling q w) τ by rwa [flingTime], show fling q w τ<2 by rwa [flingTime]⟩
lemma movesNeg(a:0<w)(a':w<2): SpaceFor τ (-2) 2 L R (v,fling q (-w)) (u,0) :=
 ⟨g.aus,g.al,show (-2:ℝ)<fling q (-w) τ by rw [flingTime];linarith,
     show fling q (-w) τ<0 by rw [flingTime];linarith, show (0:ℝ)<2 by norm_num⟩
omit g in
lemma realS (i:ℝ)(j:ℂ)(y:ℕ)(a:0≤ i)(c:(i:ℂ)=j): leanX S i y=parabola S y j:=by rw [←c]; exact congrArg _ (congrArg Complex.ofReal (Real.coe_toNNReal i a))

include hΩ
lemma playPos(a:0<w)(a':w<2): backwards S X Y A (coreSp S q B) m n (w:ℂ)=ψ (Pplus G u v L R q w):=by
 rw [Pplus, partpair S G.dep G.grade Z hΩ _ _ _ _ _ _ (movesPos G u v L R q w g a a'), fling_null, fling_price]
 unfold timesA
 rw [flingTime, PiLp.zero_apply, sub_zero, zero_sub, neg_neg] -- maybe hidden toNNReal
 rw [realS S _ w _ a.le rfl,realS S _ (2-(w:ℂ)) _ (sub_nonneg.mpr a'.le) (by push_cast;rfl),leanX,show (2:ℝ).toNNReal=2 by norm_num]
 rfl

lemma playNeg(a:0<w)(a':w<2): forwards S X Y A (coreSp S q B) m n (w:ℂ)=ψ (Pminus G u v L R q (-w)):=by
 rw [Pminus, partpair S G.dep G.grade Z hΩ _ _ _ _ _ _ (movesNeg G u v L R q w g a a'), fling_null,fling_price]
 unfold timesA
 rw [flingTime, PiLp.zero_apply, sub_zero,zero_sub,neg_neg, neg_sub_neg]
 rw [realS S (2-w) (2-(w:ℂ)) _ (sub_nonneg.mpr a'.le) (by push_cast;rfl),
     realS S w w _ a.le rfl,leanX, show (2:ℝ).toNNReal=2 by norm_num]
 change _=inner ℂ X ((parabola S n (2-(w:ℂ)) * coreSp S q B * parabola S (n+m) (w:ℂ) * A * Par S m 2) Y)
 rw [add_comm n m]
 rfl
