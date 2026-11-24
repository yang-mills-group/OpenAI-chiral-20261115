import ZecaDaub
import YM.SU5.FiniteGaugeData.Seld.Pretzel
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


local notation "Λ"=>Marked G p L
local notation "Υ"=>Marked G p R
local notation "A'"=>G.dep (G.βE p u)
local notation "B'"=>G.dep (G.βE p v)
local notation "Y'"=> face S Z G.dep G.grade d Υ
local notation "Bq"=> Bcast S G p v q
local notation "θ"=> skip b h p r
variable (gt:Blast G L R)(gx:Rail G b L R d)

abbrev ground:= (leanX S 1 m*A').adjoint (role S Z G.dep G.grade (-1) Λ)
local notation "X'"=>ground S G Ω p u L
open Lattice Celeritas
-- k:Cinema requires G? explicit
abbrev lime (k:Cinema S)(b:Axis)(h:b≠timeAxis)(p:SO)(r:Reigns p b)
   (u v:G.Chip)(L R:List χ)(d:ℝ)(s:ℝ≥0)(q:E4):ℂ→ℂ:=
   sprawl S (ground S G Ω p u L) (face S Z G.dep G.grade d (Marked G p R)) s (Bcast S G p v q) k (skip b h p r)
        (skipBound b h p r) (G.grade u+G.grade v) (G.grade v) (q b).toNNReal (d-q b).toNNReal
local notation "J"=>lime S G Ω k b h p r u v L R d s q
local notation "↜" w:max=> rotated G p u v L R q w
include hΩ h r gx

lemma plaster (v₀:0<s)(v₁:s<(q b).toNNReal)(v₂:s<(d-q b).toNNReal):
 ψ (rotated G p u v L R q w)=J (w:ℂ):=by
 have e:0<q b:=Real.toNNReal_pos.mp (v₀.trans v₁)
 have a:q b<d:=sub_pos.mp (Real.toNNReal_pos.mp (v₀.trans v₂))
 rw [rotated,partpair S G.dep G.grade Z hΩ _ _ _ _ _ _ (spinsSpace G b h p r u v L R d q w gx e a),
     fling_null, remaps S G b h p r v q w,tickR G b h p r]
 rw [show timesA τ (G.βE p u,(0:E4))=0 from rfl, zero_sub, neg_neg,sub_zero,
     lime,sprawlR S X' Y' w s _ _ _ _ _ _ _ _ v₀ v₁ v₂,ground,
     ContinuousLinearMap.adjoint_inner_left];rfl
omit hΩ h r gx
structure Segment (b:Axis)(d:ℝ)(s δ:ℝ≥0)(q:E4):Prop where
 fromS:(s:ℝ)+(δ:ℝ)≤q b
 towards:(s:ℝ)+(δ:ℝ)≤d-q b
 timelikeBound:|q timeAxis|<(s:ℝ)
variable (e:0<s)(a:0<δ)(i:Segment b d s δ q)
include i
lemma ivory : δ≤(q b).toNNReal-s ∧ δ≤(d-q b).toNNReal-s:=by
 have u(x:ℝ)(w:(s:ℝ)+(δ:ℝ)≤x):δ≤x.toNNReal-s:= le_tsub_of_add_le_right (by rw [add_comm]; exact NNReal.coe_le_coe.mp (w.trans (Real.le_coe_toNNReal _)))
 exact ⟨u _ i.fromS,u _ i.towards⟩

abbrev budget := slu S X' Y' (m+n) n δ B'
include h r a
lemma mastic(t:z∈lanes (s:ℝ)): ‖J z‖≤budget S G Ω p u v L R d δ:=by
  obtain ⟨g,g'⟩:=ivory b d s δ q i
  exact (abound S X' Y' s Bq k θ (skipBound b h p r) _ _ _ _ _ _ t a g g').trans (by
    unfold budget slu; gcongr; exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun j=>vcost ..)
include hΩ h r gx D gt e
local notation "de"=>OS.Semigroup.duration
local notation "ee"=>OS.Semigroup.sideways
lemma watercolor (u':ℝ≥0)(h':0<u')(p':u'<2):
  backE S X Y 2 A B 0 m n (2-u') u' q=J (de u'+ee (q τ))∧
  forE S X Y 2 A B 0 m n (2-u') u' q=J (-(de u')+ee (q τ)):=by
 obtain ⟨gg,hh⟩:=ivory b d s δ q i
 have α:= tsub_pos_iff_lt.mp (lt_of_lt_of_le a gg)
 have β:= tsub_pos_iff_lt.mp (lt_of_lt_of_le a hh)
 have g:0<q b:=Real.toNNReal_pos.mp (e.trans α)
 have g':q b<d:=sub_pos.mp (Real.toNNReal_pos.mp (e.trans β))
 have f(w:ℝ)(a₀:0<w)(a₁:w<2) : backwards S X Y A (coreSp S q B) m n w=J w:=
    (playPos S G Ω hΩ u v L R q _ gt a₀ a₁).trans
      ((readPos S G Ω D b h p r u v L R d q _ gt gx g g' a₀ a₁).trans
         (plaster S G Ω hΩ k b h p r u v L R d s q _ gx e α β))
 have f'(w:ℝ)(a₀:0<w)(a₁:w<2): forwards S X Y A (coreSp S q B) m n w=J (-(w:ℂ)):=by
   rw [playNeg S G Ω hΩ u v L R q _ gt a₀ a₁,
       readNeg S G Ω D b h p r u v L R d q _ gt gx g g' a₀ a₁,
       plaster S G Ω hΩ k b h p r u v L R d s q _ gx e α β, ofReal_neg]
 have Z₁:= rills S X Y (q τ) s A (coreSp S q B) m n J (fun z t=> sprawlA _ _ _ _ _ _ _ _ _ _ _ _ _ t)
    e f f' u' h' p' i.timelikeBound
 rw [rpair S _ _ _ _ _ _ _ h' p',vpair S _ _ _ _ _ _ _ h' p',regain] at Z₁
 have β₀:optx S A 0=A:=by rw [optx,neg_zero,tini,one_mul,mul_one]
 rw [backE,forE, β₀]; exact Z₁
#print axioms watercolor
