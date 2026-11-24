import ZecaPrimer
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


structure Rail (d:ℝ):Prop where
 tail_ok: BackE b (-1) L
 head_ok: LaneE b d R
local notation "Λ"=> Marked G p L
local notation "Υ"=> Marked G p R
abbrev remap (w:ℝ):=cir p G (v,fling q w)
local notation "A'"=> G.dep (G.βE p u)
local notation "B'"=> G.dep (G.βE p v)
abbrev rotated (w:ℝ):= TwoPlus Λ Υ (G.βE p u,0) (remap G p v q w)

variable (gt:Blast G L R)(gx:Rail G b L R d)
include h r in lemma tickR : timesA timeAxis (remap G p v q w)=q b:=
  (r (fling q w)).trans (flingSide b h q w)
include h r gx
lemma spinsSpace(e:0<q b)(a:q b<d):SpaceFor τ (-1) d Λ Υ (G.βE p u,0) (remap G p v q w):=by
  refine ⟨⟨LineH (K:=fun _=>H) G p b r L gx.tail_ok.1,?_⟩,⟨LineH (K:=fun _=>H) G p b r R gx.head_ok.1,?_⟩,?_,?_,?_⟩
  · intro i u;obtain ⟨i,t,rfl⟩:= List.mem_map.mp u
    change walk p.val _ τ<_;rw [r];exact gx.tail_ok.2 i t
  · intro i u;obtain ⟨i,t,rfl⟩:= List.mem_map.mp u
    change _<walk p.val _ τ;rw [r];exact gx.head_ok.2 i t

  · change (-1:ℝ)<0; norm_num
  · rw [tickR G b h p r];exact e
  rw [tickR G b h p r];exact a
local notation "Z'" t:max=> rotated G p u v L R q t
include D gt
lemma readPos(e:0<q b)(a:q b<d)(t:0<w)(v₀:w<2): ψ (Pplus G u v L R q w)= ψ (Z' w):=by
 apply siphon S G Ω D p _ _ _ (movesPos G u v L R q w gt t v₀).sprint
        (spinsSpace G b h p r u v L R d q w gx e a).sprint
 suffices Marked G p (Pplus G u v L R q w)=Z' w by rw [this]
 unfold Marked Pplus rotated TwoPlus
 simp only [List.map_append,List.map_cons,List.map_nil]
 rw [show cir p G (u,(0:E4))=(G.βE p u,0) from Prod.ext rfl (map_zero ..)]
lemma readNeg(e:0<q b)(a:q b<d)(t:0<w)(v₀:w<2): ψ (Pminus G u v L R q (-w))=ψ (Z' (-w)):=by
 apply siphon S G Ω D p _ _ _ (movesNeg G u v L R q w gt t v₀).sprint
        (spinsSpace G b h p r u v L R d q (-w) gx e a).sprint
 simp only [Pminus,rotated,Marked,TwoPlus]
 simp only [List.map_append,List.map_cons,List.map_nil]
 rw [show cir p G (u,(0:E4))=(G.βE p u,0) from Prod.ext rfl (map_zero ..),
     List.append_assoc,List.append_assoc]
 exact (List.Perm.refl _).append (.swap _ _ _)

omit D gt gx
abbrev skip (b:Axis)(h:b≠timeAxis)(p:SO)(r:Reigns p b): Cross timeAxis:=⟨feel p (basis τ), by change feel p _ τ=0; rw [r (basis τ)];simp [h,h.symm]⟩

local notation "ϰ"=> skip b h p r
lemma skipBound:‖ϰ‖≤1:=by change ‖feel p (basis τ)‖≤1; rw [Vnorm]; exact le_of_eq (by simp [basis])

abbrev Bcast:=coreSp S (feel p (axisZero q)) B'
-- simplify Bcast as optx. ...
lemma remaps: stamps S G.dep (remap G p v q w) =
 S.U (w • ϰ)*Bcast S G p v q*S.U (-w • ϰ) := by
 let e:=feel p (axisZero q)
 have g: (remap G p v q w).2=w • (ϰ).val+e:= by change feel p (_ + _)=_;rw [map_add,map_smul]
 let i:=w • ϰ
 have j:optx S (Bcast S G p v q) i.val=stamps S G.dep (remap G p v q w):=by
   unfold Bcast stamps coreSp
   rw [opt_act,g, map_add (SEP τ)]
   change optx S B' (i.val+ _)=optx S B' ((SEP τ i.val).val+(SEP τ e).val)
   rw [show (SEP τ i.val).val=i.val by change i.val-i.val τ • basis _=i.val; rw [show i.val τ=0 from i.property,zero_smul,sub_zero]]
 rw [←j,optx,laneslot S i,← show (-i).val= -i.val from rfl,laneslot,neg_smul]
