import ZecaTempera
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

open Boundary Lattice Celeritas
variable (e:0<s)(a:0<δ)(g:Test4)(i:∀ q∈ tsupport g,Segment b d s δ q)

abbrev flick(g:Test4)(j:ℕ):= g q*(backE S X Y 2 A B 0 m n (dearth j) (squirt j) q
                 -forE S X Y 2 A B 0 m n (dearth j) (squirt j) q)
local notation "J"=>lime S G Ω k b h p r u v L R d s q
local notation "f" q':max=>flick S G Ω u v L R q' g
local notation "Go"=> budget S G Ω p u v L R d δ
include hΩ D h r k gt gx e a i

lemma fleck : Tendsto (f q) atTop (𝓝 0) ∧ ∀ j, ‖(f q) j‖≤‖g q‖*(Go+Go) := by
 by_cases yy:g q=0
 · refine ⟨tendsto_const_nhds.congr (fun i=>by simp [flick,yy]),fun i=>by simp [flick,yy]⟩
 have tt:=i q (subset_closure yy)
 let t:= sideways (q τ)
 have hw(j:ℕ):=watercolor S G Ω hΩ D k b h p r u v L R d s δ q gt gx e a tt (squirt j) (squirtP j)
       (tsub_pos_iff_lt.mp (dearthP j))
 have hL(x:ℝ): (x:ℂ)+t∈ lanes (s:ℝ):=by change |((x:ℂ)+t).im|<_; simpa [sideways,t] using tt.timelikeBound

 have t':t∈ lanes (s:ℝ):=by simpa only [Complex.ofReal_zero,zero_add] using hL 0
 have hT:ContinuousAt J t:=(sprawlA _ _ _ _ _ _ _ _ _ _ _ _ _ t').continuousAt
 let uS(j:ℕ):=OS.Semigroup.duration (squirt j)
 have hv:Tendsto uS atTop (𝓝 0):=by
    refine (show OS.Semigroup.duration 0=(0:ℂ) from by simp [OS.Semigroup.duration]) ▸ ?_
    exact continuous_ofReal.continuousAt.tendsto.comp (NNReal.continuous_coe.continuousAt.tendsto.comp squirtL)
 have Hh:Tendsto (fun i=>uS i+t) atTop (𝓝 t):=by simpa only [zero_add] using hv.add (tendsto_const_nhds (x:=t))
 have Hh':Tendsto (fun i=> -uS i+t) atTop (𝓝 t):=by simpa only [neg_zero,zero_add] using hv.neg.add (tendsto_const_nhds (x:=t))
 have hr(j:ℕ):(f q) j=g q*(J (uS j+t)-J (-uS j+t)):=by unfold flick dearth; rw [(hw j).1,(hw j).2]
 constructor
 · apply Tendsto.congr' _ (show Tendsto (fun j=>g q*(J (uS j+t)-J (-uS j+t))) atTop (𝓝 0)
          from (by simpa only [comp_apply,sub_self,mul_zero] using ((hT.tendsto.comp Hh).sub (hT.tendsto.comp Hh')).const_mul (g q)))
   exact Eventually.of_forall fun j => (hr j).symm
 intro j; rw [hr,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 have hh:= mastic S G Ω k b h p r u v L R d s δ q

 exact (norm_sub_le ..).trans (add_le_add (hh (uS j+t) a tt (hL _)) 
      (hh (-uS j+t) a tt (ofReal_neg (squirt j) ▸ hL (- (squirt j:ℝ)))))

lemma agate : DotComm S A B 0 g m n (flame S 2 zero_lt_two X) (flame S 2 zero_lt_two Y):=by
 apply flanks
 let F(i:ℕ)(q:E4):=(f q) i
 have H(j:ℕ):Integrable (F j) :=by unfold F flick; simp_rw [mul_sub]; exact (fountainP ..).sub (fountainR ..)
 have t(q:E4):=fleck S G Ω hΩ D k b h p r u v L R d s δ q gt gx e a g i
 have hb(j:ℕ): ∀ᵐ q:E4, ‖F j q‖≤‖g q‖*(Go+Go):=Eventually.of_forall (fun q=>(t q).2 j)
 have hc:= tendsto_integral_of_dominated_convergence (fun q=> ‖g q‖*(Go+Go)) (fun j=>(H j).aestronglyMeasurable)
    (g.integrable.norm.mul_const _) hb (Eventually.of_forall (fun q:E4=>
          (show Tendsto (fun j=>F j q) atTop (𝓝 ((fun _=> (0:ℂ)) q)) from (t q).1)))
 rw [integral_zero] at hc; exact hc
#print axioms agate
