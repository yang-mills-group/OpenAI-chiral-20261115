import YM.SU5.FiniteGaugeData.Maypole.Trove
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Real
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Folio
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)
-- chronology.Braces
variable {α:Type}(A:α→H.Op)(ν:α→ℕ)
local notation "Ι"=> Item α
local notation "Ω°"=> wordValue S Ω A ν
local notation "Φ"=> legis S A ν
local notation "δ"=> gapK S ν
local notation "η"=> timesA a
variable (G:Canopy H α)(V:OS.Semigroup H timeAxis)(w:H)(hw:∀ x:E4,M V x w=w)(e:Mink.Ray)
local notation "T"=>timeAxis
local notation "Ψ"=> Item G.Chip
open Flute Haven
local notation "P"=> hourE
local notation "z'"=> Icc (-1:ℝ) 1
local notation "A₀"=> G.dep
local notation "θ"=> G.grade
local notation "Spel" => Marked G
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Vp.Caps
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno (Lot)
-- complex angle only via real SO.A.Parameters.F.Hz. $
variable (q r z:ℝ)
abbrev walkway (x:SO) (y:E4):= Mink.General.walk x.val y
local notation "U" q:max=> walkway (P q e)
local notation "B"=> Flute.magnet e
local notation "Cq" q:max=> Real.cos (εB q)
local notation "Sq" q:max=> Real.sin (εB q)
def dusk(r q s:ℝ)(e:Ray):E4:= board (magnet e) (r+s) (s*q) 0
def dawn(r q:ℝ)(z:ℂ):ℂ:= (Real.cos (εB q):ℂ)*(r+z*(1+(q:ℂ)^2))
private lemma sun: Real.sin (εB q)= -Real.cos (εB q)*q:=by simp only [εB,Real.sin_neg,Real.cos_neg,Real.sin_arctan,Real.cos_arctan]; ring
lemma transit(r s:ℝ): ((U q) (dusk r q s e)) = board (magnet e) ((Cq q)*(r+s*(1+q^2))) ((Sq q)*r) 0:=by
 unfold dusk walkway; rw [hourE,Flute.alto]; congr 1 <;> (first| unfold useu|unfold user_); all_goals first| (rw [sun]; ring) | simp -- tune
private lemma dawning(s:ℂ)(h:|q|≤1)(p:0<r)(k:s∈Lot (r/8)): dawn r q s ∈ OS.Semigroup.inside:=by
 let z:= εB q; change 0< (dawn r q s).re; have he: (dawn r q s).re=(Cq q)*(r+s.re*(1+q^2)):=by unfold dawn; rw [← Complex.ofReal_pow,← Complex.ofReal_one,←Complex.ofReal_add]; simp only [Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,Complex.add_re, mul_zero,zero_mul,sub_zero]
 rw [he]; have ht:(q^2:ℝ) ≤ 1:=by nlinarith only [(abs_le.mp h).1,(abs_le.mp h).2, mul_nonneg (show 0≤1+q from (by linarith only [(abs_le.mp h).1])) (sub_nonneg.mpr (abs_le.mp h).2)]
 have hx:= Complex.abs_re_le_norm s|>.trans (mem_closedBall_zero_iff.mp k); apply mul_pos (warm_cos q); by_cases p':0 ≤ s.re; · positivity
 nlinarith only [(abs_le.mp hx).1, mul_le_mul_of_nonpos_left ht (le_of_not_ge p'),p]
lemma cosPay(r:ℝ): dawn r q z = Complex.ofReal (Real.cos (εB q)*(r+z*(1+q^2))):=by unfold dawn; push_cast; rfl
local notation "𝒪" s:max q:max=> dusk r q s e
-- joint merge true Eu.Physics.
section
variable (Ω:Bench V)(ph:∀ x:E4,M V x Ω.val=Ω.val)(u:H)(L L':List (Item G.Chip))(eX:Canopy.Tile G V Ω)(l: goodB timeAxis L)(p:goodF timeAxis L')
local notation "a'"=> Ω.val
include l p eX ph
lemma αEarn(s:ℝ)(t:0<r)(p':|q|≤1)(k:|s|≤r/8) :
 inner ℂ (role V Ω.val G.dep G.grade 0 L) ((V.U ((s*q) • magnet e)*V.E (r+s).toNNReal) (face V Ω.val G.dep G.grade 0 L')) =
 inner ℂ (role V Ω.val G.dep G.grade 0 (Spel (P q e) L)) (V.F (dawn r q s) (V.U (((Sq q)*r) • (magnet e)) (face V Ω.val G.dep G.grade 0 (Spel (P q e) L')))) :=by
 let x:=𝒪 s q; let u:= role V Ω.val G.dep G.grade 0 L; let f:=face V Ω.val G.dep G.grade 0 L'; have u' := Flute.btime e (r+s) (s*q) (0:Cross timeAxis); let Ls:= shifted x L'; have hx : x T=r+s:=u'; have he:0 ≤ x T:= hx ▸ (by linarith only [(abs_le.mp k).1,t]); have hh: SEP T x= (s*q) • B:= (bspace (magnet e) (r+s) (s*q) 0).trans (zero_add _)  -- placeholder
 let P₀:= P q e; let X:= (U q) x; let Xb:=(Cq q)*(r+s*(1+q^2)); have hg:X T=Xb:= ((congrArg (fun p:E4=> time p) (transit e q r s)).trans (Flute.btime ..)); have hv:0<X T:=by rw [hg]; have he:= dawning q r (s:ℂ) p' t (mem_closedBall_zero_iff.mpr ((Complex.norm_real _).trans_le k)); rw [cosPay] at he; exact he
 have huκ: SEP T X=((Sq q)*r) • (B):=by rw [show X= _ from transit e q r s,bspace,zero_add]
 let LX:=Spel P₀ L; let LY:=Spel P₀ L'
 let F:=(P₀); have ht: Spel P₀ (L++ Ls) = LX ++ shifted X LY :=by
    unfold LX LY Ls Marked shifted; rw [List.map_append,List.map_map,List.map_map]; congr 1; congr 1; funext p; apply Prod.ext; rfl; exact map_add ..
 have γ:= inB L l; have Q:= inF L' p; have hL:= negateT G q e l p'; have hB:= posit G q e p p';
 have hd:dawn r q s=OS.Semigroup.duration (X T).toNNReal:=by rw [OS.Semigroup.duration,Real.coe_toNNReal _ hv.le,hg,cosPay]
 let k:BackE T 0 L:=γ; rw [show V.U _* V.E _= V.E (r+s).toNNReal* V.U ((s*q) • magnet e) from (V.independent ..).symm, ←hh,←hx,rho_join V Ω.val ph G.dep G.grade x L L' he γ Q,hd, V.roots_heat (Real.toNNReal_pos.mpr hv), ← huκ]; let F:= aheadJoin x L L' he k Q
 refine (Steno P₀ G V Ω eX (L++ Ls) F (ht ▸ aheadJoin X LX LY hv.le hL hB)).trans ((congrArg (wordValue V Ω.val A₀ θ) ht).trans (rho_join V Ω.val ph A₀ θ X LX LY hv.le hL hB).symm)
omit l p
lemma purse (p:goodF timeAxis L): ∃ C:ℝ, ∀ᶠ t in atTop, Draft V (magnet e) (face V Ω.val A₀ θ 0 L) C t:=by
 let R:= oddSpin L T G.mirrorK; have he:goodB T R:=τOdd L G.mirrorK p; let X(q):= role V a' A₀ θ 0 (Spel (P q e) R); let Y(q):=face V a' A₀ θ 0 (Spel (P q e) L); let Y0:=face V a' A₀ θ 0 L
 have hx: Y0=role V a' A₀ θ 0 R:=by
    have he:= ok_back V Ω.val G.dep G.grade 0 L G.mirrorK (fun i=>rfl) (fun j=>(G.spar j).symm) (inF L p); rw [neg_zero] at he; exact he.symm
 obtain ⟨C',hv,v⟩:=FacePrice G V Ω.val e L p; obtain ⟨C₁,k,g⟩:= RolePrice G V Ω.val e R he; refine ⟨C₁*C',(eventually_gt_atTop (0:ℝ)).mono ?_⟩; intro t u q i; let U':=V.U (((Sq q)*t) • B); let f(z:ℂ):ℂ:=inner ℂ (X q) (V.F (dawn t q z) (U' (Y q))); refine ⟨f,?_,?_,?_⟩
 · intro x h; let H':= V.localHeat _ (dawning q t x i u h); exact ((innerSL ℂ (X q)).comp (ContinuousLinearMap.apply ℂ H.space (U' (Y q)))).analyticAt _|>.comp (H'.comp (show AnalyticAt ℂ (fun z=>dawn t q z) x from ((analyticAt_const.mul (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))))) -- tune parens
 · intro x h; let D:= V.F (dawn t q x); have hd:‖D‖≤1:= V.norm_row (dawning q t x i u h); refine (norm_inner_le_norm ..).trans ?_; refine mul_le_mul (g q i) ((D.le_opNorm _).trans ?_) (norm_nonneg _) k; rw [show ‖U' (Y q)‖=‖Y q‖ from V.unitary ..]; exact (mul_le_of_le_one_left (norm_nonneg _) hd).trans (v q i)
 intro s q'; change _=inner ℂ Y0 _; nth_rw 1 [hx]; exact (αEarn G V e q t Ω ph R L eX he p s u i q').symm
-- concl all slice Px.Support speed. PVM.
lemma sightseeing (p:Dense (Submodule.span ℂ (John V Ω.val A₀ θ):Set H)): V.ℚmeasure.region (copyE (magnet e))ᶜ=0:=by
 refine polarE V (magnet e) (BudgeSet V Ω.val A₀ θ) (sweep V Ω.val A₀ θ p) (fun i ⟨v,q,t⟩=> t ▸ purse G V e Ω ph v eX q)
#print axioms sightseeing
end
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
