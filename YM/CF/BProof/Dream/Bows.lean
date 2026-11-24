import YM.CF.BProof.Dream.Index
/-! Tz and Mark dictionary up to v=2. Eased connectors from Γ. Expressions total on ℝ². -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix SU Finset Function Metric Complex Extension.Mar Mag
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {i : Fin 5}
-- first and second transitions in first interval. last one for [1,2].
def alpha(t:ℝ):= ease (2*t)
def second(t:ℝ):= ease (2*t-1)
def tertiary(t:ℝ):= ease (t-1)
@[fun_prop] lemma alphaS:ContDiff ℝ ∞ alpha:= ease_s.comp (contDiff_const.mul contDiff_id)
@[fun_prop] lemma secondS:ContDiff ℝ ∞ second:= ease_s.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
@[fun_prop] lemma terS:ContDiff ℝ ∞ tertiary:= ease_s.comp (contDiff_id.sub contDiff_const)
lemma alpha_down{t:ℝ}(h:t≤1/8): alpha t=0:=ease_low _ (by linarith)
lemma alpha_up{t:ℝ}(h:3/8≤t): alpha t=1:=ease_up _ (by linarith)
lemma second_down{t:ℝ}(h:t≤1/2): second t=0:=ease_low _ (by linarith)
lemma second_up{t:ℝ}(h:7/8≤t): second t=1:=ease_up _ (by linarith)
lemma ter_down{t:ℝ}(h:t≤5/4): tertiary t=0:= ease_low _ (by linarith)
lemma ter_up{t:ℝ}(h:7/4≤t): tertiary t=1:=ease_up _ (by linarith)
@[simp] lemma alpha0: alpha 0=0:= alpha_down (by norm_num)
lemma KingB (t:ℝ):inK (shiftB t):= ⟨shiftB_U t,shiftB_D t⟩

-- before and after B. For x=1 boundary amendment needs these.
namespace Scene
variable (F: Scene i)
def wind(s:ℝ): E:= F.A (ease s)
def cardB(s v:ℝ):= mold (species (F.wind s)) (shiftB (alpha v))
def knotB(s:ℝ):= mold (species (F.wind s)) living
def pluck(s v:ℝ):= (gamma i).seat (ease s * tertiary v)
def part(s v:ℝ):= mold (F.line (ease s,second v)) living
def brace(s v:ℝ):= F.cardB s v+(F.part s v-F.knotB s)+(pluck (i:=i) s v-living)
-- pluck lacks F, reference (i:=..)
lemma wind0 : F.wind 0=1:=by rw [wind,ease_zero,F.sewn0]
lemma wind1 : F.wind 1=locus i:=by rw [wind,ease_one,F.sewn1]
lemma busy {v:ℝ}(h:v≤1/2)(s:ℝ): F.brace s v=F.cardB s v:=by unfold brace part pluck; rw [second_down h,F.turn _ (easeZ s),ter_down (by linarith),mul_zero,(gamma i).seat0]; unfold knotB wind; abel
lemma live {v:ℝ}(h:1/2≤v)(e:v≤1)(s:ℝ): F.brace s v=F.part s v:=by unfold brace cardB pluck; rw [alpha_up (by linarith),ter_down (by linarith),mul_zero,(gamma i).seat0]; unfold knotB living; abel
lemma pass {v:ℝ}(h:1≤v)(s:ℝ): F.brace s v=pluck (i:=i) s v:=by unfold brace cardB part; rw [alpha_up (by linarith),second_up (by linarith), F.oneT _ (easeZ s),mold_one]; change F.knotB s+(_-_)+_= _; abel -- tune `change` metas
lemma checkpointU (s v:ℝ): (F.brace s v)ᵀ= F.brace s v∧ inK (F.brace s v):=by
 by_cases p:v≤1/2; rw [F.busy p]; exact ⟨moldT (shiftB_T _),moldK (classK _) (KingB _)⟩; by_cases h:v≤1; rw [F.live (by linarith) h]; exact ⟨moldT lv,moldK (F.unit _ ⟨easeZ _,easeZ _⟩) lk⟩; rw [F.pass (by linarith)]; exact (gamma _).sound _
lemma wind_s: ContDiff ℝ ∞ (fun s=> fund (F.wind s)):=F.moved.comp ease_s
lemma brace_s : ContDiff ℝ ∞ (uncurry F.brace):=by
 have he : ContDiff ℝ ∞ (fun x:Sq=> species (F.wind x.1)):= curvesS.comp (F.wind_s.comp contDiff_fst)
 have hw : ContDiff ℝ ∞ (uncurry (pluck (i:=i))):=(gamma i).seat_s.comp ((ease_s.comp contDiff_fst).mul (terS.comp contDiff_snd))
 let f(x: Sq):=(ease x.1,second x.2); have hh: ContDiff ℝ ∞ (F.line ∘ f):=contDiff_iff_contDiffAt.mpr (fun x=> (F.path (f x) ⟨easeZ _,easeZ _⟩).comp x ((ease_s.comp contDiff_fst).prodMk (secondS.comp contDiff_snd)).contDiffAt)
 exact ((moldS he (shiftB_S.comp (alphaS.comp contDiff_snd))).add ((moldS hh contDiff_const).sub (moldS he contDiff_const))).add (hw.sub contDiff_const)
lemma brace_d (v:ℝ) : F.brace 0 v= shiftB (alpha v):=by
 by_cases p:v≤1/2; rw [F.busy p,cardB,F.wind0,speciesOne,mold_one]; by_cases h:v≤1; rw [F.live (by linarith) h,alpha_up (by linarith),part,ease_zero,F.zeroT (second v) (easeZ _),mold_one]; rfl; rw [F.pass (by linarith),pluck,ease_zero,zero_mul,(gamma i).seat0,alpha_up (by linarith)]; rfl
lemma beginT {v:ℝ}(h:v≤ 1/8)(s:ℝ): F.brace s v= mold (species (F.wind s)) (Pair.pairM Pair.e0):=by rw [F.busy (by linarith),cardB,alpha_down h,shiftB_0]
lemma bT (s v:ℝ)(h:7/8≤v)(u:v≤5/4): F.brace s v=living:=by
 by_cases p:v≤1; rw [F.live (by linarith) p,part,second_up h,F.oneT _ (easeZ _),mold_one]; rw [F.pass (by linarith),pluck,ter_down u,mul_zero,(gamma i).seat0]
lemma earlyN (v:ℝ)(h:v≤1/2): F.brace 1 v=mold (Bz i) (shiftB (alpha v)):=by rw [F.busy h,cardB,F.wind1]
lemma midN (v:ℝ) (h:1/2≤v)(p:v≤1): F.brace 1 v=(gamma i).seat (1-second v):=by rw [F.live h p,part,ease_one,F.seat (second v) (easeZ _)]
lemma tallN (v:ℝ) (p:1≤v): F.brace 1 v=(gamma i).seat (tertiary v):=by rw [F.pass p,pluck,ease_one,one_mul]
lemma later (s v:ℝ)(h:1≤v): F.brace s v=(gamma i).seat (ease s*tertiary v):= F.pass h s
lemma windZ (F:Scene 0)(s:ℝ): F.wind s=1:= congrFun (F.quiet rfl).1 _
lemma braceZ (F:Scene 0)(s v:ℝ): F.brace s v=shiftB (alpha v):=by unfold brace cardB knotB pluck part; rw [(gamma 0).stays,F.windZ,speciesOne,(F.quiet rfl).2]; simp
end Scene
end YM.CF.BProof.Dream
