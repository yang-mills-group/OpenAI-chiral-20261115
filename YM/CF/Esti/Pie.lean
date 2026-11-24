import YM.CF.Esti.Flare
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {z i j:ℕ}{E D:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup D][NormedSpace ℝ D]{u:E}{F:E→ Config G f}{x':ℝ}
def pers (S:Finset (Cell f))(p:Clip)(t:ℝ)(V:Config G f)(x:Site f):=∀ i∈S,SU.group.chord (faceValue V i) ≤ t*Real.exp (separation x i.1/p.relaxation)
def taken (S: Finset (Cell f))(p:PathData G)(q:Clip)(r b:ℕ)(t:ℝ)(V:Config G f)(i:Twin f) : SU.group.Color:= if i.2 then if pers S q t V i.1.1 then plotted p q r b V i else 0 else if i.1∈S then thinned p q t b r V i else plotted p q r b V i
def hallP (S: Finset (Cell f))(q:Clip)(V:Config G f)(i:Cell f)(t:ℝ):ℝ:= if i∈ S then PathData.clipped q t (Pressure.toll V i) else q.direct * SU.group.price (faceValue V i)
def king (S: Finset (Cell f))(p:PathData G)(q:Clip)(r b:ℕ)(t:ℝ)(V:Config G f)(i:Cell f) := hallP S q V i t + ‖taken S p q r b t V (i,true)‖^2/2
lemma persR (D: Finset (Cell f))(p:Clip)(t:ℝ)(V:Config G f)(i:Site f)(ht:0≤t)(h:∀ j:Cell f,t*Real.exp (separation i j.1/p.relaxation)<Pressure.toll V j→ j∈D): pers D p t V i ↔ PathData.kept p t i V:=by
 refine ⟨fun b j=>le_of_not_gt (fun x=>x.not_ge (b j (h _ x))),fun x j _=>x j⟩
lemma crownK (D: Finset (Cell f))(p:PathData G)(q:Clip)(r b:ℕ)(t:ℝ)(V:Config G f)(i:Cell f)(ht:0≤t)(h:pers D q t V i.1 ↔ PathData.kept q t i.1 V)(e:i∈D ∨ Pressure.toll V i ≤ t): king D p q r b t V i=crown p q r b t V i :=by
 have hx:hallP D q V i t=PathData.clipped q t (SU.group.chord (faceValue V i)):=by
    unfold hallP; split; rfl; rename_i l; rw [PathData.clipped,if_pos (show SU.group.chord (faceValue V i) ≤ t from e.resolve_left l),SU.group.chord_price]; ring
 unfold king taken crown; rw [hx]; dsimp only; unfold Pressure.trunk; simp_rw [h]; rw [add_comm]; split_ifs <;> simp [plotted]
lemma takes_q (D: Finset (Cell f))(p:PathData G)(q:Clip)(r b:ℕ)(t:ℝ)(V:Config G f)(i:Twin f)(ht:0≤t)(h:pers D q t V i.1.1 ↔ PathData.kept q t i.1.1 V)(e:i.1∈D ∨ Pressure.toll V i.1 ≤ t): taken D p q r b t V i = thinned p q t b r V i:=by
 unfold taken plotted thinned; rw [h]; by_cases g:i.2=true; simp [g]; by_cases f:i.1∈D; · simp [g,f]
 simp only [g,Bool.false_eq_true, ↓reduceIte,f]
 suffices b:(if Pressure.toll V i.1=0 then (1:ℝ) else min 1 (t/Pressure.toll V i.1))=1 by rw [b,one_smul]
 split; rfl; next x=> exact min_eq_left ((one_le_div (lt_of_le_of_ne (SU.group.chord_nonneg _) (Ne.symm x))).2 (e.resolve_left f)) -- syntax
abbrev HeldT (V:E→ Config G f)(D:Finset (Cell f))(x:E):Prop:=∀ᶠ v in 𝓝 x,∀ i∈D, faceValue (V v) i=faceValue (V x) i
lemma held_p {D:Finset (Cell f)}(p: HeldT F D u)(q:Clip)(x: Site f)(t:ℝ): ∀ᶠ v in 𝓝 u, pers D q t (F v) x ↔ pers D q t (F u) x:= p.mono fun v h=>by unfold pers; exact forall_congr' fun i=> imp_congr_right fun s=>by rw [h _ s]
lemma pruned {S: Finset (Cell f)}(p:HeldT F S u)(v:ℝ)(h:0≤v)(t:ℝ)(ht:0≤t)(f:PathData G)(q:Clip)(i j:ℕ)(l:Twin _)(hf: Allows n (fun z=>plotted f q i j (F z) l) u v) : Allows n (fun z=>taken S f q i j t (F z) l) u v:=by
 have H:= (held_p p q l.1.1 t); unfold taken; split_ifs with hx hk; -- tune
 · by_cases l':pers S q t (F u) l.1.1
   · exact hf.germ (H.mono fun z p=> (if_pos (p.mpr l')).symm)
   exact (allows_const u (v:=(0:SU.group.Color)) (by rw [norm_zero]; exact h)).germ (H.mono fun z p=> (if_neg (mt p.mp l')).symm)
 · let r(z:E):= Pressure.toll (F z) l.1; let a(z:E):= if r z=0 then 1 else min 1 (t/r z)
   have ha:|a u| ≤ 1:=by
      unfold a; split; simp; have hv:0 ≤ t/r u:=div_nonneg ht (SU.group.chord_nonneg _); rw [abs_of_nonneg (le_min zero_le_one hv)]; exact min_le_left ..
   apply ((hf.smul (a u)).mono (mul_le_of_le_one_left h ha)).germ; apply p.mono; intro x p; have hp:r x=r u:=congrArg SU.group.chord (p _ hk); simp only [plotted,hx,thinned,Bool.false_eq_true,↓reduceIte]; unfold a; rw [←hp]
 exact hf
lemma bia {g k:E → SU.group.Color}(h: Allows n g u C)(p:Allows n k u K) : Allows n (fun z=> inner ℝ (g z) (k z)) u (2^n*C*K):=Vol.breeze h p -- tune import
lemma cow {g:E→SU.group.Color}(p:Allows n g u C):Allows n (fun z=>‖g z‖^2/2) u (2^n*C*C):=by
 refine (((bia p p).smul (1/2)).mono (mul_le_of_le_one_left (by have hx:=p.nonneg; positivity) (by norm_num))).germ ?_
 exact Eventually.of_forall fun x=> by dsimp only; rw [real_inner_self_eq_norm_sq]; change (1/2:ℝ)*_= _; ring
lemma creek (i:Cell f)(b:Clip)(t:ℝ) (h:0 ≤ t) (hu:t ≤ 1) (hp:FuelG _ F u n C) (s: Finset (Cell f))(p:HeldT F s u): Allows n (fun z=>hallP s b (F z) i t) u (max (4*(b.linear+b.direct)) (b.direct*(Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 C)))):=by
 let d:= SU.group; let A(z:E):= Pressure.toll (F z) i; let C:=PathData.clipped b t (A u)
 have ha:=b.quadratic_pos; have hb:=b.tail_pos; unfold hallP; split; next k=>
    apply ((allows_const (v:=C) u ?_).mono (le_max_left ..)).germ
    · exact (p.mono fun x p=> by unfold C A Pressure.toll; dsimp only; rw [p _ k])
    have hv:0 ≤ A u:= SU.group.chord_nonneg _; have ht:A u ≤ 2:= SU.group.chord_le_two _; unfold C PathData.clipped; split
    · rw [Real.norm_of_nonneg (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left (show (A u)^2 ≤4 by nlinarith) ha.le]
    rw [Real.norm_of_nonneg (by positivity)]; have ho : b.linear*t*A u ≤ b.linear*1*2:=by gcongr
    linarith
 have hh:= trekP _ F hp (square i.2.val.1 i.2.val.2) i.1 4 le_rfl; have he:=fare_a hh
 apply ((he.smul b.direct).mono ?_).germ; · exact Eventually.of_forall fun i=> congrArg (b.direct*·) (fare_h ..)
 rw [abs_of_pos ha]; exact le_max_right ..
end YM.CF.Esti
