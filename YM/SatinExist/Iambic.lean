import YM.SatinExist.Ferry
/-!
 # Wave pricing. Including translations cost from Matsubara and back.
-/
set_option autoImplicit false
set_option maxRecDepth 2450
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" => Cache S
local notation "R" => saucer S
local notation "T" => M S
variable (Ω: H) {n:ℕ}(p:E4) (r:Fin n→ℕ) (F:Fin n→ H.Op) (y:Fin n→E4)
local notation "τ" m:max t:max=> Par S m (Real.toNNReal t)
section Wave
-- explicit Gap Minkowski signs. InTube uses ONE Eu orientation, space real.
def sepV (j:Axis)(p:E4) : E4:= (SEP j p).val
abbrev OrientedTimes (n:ℕ) := {p:Times n | ∀ i,0<(p i).im}
abbrev waveArc (z:Times n):H.space:= regiaN S Ω n (fun i=> parabola S (pedestal 0 r i) (-(z i)*I)) F 0 (fun i=> (SEP j (y i)).val)
abbrev waveΓ (m:ℕ) (z:Times n):= regiaN S Ω n (fun i=> parabola S (pedestal m r i) (-(z i)*I)) F (sepV j p) (fun i=> sepV j (y i))
-- `Times` := Pi. analytic in n dimensions on chamber.
lemma wave_h : AnalyticOnNhd ℂ (waveArc S Ω r F y) (OrientedTimes n):=by
 intro z q; apply regia_ana; intro i; let Y(z:Times n):= -(z i)*I; have hv:Y z∈inside:=by change 0<(Y z).re; simp [Y]; exact q i
 let C: Times n →L[ℂ]ℂ:= ContinuousLinearMap.proj i; let U:=waveArc S Ω r F y; apply (Bokeh S (pedestal 0 r i) (Y z) hv).comp (show AnalyticAt ℂ Y z from (C.analyticAt z).neg.mul analyticAt_const) -- exact
-- incremental formulation, works up to pressed budgets. positive-time fields. y time assembly.
def countM (j:Axis): ∀ {n:ℕ},E4 → (Fin n→ E4) → (Fin n→ ℝ≥0)→Times n
 | 0,_,_,_=> Fin.elim0
 | n+1,p,q,v=> Fin.cons ((↑((q 0-p) j):ℂ)+(OS.Semigroup.duration (v 0))*I) (countM j (q 0) (Fin.tail q) (Fin.tail v)) -- tune field order
lemma clock_ready (h:Fin n→ℝ≥0) (e:h∈Margins n): countM j p y h∈OrientedTimes n:=by
 induction n generalizing p with
 | zero=> exact fun i=> Fin.elim0 i
 | succ n ih=> refine fun i=> Fin.cases ?_ (fun i=> ?_) i
               · change 0< (((↑((y 0-p) j):ℂ)+(_)*I):ℂ).im; simp [OS.Semigroup.duration]; exact e 0
               · exact ih (y 0) (Fin.tail y) (Fin.tail h) (fun i=>e i.succ) i -- indentation
lemma amount_I (u:ℝ)(t:ℝ≥0): (-((u:ℂ)+(OS.Semigroup.duration t)*I))*I= OS.Semigroup.duration t + sideways u:=by unfold sideways; rw [neg_mul,add_mul, mul_assoc,I_mul_I]; ring
lemma resize_timeM (t p:E4)(u:ℝ≥0)(e:0<u)(m:ℕ): T (sepV j t-sepV j p) * parabola S m ((OS.Semigroup.duration u)+sideways ((t-p) j))= T (t-p) * Par S m u:=by
 let a:= (t-p) j
 let C:= T (sepV j t-sepV j p)
 change C * parabola S m _= _
 rw [← FsAct S _ _ _ (dur.mpr e), ←mul_assoc]; unfold C; rw [← timeslot S a,tgo]; have hz:(sepV j t-sepV j p + a • basis j)=t-p:=by unfold sepV; change t-t j • basis j-(p-p j • basis j)+ (t j-p j) • basis j= _; rw [sub_smul]; abel
 rw [hz]
lemma wave_pay (m:ℕ) (h:Fin n→ℝ≥0) (e:h∈Margins n) : waveΓ S Ω p r F y m (countM j p y h)= regiaN S Ω n (slew S (pedestal m r) h) F p y:=by
 induction n generalizing p m with
 | zero=> rfl
 | succ n ih=>
    unfold waveΓ slew; rw [regiaN,regiaN]; let H':= Fin.tail h; let r':= Fin.tail r; let Y':=Fin.tail y; let G':= Fin.tail F; let q:=y 0; let z:= r 0; let u:=h 0
    let X:= slew S (pedestal z r') H'; let Z:= fun i:Fin n=> parabola S (pedestal z r' i) (-countM j q Y' H' i*I); let w:= regiaN S Ω n X G' q Y'; let U:=waveΓ S Ω q r' G' Y' z (countM j q Y' H'); have hp:U = w:= ih q r' G' Y' z H' (fun i=>e i.succ)
    change T _ (parabola S (m+z) (-((↑((q-p) j):ℂ)+ OS.Semigroup.duration u*I)*I) (F 0 U))= T _ (Par S (m+z) u (F 0 w)); rw [amount_I,hp]; exact DFunLike.congr_fun (resize_timeM S q p u (e 0) (m+z)) (F 0 w)
lemma conducts (h:Fin n→ℝ≥0) (e:h∈Margins n) : waveArc S Ω r F y (countM j 0 y h)= regiaN S Ω n (slew S (pedestal 0 r) h) F 0 y := by
 rw [← wave_pay S Ω 0 r F y 0 h e]; unfold waveArc waveΓ sepV; rw [map_zero]; rfl
end Wave
section Heat
lemma part_par (n m:ℕ)(u v:ℝ)(p:0<u)(q:0<v): (τ n u)*(τ m v)=τ (n+m) (u+v):=by
 let x:=u.toNNReal; let y:=v.toNNReal; have hz:0<x:=Real.toNNReal_pos.mpr p; have hw: 0<y:=Real.toNNReal_pos.mpr q
 have he:x+y=(u+v).toNNReal:= (Real.toNNReal_add p.le q.le).symm
 ext1 z; apply cache_I S (n+m); refine DFunLike.congr_fun (Eq.trans (?_ : K (n+m)*( Par S n x * Par S m y)= _) (P_Heq S (u+v).toNNReal (n+m) (Real.toNNReal_pos.mpr (add_pos p q))).symm) z
 rw [cacheA,← he,S.time]; change K n*K m*(Par S n x*Par S m y)= S.E _ * S.E _; rw [←P_Heq S x n hz, ← P_Heq S y m hw]; let M:=Par S n x; rw [mul_assoc (K n),← mul_assoc (K m), (show Commute (K m) (Par S n x) from (gear S (OS.Semigroup.duration x) (dur.mpr hz) n).pow_left m).eq]; simp only [mul_assoc]
end Heat
end YM.SatinJets
