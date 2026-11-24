import YM.SU5.FiniteGaugeData.Concord.PriceCard
/-! # Concrete estimates for the full read at this electorate -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
namespace Meet
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable {i k:ℕ→ℕ} (W:Traced Y H i k F E P)
variable (S:ℕ→Finset Cover) (n d s:ℕ)
local notation "S'"=> spread Λ l S
local notation "K"=> tent Y H
local notation "Ω" => ConeFilter Y i k
local notation "V'"=> W.own
local notation "ℒ" z:max=> (z)*(count ((S') s))
local notation "αs"=> facia Λ l S s (charger Y H S)
local notation "ρ" f:max n:max d:max=> purseFee Y H S f s n d

-- room certificates for contributing marks at boundaries of evaluators (embedding conveniences)
-- plus the actual mixed quote quals
structure Admitted (n d:ℕ) :Prop where
  names : ∀ j ≤ s,Hosp (S j) (side Y n j) ∧ Hosp (spread Λ l S j) (side Y n j)
  honor : ∀ j<s, SeasonPass Y H ((S') j) j n d
  ultimately : Ready Y H ((S') s) s n d

private lemma mix {I:Type*}{l:Filter I}{p:ℕ→ I→Prop}: ∀ s:ℕ,(∀ j<s, ∀ᶠ x in l,p j x) → ∀ᶠ x in l,∀ j<s,p j x
| 0 => fun _=> Eventually.of_forall (fun _ _=>by omega)
| s+1=> fun h=>
    ((mix s (fun i t=> h i (by omega))).and (h s (lt_add_one _))).mono fun _ p j t=> by
      obtain a | a := lt_or_eq_of_le (Nat.le_of_lt_succ t)
      · exact p.1 j a
      exact a ▸ p.2

include H in
lemma room_card : ∀ᶠ n in atTop,∀ j ≤ s,Hosp (S j) (side Y n j) ∧ Hosp (spread Λ l S j) (side Y n j):=by
  have he(j:ℕ)(T:Finset Cover) : ∀ᶠ n:ℕ in atTop,Hosp T (side Y n j):= ((momentum Y j).eventually (suitable T K)).mono (fun n p=> Eq.mp (congrArg (Hosp T) (terrain Y H (Y.ir n) j)) p)
  exact (mix (s+1) (fun j _=> (he j (S j)).and (he j ((S') j)))).mono (fun n h j v=> h j (by omega))
include W
lemma admission_row : ∀ᶠ n in atTop,∀ᶠ d in atTop,Admitted Y H S s n (k d) :=by
  filter_upwards [room_card Y H S s, mix s (fun i _=> crowd Y H ((S') i) i)] with n p h
  filter_upwards [ready_row Y H ((S') s) s (V') n] with d r using ⟨p,fun j v=> ⟨h j v, r.1.1, lt_trans v r.1.2⟩,r⟩

lemma admission_cone : ∀ᶠ j in ConeFilter Y i k, Admitted Y H S s (i j.1) (k j.2) := by
  filter_upwards [((V').pick.grow_i.tendsto_atTop.comp ConeFilter.late_left).eventually (room_card Y H S s), mix s (fun j _=> box_visit (V').pick (S:=((S') j)) (s:=j)),ready_cone _ _ ((S') s) s (V')] with n t h i using ⟨t,h,i⟩ -- tune

-- error sequences & convergence bonuses. xactor, full quote
omit W

def booth (e:ℝ):ℝ:= Meet.delta Y H S s (e*(count ((S') s)+1)) e
lemma booth_nonneg (z:ℝ) (p:0≤z) :0≤ booth Y H S s z:= delta_pos Y H S s (mul_nonneg p (add_nonneg (count_nonneg _) zero_le_one)) p
lemma booth_time:Tendsto (fun i=> booth Y H S s (Meter i)) atTop (𝓝 0):= by
  let b:=(local_cost Y H s ((S') s)).choose; let t:= meter_time
  have he:= ((t.mul_const (count ((S') s)+1)).add (t.const_mul (b*s))).mul_const αs
  simpa only [zero_mul,mul_zero,add_zero,booth,delta,b] using he -- need unfold booth, delta

private lemma puff (t:ℝ)(e:0 ≤ t) : t ≤ t*(count ((S') s)+1):= le_mul_of_one_le_right e (le_add_of_nonneg_left (count_nonneg _))
private lemma packed (t:ℝ)(e:0 ≤ t) : ℒ t ≤ t*(count ((S') s)+1):= mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) e

include W
local notation "Qt"=> upper S
local notation "Q"=> final S P
local notation "Z" => stock Λ l S K

theorem besides : ∀ᶠ n in atTop,∀ ε, 0 < ε→ ∀ᶠ d in atTop, Admitted Y H S s n (k d) ∧
    ∀ f:∀ j,Palette (S j),
      ‖(Z) f (ground Y H S n (k d)) s - (Z) f (upper S n P) s‖ ≤ s*ε*(facia Λ l S s (charger Y H S)*purse S f s) ∧
      ‖purseFee Y H S f s n (k d) - matt Y H W S f s n‖ ≤ booth Y H S s ε * purse S f s := by
  filter_upwards [admission_row Y H W S s, first_row Y H ((S') s) s (V')] with n t h ε e
  filter_upwards [t, (Metric.tendsto_nhds (α:=Music ((S') s))|>.mp h ε e), mix s (fun j _=> Metric.tendsto_nhds.mp ((W.receipts.clocks j ((S') j)).inner n) ε e)] with d p h u
  refine ⟨p, fun f=> ?_⟩; let b:=charger Y H S; let r:=ℒ ε; let V:=ground Y H S n (k d); let G:= upper S n P; let L:=critics Y H ((S') s) s n (k d)
  have hi:= fun i (_:i<s)=> ground_cap Y H S n (k d) i; have ht:=fun i (_:i<s)=> upper_cap Y H W S n i; have hv(i)(t:i<s):dist (V i) (G i)≤ε:= (u i t).le
  exact ⟨price Λ l S K f V s b (charge Y H S) hi G ht ε e.le hv, quote_diff Y H S f s V G hi ht (critic Y H ((S') s) s n (k d)) (gaugeEar Y H ((S') s) s (V') n) (fiscal ..) (e.le.trans (puff (Λ:=Λ) (l:=l) S s ε e.le)) e.le hv (h.le.trans (puff (Λ:=Λ) (l:=l) S s ε e.le))⟩ -- H missing usage in puff? locals includes Y only? `ℒ` only spread Λ l implicit

theorem launched : ∀ᶠ n in atTop,∀ f:∀ j,Palette (S j),
    ‖(Z) f (upper S (i n) P) s - (Z) f (final S P) s‖ ≤ s*Meter n*(facia Λ l S s (charger Y H S)*purse S f s) ∧
    ‖matt Y H W S f s (i n)-finished Y H W S f s‖ ≤ booth Y H S s (Meter n)*purse S f s:=by
  filter_upwards [mix s (fun j _=> chamber Y H ((S') j) j W), meshed Y H ((S') s) s W] with n t h f
  let b:=charger Y H S; let V:=upper S (i n) P; let G:=final S P
  have e:0 ≤ Meter n:= (meter_p _).le
  have hi:= fun j (_:j<s)=> upper_cap Y H W S (i n) j; have ht:=fun j (_:j<s)=> final_cap Y H W S j
  have he:= e.trans (puff (Λ:=Λ) (l:=l) S s _ e); have h':= h.1.trans (packed (Λ:=Λ) (l:=l) S s _ e)
  exact ⟨price Λ l S K f V s b (charge Y H S) hi G ht _ e t,quote_diff Y H S f s V G hi ht _ (finale Y H ((S') s) s W.own) (finale_cap ..) he e t h'⟩

theorem runway : ∀ᶠ n in atTop,∀ d, legacy Y (i n) (k d)→ Admitted Y H S s (i n) (k d) ∧
    ∀ f: ∀ j,Palette (S j),
      ‖(Z) f (ground Y H S (i n) (k d)) s - (Z) f (final S P) s‖ ≤ s*Meter n*(facia Λ l S s (charger Y H S)*purse S f s) ∧
      ‖purseFee Y H S f s (i n) (k d) - finished Y H W S f s‖ ≤ booth Y H S s (Meter n)*purse S f s := by
  filter_upwards [mix s (fun j _=> W.receipts.errorC j ((S') j)),meshed Y H ((S') s) s W,ConeFilter.criterion.mp (admission_cone Y H W S s)] with n t h u d v
  refine ⟨u d v,fun f=> ?_⟩; let b:=charger Y H S; let V:=ground Y H S (i n) (k d); let G:=final S P
  have e:0 ≤ Meter n:= (meter_p _).le
  have hi:= fun j (_:j<s)=> ground_cap Y H S (i n) (k d) j; have ht:=fun j (_:j<s)=> final_cap Y H W S j; have hq:= fun (j:ℕ) (r:j<s)=> (t j r d v).2.1
  have he:= e.trans (puff (Λ:=Λ) (l:=l) S s _ e); have h':= (h.2 d v).2.trans (packed (Λ:=Λ) (l:=l) S s _ e)
  exact ⟨price Λ l S K f V s b (charge Y H S) hi G ht _ e hq,quote_diff Y H S f s V G hi ht _ (finale Y H ((S') s) s W.own) (finale_cap ..) he e hq h'⟩

-- usable version at the tprod with palette certs
variable (f:∀ j,Palette (S j))(P':ℕ→junior (tent Y H))(t:synch Y H S f s P')(v:Style.fits s P')
local notation "T" => PiTensorProduct.tprod ℂ P'
local notation "X"=> starGem Y H W s T
include W t v
theorem registers : (∀ᶠ n:ℕ in atTop, Tendsto (fun d=> reader Y H n (k d) s W T) atTop (𝓝 (matt Y H W S f s n))) ∧
    Tendsto (fun n=> matt Y H W S f s (i n)) atTop (𝓝 (starGem Y H W s T)) ∧
    Tendsto (fun j:ℕ×ℕ=> reader Y H (i j.1) (k j.2) s W T) (ConeFilter Y i k) (𝓝 (starGem Y H W s T)):=by
  have he : Tendsto (fun j:ℕ=> booth Y H S s (Meter j)*purse S f s) atTop (𝓝 0):=by simpa using (booth_time Y H S s).mul_const (purse S f s)
  have hv(ε:ℝ)(p:0<ε) : ∀ᶠ j:ℕ in atTop,booth Y H S s (Meter j)*purse S f s<ε:=he.eventually (gt_mem_nhds p)
  simp_rw [←finished_eq Y H W S f s P' t v]
  have hf (n d:ℕ)(r:Admitted Y H S s n d) := weighed Y H W S f n d s P' t v r.honor r.ultimately
  refine ⟨?_,Metric.tendsto_nhds.mpr ?_,Metric.tendsto_nhds.mpr ?_⟩
  · filter_upwards [besides Y H W S s] with n p
    refine Metric.tendsto_nhds.mpr fun ε v=>?_ -- shadow
    obtain ⟨x,d⟩:= (hv ε v).exists; filter_upwards [p _ (meter_p x)] with j t'; rw [←hf n (k j) t'.1, dist_eq_norm]; exact (t'.2 f).2.trans_lt d
  · intro ε p; filter_upwards [hv ε p, launched Y H W S s] with n h q; rw [dist_eq_norm]; exact (q f).2.trans_lt h
  intro ε p; apply ConeFilter.criterion.mpr; filter_upwards [hv ε p,runway Y H W S s] with n h r x y; obtain ⟨v,d⟩:=r x y; rw [←hf (i n) (k x) v, dist_eq_norm]; exact (d f).2.trans_lt h

end Meet
end YM.CF.Buffered.Concord

#print axioms YM.CF.Buffered.Concord.Meet.registers
