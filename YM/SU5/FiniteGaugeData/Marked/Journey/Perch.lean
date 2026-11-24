import YM.SU5.FiniteGaugeData.Marked.Journey.Ashore

/-!
# Extract on the elected volumes from all levels. Small volumes charged too.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common TopologicalSpace
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x) (s :ℕ) (S:Finset Cover)
local notation "Ω" i:max=> (tent Y h).c (momentm Y i s)
local notation "p"=> VolumeCape.Dream.plot l
local notation "C"=> (p).C
local notation "D"=> (p).K
local notation "X" i:max=> Orbit (Ω i)
local notation "χ" i:max=> city (Ω i)
local notation "κ" i:max=> Real.exp (duetCharge Y s * ((momentm Y i s).val:ℝ)^4)
local notation "c"=> Cadets Y h s S
local instance : Fact ((1:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
-- countable determining family including early
abbrev SK := (Courses (VolumeCape.Dream.plot l).C S → Common.J (VolumeCape.Dream.plot l).C S) ×
               ((i:Cadets Y h s S) → Lp ℂ 1 (city ((tent Y h).c (momentm Y i.val s))))
private lemma amtR (x:Purse S)(u:Courses C S): Integrable (amount C D S x.val u) (law C S):=Env.integrableX (amount_env C D S x.property u) _
private lemma toeR (x:Purse S)(i:ℕ): Integrable (toes Y h s i x.val) (χ i):=Env.integrableX (toes_m Y h s i S x.property) _
def fileR (x:Purse S): SK Y h s S:= (fun u=> Integrable.toL1 _ (amtR (l:=l) S x u),fun i=> Integrable.toL1 _ (toeR Y h s S x i))
def desk:ℝ:= argument Y h s S * Fintype.card (Courses (VolumeCape.Dream.plot l).C S) + ∑ i:Cadets Y h s S, Real.exp (duetCharge Y s * ((momentm Y i.val s).val:ℝ)^4)
lemma desk_n: 0≤desk Y h s S:=add_nonneg (mul_nonneg (ahead Y h s S).le (Nat.cast_nonneg _)) (sum_nonneg fun _ _=> (Real.exp_pos _).le)
lemma filing (f g:Purse S): receipt Y h s S (f.val-g.val)≤ desk Y h s S*dist (fileR Y h s S f) (fileR Y h s S g):=by
  let V:=fileR Y h s S f; let W:=fileR Y h s S g
  let Z:=dist V W
  have he(u:Courses C S): (∫ x, ‖amount C D S (f.val-g.val) u x‖ ∂law C S) ≤ Z:= by
    have ht:dist (V.1 u) (W.1 u)= _ := -- give expected
      (show _=(∫ x, ‖amount C D S (f.val-g.val) u x‖ ∂law C S) from by unfold V W fileR; dsimp only; rw [dist_eq_norm,←Integrable.toL1_sub,L1.norm_of_fun_eq_integral_norm]; rfl)
    rw [←ht]; exact (dist_le_pi_dist V.1 W.1 u).trans (by unfold Z; rw [Prod.dist_eq]; exact le_max_left ..)
  have hu:(Touch S l (f.val-g.val))≤ (Fintype.card (Courses C S):ℝ)*Z:= (sum_le_sum (s:=univ) (fun i _=> he i)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul]) -- tune
  have hv(i:c):youth Y h s i.val (f.val-g.val) ≤ Z:=by
    have t:dist (V.2 i) (W.2 i)=youth Y h s i.val (f.val-g.val):=by unfold V W fileR youth; dsimp only; rw [dist_eq_norm,←Integrable.toL1_sub,L1.norm_of_fun_eq_integral_norm]; rfl
    rw [←t]; exact (dist_le_pi_dist V.2 W.2 i).trans (by unfold Z; rw [Prod.dist_eq]; exact le_max_right ..)
  change argument Y h s S * Touch S l (f.val-g.val)+(∑ i:c, (κ i.val)*youth Y h s i.val (f.val-g.val)) ≤ _
  unfold desk; rw [add_mul,mul_assoc,Finset.sum_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hu (ahead Y h s S).le) (sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hv i) (Real.exp_pos _).le)
lemma carpet:∃ F:ℕ→Purse S,∀ x:Purse S,∀ r:ℝ,0<r→ ∃ i:ℕ,receipt Y h s S (x.val-(F i).val)<r:=by
  let Q:= fileR Y h s S
  let L:= Set.range Q; let XY:=L.Elem
  let A:Purse S:= ⟨1,Sound.ice⟩
  letI:Nonempty XY:=⟨Set.rangeFactorization Q A⟩
  obtain ⟨V,hV⟩:= exists_dense_seq XY
  choose F hf using fun i:ℕ=> (V i).property
  refine ⟨F,fun f r h'=>?_⟩
  let d:= desk Y h s S; have hp:0≤d:=desk_n ..
  obtain ⟨i,u⟩:=hV.exists_dist_lt (Set.rangeFactorization Q f) (ε:=r/(d+1)) (by positivity)
  refine ⟨i,lt_of_le_of_lt (filing Y h s S f (F i)) ?_⟩; change d*dist (Q f) (Q (F i)) < r
  change dist (Q f) (V i).val < r/(d+1) at u
  rw [hf i]; nlinarith [(lt_div_iff₀ (by linarith only [hp]:0<d+1)).1 u, dist_nonneg (x:=Q f) (y:=(V i).val)]

def legacy (i k:ℕ):= (Y.ir i).val^5 ≤ Y.uv k
lemma cadence (f:ℕ→ℕ)(a:StrictMono f):∀ i,∀ᶠ k:ℕ in atTop,legacy Y i (f k):=fun i=> (Y.uv_grows.comp a).tendsto_atTop.eventually_ge_atTop _
lemma absent (f:ℕ→ℕ)(a:StrictMono f):∀ i,∀ᶠ k:ℕ in atTop,¬legacy Y (f k) i:=fun i=> ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp (Y.ir_grows.comp a).tendsto_atTop|>.eventually_gt_atTop (Y.uv i)).mono fun _ v=> not_le.mpr v
lemma exist_excerpt (f g:ℕ→ℕ)(a:StrictMono f)(b:StrictMono g) (pay:ℕ→ℕ→Prop)(e:∀ i,∀ᶠ k:ℕ in atTop,pay i k):
    ∃ i k:ℕ→ℕ, StrictMono i ∧ StrictMono k ∧
      (∀ x y, legacy Y (f (i x)) (g (k y)) → (Y.voyage (f (i x))).kick ≤ g (k y) ∧ pay (f (i x)) (g (k y))) ∧
      ∀ (s:ℕ) (S:Finset Cover)(u:Chorus)(x:Purse S), ∃ F z, Couplet (f∘i) (g∘k) (output Y h s S u x) F z (fun e=> ∀ᶠ n in atTop,legacy Y (f (i n)) (g (k (e n)))) := by
  let Z:=ℕ × Playbill
  let T (j:Z):=(carpet Y h j.1 j.2.1).choose j.2.2.2
  let F(j:Z):=output Y h j.1 j.2.1 j.2.2.1 (T j)
  /- Need row convergence on ALL unthinned periods in Course input. So apply two_steps on raw F j i k with the i k parameters instead of precomp. -/
  -- use trick extend recites coordinates with ALL row exams independent of period.
  let P(v:Option ℕ × Z)(i k:ℕ):=F v.2 (v.1.getD (f i)) (g k)
  obtain ⟨i,k,x,y,E,V⟩:= recites P (fun j=> ⟨_,fun m k=> paid_stage Y h _ _ _ _ _ _⟩)
    (fun i=> b.tendsto_atTop.eventually ((eventually_ge_atTop ((Y.voyage (f i)).kick)).and (e (f i))))
    (fun n=> cadence Y g b (f n)) (fun n=> absent Y f a (g n))
  have H(j:Z):∃ M z,Couplet (f∘i) (g∘k) (F j) M z (fun e=> ∀ᶠ n in atTop,legacy Y (f (i n)) (g (k (e n)))) :=by
    choose M w h using V
    refine ⟨fun v=> M (some v,j) 0,_,⟨?_,?_,(h (none,j)).paths⟩⟩
    · intro v; exact (h (some v,j)).inner 0
    refine (h (none,j)).periods.congr (fun t=> ?_)
    exact tendsto_nhds_unique (f:=fun n=>P (none,j) (i t) (k n)) ((h (none,j)).inner (i t)) ((h (some (f (i t)),j)).inner 0)
  refine ⟨i,k,x,y,E,fun s S u v=> rising_cloud _ ?_⟩
  intro r e
  obtain ⟨m,w⟩:= (carpet Y h s S).choose_spec v r e
  let j:Z:= (s,S,u,m)
  obtain ⟨M,z,E'⟩:= H j
  exact ⟨F j,M,z,(fun p' a=> (paid_joint Y h s S u v (T j) p' a).trans w.le),E'⟩
end YM.CF.Buffered.Afterglow.Journey
