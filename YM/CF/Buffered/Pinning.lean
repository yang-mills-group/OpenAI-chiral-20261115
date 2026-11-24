import YM.CF.Gloss.Feast

/-!
# VolumeBurn's version of the auxiliary heat donor

The manuscript allows the pin choice in `Gloss/Net.lean`'s scalar exponent
of `RP.Str.hoistF` to be made coherently on its different top cubes; so it may
NOT be definitionally `pinpoint`. Parameterize by those choices. This is the
payer/tolerance and reflection check at **one cube**. Not a comparison of
such donors across different periods! All used only on the auxiliary side of
the argument.

Pin/cabin defs and lemmas below largely by generalizing scripts in
`Phase/Exact`, `Gloss/{Net,Scene,Year}`. See `heat_db`.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Gloss Spark RG WilsonStartup Vale Scroll Spire
attribute [local instance] opCStarAlgebra

variable {m B : Side} {c : Phase.Part m B} {A D d e : ℝ}

structure Pinning (m B : Side) where
  pin : Stamp m B → Index m
  admissible (S : Stamp m B) (p : Branch.Grove (terr _) S) (h : S.card ≤ scallop B) :
    sanctioned m B S (some (pin S))

abbrev originalPinning (m B : Side) : Pinning m B :=
  ⟨pinpoint m B, Phase.Grove.plane⟩
namespace Pinning

variable (p : Pinning m B)

def term (W : Scroll m B c) (S : Stamp m B) :=
  if S.card ≤ scallop B then W.value S (some (p.pin S)) else fun _ => 0

def bill (W : Scroll m B c) (a : costG m B) := Gloss.workQ a (p.term W a.2)
def target (a : costG m B) := ρx a.1 (p.pin a.2)

def cabin (W : Scroll m B c) (x : Pack m B) := ∑ i : costG m B, p.bill W i x
def pass (W : Scroll m B c) (i : Axis) (x : Pack m B) :=
  ∑ k : costG m B, RP.bonus (p.target k) i • p.bill W k x

lemma bill_rotates (W : Scroll m B c) (x : Era m) (i : costG m B) (U : Pack m B) :
    p.bill W (Gloss.mot x i) (vest B x U) = payZ x (p.bill W i U) := Gloss.ch_h ..
lemma target_moves (x : Era m) (i : costG m B) : p.target (mot x i) = ρx x⁻¹ (p.target i) := by
  unfold Pinning.target Gloss.mot
  dsimp only
  rw [ρXp]
lemma cabin_rotates (W : Scroll m B c) (x : Era m) (U : Pack m B) :
    p.cabin W (vest B x U) = payZ x (p.cabin W U) := by
  unfold Pinning.cabin
  rw [← Equiv.sum_comp (eQ B x) (fun j => p.bill W j (vest B x U)), pay_m]
  exact sum_congr rfl fun i _ => bill_rotates ..

lemma cabin_split (W : Scroll m B c) (i : Axis) (x : Pack m B) :
    p.cabin W x = p.pass W i x + star (p.pass W i (Pbar m B i x)) := by
  unfold Pinning.cabin pass
  let y := slideM m i
  let v := Gloss.phat y
  have hv : v⁻¹ = v := by unfold v; rw [← κo, show y⁻¹=y from slide_inv ..]
  have hx (j : Index m) : ρx v j = y.adv j := rfl
  have hstar (z : ℂ) : payZ v z = star z := by unfold payZ; rw [show wageZ v=true from η_d m i]; rfl
  rw [← Equiv.sum_comp (eQ B v) (fun k => bonus (p.target k) i • p.bill W k (Pbar m B i x)),
      star_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [show Pbar m B i x = vest B v x from (ζ_b ..).symm, show eQ B v j = mot v j from rfl,
      bill_rotates, star_smul, target_moves, hv, hx]
  simp only [hstar, star_star, star_trivial, ← add_smul]
  rw [add_comm, show bonus (Trip.adv _ _) i+_=1 from bonusP i (p.target j), one_smul]

variable {W : Scroll m B c} (H : ScaleK A D W) (g : Budget B e d)
include H g
lemma term_seal (S : Stamp m B) : SealX m B (some (p.pin S)) S (p.term W S) (W.mint S) e := by
  unfold term; let x := currency H g.1 S (some (p.pin S)); split_ifs; exact x
  exact ⟨continuousOn_const,x.pos,fun _ _=> (le_of_eq (norm_zero)).trans x.pos,fun _ _ _=>rfl,
    x.connect,fun _ _ _ _ _ _ _=>rfl⟩
lemma term_local (S : Stamp m B) {x y:Pack m B} (h:x∈payer m B e) (f:y∈payer m B e)
    (v:Phase.Sample.AgreeF (faces m (p.pin S)) x.2 y.2)
    (k:Agrees (room m B (p.pin S)) x.1 y.1) : p.term W S x=p.term W S y := by
  have he := term_seal p H g S
  by_cases hz : W.mint S=0
  · rw [norm_le_zero_iff.mp ((he.norm _ h).trans hz.le), norm_le_zero_iff.mp ((he.norm _ f).trans hz.le)]
  by_cases heq : S.card ≤ scallop B
  · have hp := p.admissible S (he.connect hz) heq; exact he.matched _ _ hp h f (v.less (slab_ch hp)) k
  simp [term,heq]
lemma bill_continuousOn (w : costG m B) : ContinuousOn (p.bill W w) (payer m B e) :=
  (continuousOn_const (c:=rip m)).smul ((kilo_o _).comp_continuousOn ((p.term_seal H g _).cont.comp
    (vest_p w.1).continuousOn (fun x h=>voxel B w.1 e x h)))
lemma bill_matched (i:costG m B)(x y:Pack m B)(hx:x∈payer m B e)(hy:y∈payer m B e)
    (h:Phase.Sample.AgreeF (faces m (p.target i)) x.2 y.2)
    (hv:Agrees (room m B (p.target i)) x.1 y.1): p.bill W i x=p.bill W i y:= by
  unfold bill workQ; apply congrArg; apply congrArg; apply term_local p H g i.2 (voxel B _ e _ hx) (voxel B _ e _ hy)
  · intro j u; have he:(ρx i.1 j)∈ faces m (p.target i):= by unfold Pinning.target; rw [←ϕ_p]; exact mem_image_of_mem _ u
    exact congrArg (doveV i.1.charge) (h _ he)
  exact setN i.1 _ _ _ ((ξ_p i.1 B _).symm ▸ hv)
lemma bill_bound (S : costG m B) {x:Pack m B} (f:x∈payer m B e) : ‖p.bill W S x‖≤ rip m*W.mint S.2 := by
  unfold bill workQ; rw [norm_smul, pay_t,Real.norm_of_nonneg (by unfold rip; positivity)]
  apply mul_le_mul_of_nonneg_left ((p.term_seal H g _).norm _ (voxel B _ _ _ f)); unfold rip; positivity

variable (i : Axis)
lemma cabin_half_bound : ∃ K≥(0:ℝ), ∀ x∈payer m B e, ‖p.pass W i x‖≤K := by
  let f (S:costG m B) := ‖bonus (p.target S) i‖*(rip m*W.mint S.2)
  have he S : 0≤f S := mul_nonneg (norm_nonneg _) (mul_nonneg (by unfold rip; positivity) (p.term_seal H g _).pos)
  refine ⟨∑ S,f S,sum_nonneg (fun S _=>he S),fun x h=>?_⟩
  unfold pass; apply (norm_sum_le ..).trans; refine sum_le_sum fun S _=> ?_
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (bill_bound p H g S h) (norm_nonneg _)
lemma cabin_half_continuousOn : ContinuousOn (p.pass W i) (payer m B e):=
  continuousOn_finsetSum _ fun j _=> (continuousOn_const (c:=bonus (p.target j) i)).smul (bill_continuousOn p H g j)
lemma cabin_half_local (x y:Pack m B)(hx:x∈payer m B e)(hy:y∈payer m B e)
    (t:NorthOf m B i x y):p.pass W i x=p.pass W i y:=by
  apply sum_congr rfl; intro j _; by_cases k:p.target j∈ seaM m i
  · rw [bill_matched p H g j x y hx hy (t.labels.less (level_keep i k)) (fun e x y=> t.gaugeS e (plane_room i k x) (plane_room i k y))]
  simp [bonus,k]
lemma cabin_split_sewn (x y z:Pack m B)(β:ℝ)(f:tiedK m B i x y z∈TallyR m B e β):
    p.cabin W (tiedK m B i x y z) = p.pass W i (tiedK m B i x y y) + star (p.pass W i (tiedK m B i x z z)):=by
  have he := (RP.apt ..).mp f; have hg := tallyP f
  rw [cabin_split p W i,sew i,cabin_half_local p H g i _ _ hg (tallyP he.1) (strum i x y z y),
    cabin_half_local p H g i _ _ (by rw [←sew]; exact Mir.Trip.dominated _ _ hg) (tallyP he.2) (strum i x z y z)]
lemma cabin_bound : ∃ K≥(0:ℝ), ∀ x∈payer m B e, ‖p.cabin W x‖≤K := by
  obtain ⟨v,k,L⟩ := p.cabin_half_bound H g 0
  exact ⟨v+v,by positivity,fun x h=>by rw [cabin_split p W 0]; apply (norm_add_le ..).trans; rw [norm_star]; exact add_le_add (L x h) (L _ (dominated _ _ h))⟩
lemma cabin_continuousOn : ContinuousOn (p.cabin W) (payer m B e) :=
  continuousOn_finsetSum _ fun j _ => p.bill_continuousOn H g j
end Pinning

/-- Same convention as `shireF/hoistF` including order and `linearB`, negative-log
cabin rule. `cut` is the antiperiodic seam index (background `northZ`, changed by
reindexing in proofs). `β` the heat **history's** top inverse coupling. Use
`net ... 0`, i.e., only `water` product there, as required in `Lives_B`. -/
def heatTerm (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t e u : ℝ)
    (cut : Foot m B) (f : RP.Test m B) (x : Pack m B) : ℂ :=
  ↑(Nova.primal clip (Domain m B) β t x.1) * (TallyR m B e 0).indicator
    (fun w => (net m B 0 w : ℂ) * Complex.exp (-(1:ℂ)*p.cabin W w) *
      inner ℂ (linearB (CSide m B))
        (acts (f w * quant (n := Xmind m B) (grow (wiel m B cut w.1) u))
          (pairWave (n := Xmind m B) (Phase.pair m B w.1 w.2)))) x

def heatNum (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t e u : ℝ)
    (cut : Foot m B) (f : RP.Test m B) : ℂ :=
  ∫ x, heatTerm p W clip β t e u cut f x ∂wheel m B

/-- Scope check for the preceding defs; includes the installed donor. -/
theorem heat_db (W : Scroll m B c) (clip : Clip) (β t e u : ℝ)
    (cut : Foot m B) (f : RP.Test m B) :
    heatTerm (originalPinning m B) W clip β t e u cut f =
      RP.Str.hoistF clip t β W e 0 u 1 cut f := by
  funext x; unfold heatTerm RP.Str.hoistF RP.Str.ratioRF RP.Str.amplitudeF
  rfl

end YM.CF.Buffered
