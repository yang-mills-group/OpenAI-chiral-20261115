import YM.CF.Vp929.Stage.Limsup
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
namespace Branch
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
local notation "F" => dleaf R.L
variable (H : Service V U W J q h D C R0 P N0 delay) (hh : 1≤h)

-- More generally the inputs from beyond the steps using the prescription can be arbitrary (even
-- unprepared at u_m); no convergence assertion outside the portion already at the epsilon/1000
-- prices. The pivot theorem above uses uniform insensitivity in the version Branch.limsup (for
-- two equal horizon full prepared branches), since the only use it needs is for switched launch.
-- We include this one for clarity on insensitivity to prepared upper steps.
namespace CommonRun

variable (g : ℕ) (A:Spine W m k) (T:Month x 1 6 2 N0 V W)

abbrev payer(i:ℕ) := P _ _ (A.address i) (X i) (T.a i) (T.a (i+1))
structure Supply (B b:Side)(R:Patch) where
 β :ℕ→ℝ
 arrays (i:ℕ): Corr (cell b B R.L i)
 off:ℕ→ℂ
variable (S:Supply B m R)
abbrev matriarch (i:ℕ): GramM (cell m B R.L i) := construct (T.a i) (V.L.path (k-i)) K.top.clip (A.last.Q i) (S.β i) (S.arrays i) (S.off i)
abbrev demands (i:ℕ) := (payer P A T i).posted (S.β (i+1)) (S.arrays (i+1))
-- g is top of common portion already paid epsilon/1000. So g=u_m-1 is fine in the lemma;
-- prepared input to step u_m-1 doesn't need to pay. Keep Spine(horizon) fixed arbitrarily.
structure PaidRun (P:Prescription R B) (g:ℕ)(A:Spine W m k)(T:Month x 1 6 2 N0 V W)(h:ℝ) (S:Supply B m R):Prop where
 legal(i:ℕ)(ht:i≤g):entersReal (X i) (S.β i)
 tables(i:ℕ)(t:i≤g): Charged (T.a i) (A.last.Q i) K.j R.L.val h (dleaf R.L (X i)/1000) (S.arrays i)
 step(i:ℕ)(t:i+1 ≤ g) : S.arrays i= (payer P A T i).realArr (S.β (i+1)) (S.arrays (i+1))
 shift(i:ℕ)(t:i+1 ≤ g) : S.β i = S.β (i+1)+ (A.address i).movement V-demands P A T S i
-- at level0 use any anchor within entersReal (fits uses here); no assumptions above g at all
variable {P g A T S} {S' :Supply B m R}
variable (Z:PaidRun P g A T h S)(U':PaidRun P g A T h S') (u:g≤k) (hp: S.β 0=S'.β 0)
    (t:A.Can J q T)(late:delay ≤ x)(p0:∀ y ≥ x, Prices R.L D y)
local notation "ζ" => demands P A T S
local notation "ζ'" => demands P A T S'
include Z U' hp
private lemma shift_diff (i:ℕ)(v:i ≤ g) : S.β i-S'.β i=∑ j∈range i,(demands P A T S j-demands P A T S' j):=by
 induction i with
 | zero=> rw [hp,sub_self]; simp
 | succ i ih=>
   let q:= ih (Nat.le_of_lt v); rw [Z.shift i v,U'.shift i v] at q; rw [Finset.sum_range_succ,←q]; ring
include u H t late p0
private lemma totCs (i:ℕ) : (∑ j∈range i, D (X j)) ≤ strip (X i)*(1/400):=by
 let t i:=strip (X i); have h(i):= p0 (X i) (Vale.crown ..); have p(j) : 0 < t j := strip_pos (h j).grade
 apply le_trans _ (mul_le_mul_of_nonneg_left (prices_sum p0 i) (p i).le)
 rw [mul_sum]; refine sum_le_sum fun j e=>?_ ; set y:= D (X j); have hY:0 ≤ y:=(h j).bank; let b:=t (j+1); have hx':0<b:=p _
 change y ≤ t i*(y/b); rw [←mul_div_assoc]; exact (le_div_iff₀ hx').2 (le_trans (mul_le_mul_of_nonneg_left ((h _).increase _ (hat_mono (mem_range.mp e))) hY) (le_of_eq (mul_comm ..)))
omit U' hp in
private lemma earns_run(i:ℕ)(v:i+1≤g) : |demands P A T S i| ≤ D (X i):=by
 let hq(i):= p0 (X i) (Vale.crown ..); let c:= H.provides _ _ _ _ _ _ (late.trans (Vale.crown ..)) (t.request i (v.trans u)); let ku:=S.β (i+1); let G:=S.arrays (i+1)
 have ht(i)(t:i≤g): enters (X i) ((S.β i:ℝ):ℂ):=by
    refine ⟨?_,?_,?_⟩; · simp only [Complex.ofReal_re]; linarith [(hq i).grade,(Z.legal i t).1]
    · simp only [Complex.ofReal_re]; linarith [(hq i).grade,(Z.legal i t).2]
    rw [Complex.ofReal_im,abs_zero]; linarith [strip_pos (hq i).grade]
 have hx:i < i+1:=Nat.lt_succ_self _; have hh:(F (X (i+1)))/1000 ≤ 3*F (X i):=by
    have h:= (hq i).leaf_mono (X (i+1)) (hat_mono (by omega)); linarith [(hq i).leaf]
 have hy:0≤3*F (X i):=by linarith [(hq i).leaf]
 exact le_trans (Complex.abs_re_le_norm _) ((c.cost (ku:ℂ) (G,0) (hat_step i ▸ ht (i+1) v) ⟨(Z.tables _ v).mono hh, Charged.zero.mono hy⟩).2)
lemma comparison (r i:ℕ)(hk:i+r≤g) : Cost (T.a i) h (F (X i)*decline r) (S.arrays i-S'.arrays i) ∧ |S.β i-S'.β i| ≤ strip (X i)*decline r:=by
 let D₁(j):=ζ j; let D₂(j):=ζ' j; have clocks(j):=p0 _ (show x ≤ X j from Vale.crown ..)
 induction r generalizing i with
 | zero=>
   have he:=Z.tables i hk; have ht:=U'.tables i hk; constructor
   · exact (he.toCost.sub ht.toCost).mono (by simp only [decline,pow_zero,mul_one]; linarith [(clocks i).leaf])
   rw [shift_diff Z U' hp i hk]; have hu(j)(e:j∈range i): |ζ j-ζ' j| ≤ D (X j)+D (X j):= le_trans (abs_sub ..) (add_le_add (earns_run H Z u t late p0 _ (by have hh:= mem_range.mp e; omega)) (earns_run H U' u t late p0 _ (by have hh:= mem_range.mp e; omega))); refine (Finset.abs_sum_le_sum_abs ..).trans <| le_trans (sum_le_sum hu) ?_; rw [sum_add_distrib]; have he:= totCs H Z U' u hp t late p0 i; simp only [decline,pow_zero,mul_one]; linarith [strip_pos (clocks i).grade]
 | succ r ih=>
   have η:0≤decline r:=by unfold decline; positivity
   have stars(j)(v:j+1+r≤g): Cost (T.a j) h (F (X j)*((decline r+decline r)/4)) (S.arrays j-S'.arrays j) ∧ |ζ j-ζ' j| ≤ 100* D (X j)*(decline r+decline r) := by
     let e:j+1 ≤ g:=by omega
     obtain ⟨hv,hY⟩:= ih (j+1) v
     let hg:= H.provides _ _ _ _ _ _ (late.trans (Vale.crown ..)) (t.request j (e.trans u)); rw [Z.step j e,U'.step j e]; refine hg.stars _ _ _ _ _ _ ?_ η η (hat_step j ▸ hv) (hat_step j ▸ hY)
     rintro w ht; rcases ht with H|q
     · subst w; exact ⟨hat_step j ▸ Z.legal _ e, hat_step j ▸ Z.tables _ e⟩
     rw [Set.mem_singleton_iff] at q; subst w; exact ⟨hat_step j ▸ U'.legal _ e,hat_step j ▸ U'.tables _ e⟩
   constructor
   · exact (stars i (by omega)).1.mono (by unfold decline; rw [pow_succ]; exact le_of_eq (by ring))
   rw [shift_diff Z U' hp i (by omega)]
   refine (Finset.abs_sum_le_sum_abs ..).trans <| le_trans (sum_le_sum fun j p=> (stars j (by have ht:= mem_range.mp p; omega)).2) ?_
   rw [←sum_mul,←mul_sum]; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (totCs H Z U' u hp t late p0 i) (by norm_num : (0:ℝ)≤100)) (add_nonneg η η)) (le_of_eq ?_); unfold decline; rw [pow_succ]; ring
open Graph Graph.Diff Graph.Angle Window
omit Z U' u H t late p0 hp in
private lemma diff_mono {n B:Side} {U' : Grasp V.U B d} {Xx Xx' : GramM (mid n B)} {S S'} (ε:ℝ) (L:∀ i, ‖field U' Xx S i-field U' Xx' S' i‖ ≤ ε) (g:Integrable (fun i=>beamZ _ (field U' Xx S i)) (city _)) (g':Integrable (fun i=>beamZ _ (field U' Xx' S' i)) (city _)) : ‖compensated U' Xx S-compensated U' Xx' S'‖ ≤ ε := by
  rw [←integral_beam,←integral_beam,←integral_sub g g']
  have h(i:Orbit (mid n B)): ‖beamZ _ (field U' Xx S i)-beamZ _ (field U' Xx' S' i)‖ ≤ ε:= by
    unfold beamZ; rw [←inner_sub_right]; exact (norm_inner_le_norm ..).trans (by rw [(tickB (mid n B)).2,one_mul]; exact L i)
  exact (norm_integral_le_of_norm_le (integrable_const ε) (Eventually.of_forall h)).trans_eq (by rw [integral_const,probReal_univ,one_smul])
omit U' hp in
private lemma warm (i:ℕ)(v:i≤g) : Integrable (fun x=>beamZ _ (field U (matriarch A T S i) (A.loom i) x)) (city _):=by
  let U':= (t.cape i).paid; have he:= denInt W (I:=A.last.Q i) (show Roof _ J.k d J.n (A.loom i) from {U' with paid:=fun j=>(U'.paid j).shrink J.hr.le}) (k-i) (J.gran.trans (t.cape i).size) (S.β i) (S.off i) ((Z.tables i v).toCost.lot (S.β i) (S.off i))
  let h: Integrable (denZ (matriarch A T S i) U (A.loom i)) (city (M i)) := Integrable.of_bound he.meas.aestronglyMeasurable _ (Eventually.of_forall he.cost.choose_spec)
  exact (innerSL ℂ (mateK (M i)) |>.restrictScalars ℝ).integrable_comp (h.smul (Complex.exp (-(S.off i))))
omit t Z U' hp u
include hh
lemma prepared_limsup (ε : ℝ) (he : 0<ε) (i : ℕ) : ∀ᶠ g : ℕ in atTop,
    ∀ (k:ℕ),g≤k→∀ (A:Spine W m k),A.Can J q T→∀ S S':Supply B m R,PaidRun P g A T h S→PaidRun P g A T h S'→ S.β 0=S'.β 0 → let u:= matriarch A T S i; let v:= matriarch A T S' i; let s:= A.loom i; |u.beta-v.beta| ≤ ε ∧ (∀ y, ‖field U u s y-field U v s y‖ ≤ ε) ∧ ‖compensated U u s-compensated U v s‖ ≤ ε := by
  have clz(n):Prices _ _ (X n):= p0 (X n) (Vale.crown ..)
  let δ:= F (X i)/1000; let p:=T.a i; let N:= (M i); let Rr:= K.top.clip; let κ:= K.top.paths; let f:= taxPart V p (2*(X i))*sites N; let α:= Real.exp f; let w:= α*Real.exp (flagBill (M i) δ δ (cashU W.C))
  let D':= strip (X i); let u:= F (X i); have t:Tendsto decline atTop (𝓝 0):= by
    simpa only [mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul (2:ℝ))
  have θ:Tendsto (fun r=>Record.paceZ p N Rr κ (D'*decline r) (u*decline r)) atTop (𝓝 0):= by
    unfold Record.paceZ Graph.Diff.rankV; exact (by simpa only [mul_zero,zero_mul,add_zero] using! ((((t.const_mul D').mul_const (jumpTax p (More N) Rr κ)).const_mul 2).add (((t.const_mul u).mul_const ((More N).val^4 : ℝ)).const_mul 3)))
  have hf₁ : ∀ᶠ r : ℕ in atTop, D'*decline r ≤ ε:= (t.const_mul D').eventually (ge_mem_nhds (by simpa using he))
  have hf₂ : ∀ᶠ r : ℕ in atTop, (D'*decline r)*jumpTax p (More N) Rr κ ≤ 1/2:= ((t.const_mul D').mul_const _).eventually (ge_mem_nhds (by norm_num))
  have hf₃ : ∀ᶠ r : ℕ in atTop, (u*decline r)* ((More N).val:ℝ)^4 ≤ 1/2 := ((t.const_mul u).mul_const _).eventually (ge_mem_nhds (by norm_num))
  have hf₄ : ∀ᶠ r : ℕ in atTop, w*Record.paceZ p N Rr κ (D'*decline r) (u*decline r) ≤ ε:= (θ.const_mul w).eventually (ge_mem_nhds (by simpa using he))
  obtain ⟨r,p₁,p₂,p₃,p₄⟩:= (hf₁.and (hf₂.and (hf₃.and hf₄))).exists
  filter_upwards [eventually_ge_atTop (i+r)] with g' hk; intro k hg A av S S' H' H'' ht Zh Yh SV; let r':=decline r; let w':=Record.paceZ p N Rr κ (D'*r') (u*r')
  have hi:i≤ g':= (Nat.le_add_right i r).trans hk; let D0:= D'*decline r; let Vμ:=u*decline r
  obtain ⟨q₁,q₂⟩:= comparison H H' H'' hg ht av late p0 r i hk
  have e : Zh.p=p:=rfl; have e':Yh.p=p:=rfl
  have hc : Record.Cart Zh Yh h κ Vμ D0 := ⟨e.trans e'.symm,rfl,rfl,rfl,q₂,rfl,rfl, ⟨⟨q₁.inc.weight,fun _ v=> v.elim⟩,⟨q₁.dark.weight,fun _ v=> v.elim⟩⟩,e ▸ p₂,p₃⟩
  let T:= (av.cape i).paid; have hR: Roof _ J.k d J.n SV:={T with paid:=fun i=>(T.paid i).shrink J.hr.le}
  let g:= levelQ W.C; let C:= cashU W.C; have pw: Ledger h δ δ g C Zh:= frostQ ((H'.tables i hi).toCost.lot _ _) (zero_le_one.trans hh) (A.last.sound i); have pu:Ledger h δ δ g C Yh:= frostQ ((H''.tables i hi).toCost.lot _ _) (zero_le_one.trans hh) (A.last.sound i)
  have pv:=V.L.mood (k-i); have hu:=J.gran.trans (av.cape i).size; have hp:0≤δ:=div_nonneg (clz i).leaf.le (by norm_num)
  let F'(i:Orbit N):= Record.on_trace Zh Yh SV hR hu hc pv pw pu hh hp (cash_v _) (level_p _).le (paths_nonneg V) i
  have ha: 0 ≤ w' := by
    unfold w'; rw [←e]; exact Record.respects Zh Yh SV hR hu hc pv pw pu hh hp (cash_v _) (level_p _).le (paths_nonneg V)
  have hX (b:Orbit N) : past Yh b.1 ≤ α := by
    have ht: X i/2 ≤ Yh.beta ∧ Yh.beta ≤ 2* X i := by
      have hx:= p0 (X i) (Vale.crown ..); let h':= H''.legal i hi; change _ ≤ S'.β i ∧ S'.β i ≤ _; constructor <;> linarith [hx.grade,h'.1,h'.2]
    have h:= Window.energy_low Yh.p Yh.path Rr pv (b:=Yh.beta) (by linarith [(clz i).grade,ht.1]) b.1
    have ht' := ((neg_le.mp h).trans (tax_price V N ht.2)); rw [e'] at ht'
    unfold Graph.past; rw [e']; exact Real.exp_monotone ht'
  have hY(j:Orbit N) : ‖field U Zh SV j-field U Yh SV j‖ ≤ ε := by
      have he:= F' j; rw [e] at he; exact he.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hX _) (Real.exp_pos _).le) ha).trans p₄)
  exact ⟨q₂.trans p₁,hY,CommonRun.diff_mono _ hY (warm H H' hg av late p0 _ hi) (warm H H'' hg av late p0 _ hi)⟩
end CommonRun
end Branch
end YM.CF.Py.Rate
