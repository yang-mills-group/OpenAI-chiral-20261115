import YM.CF.Vp929.Ledger.Roof
import YM.CF.Vp929.Ladder.Record
import YM.CF.Vp929.Analysis.Ladder

/-! Reference calculation on the whole geometric ladder. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h x delay : ℝ} {D C R0 : ℝ → ℝ} {m m' N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {P : Prescription R B} {N0 k k' : ℕ} {T : Month x 1 6 2 N0 V W}
  (H : Service V U W J q h D C R0 P N0 delay)
  (U₀ : Retag V U W J h N0 delay)
  (hh : 1 ≤ h)
  (hp : ((R.L.val:ℝ)^4)⁻¹ < VolumeRate.propagation)
local notation "ℓ" => R.L
local notation "M" => oYY V N0 J x
local notation "pE" => (dleaf R.L x/1000+dleaf R.L (hat R.L x 1)/1000 + C x/(R.L.val:ℝ)^4)

-- reindex the actual rack, not re-choosing an arbitrary new map.
lemma gowns {F_:(s:Side)→Scree.Loom s→Prop}(pF:RackedΛ F_ J) (q:Chi)(K:Side)(n t:Side)(x:n=K*N)(u:J.h ≤ K.val)(g:t=K*R.L*N)(G:Ratio (Scree.mid n B) (Scree.mid t B))(hp:G.count=R.L): ∃ WV:Scree.Loom (Scree.mid n B), RocketV V _ _ U W J WV G q ∧ F_ _ WV:=by
 subst n t; exact ⟨J.rack _ u, ⟨J.roof _ u,u.trans (size_q K B N),fun t Z V=> J.tick u (le_trans u (Nat.le_mul_of_pos_right _ R.L.property)) G hp q Z t V⟩,pF _ u⟩

/-- Eventual purchases needed on the auxiliary calendars. -/
structure Walker (T : Month x 1 6 2 N0 V W) (J : Robes N V W) (z delay : ℝ) (D : ℝ → ℝ) : Prop where
  music {m : Side} (hm : (oYY V N0 J x).val ≤ m.val) (k : ℕ) (A : V.L.Last U W.C m k) : A.music z
  allow {m : Side} (hm : (oYY V N0 J x).val ≤ m.val) (k : ℕ) (A : V.L.Last U W.C m k) : 0<k → |A.move 0| + billX R.L/512 ≤ (strip x/8)/8
  width : 8*z ≤ x
  bank : T.q = grainZ V W N0 x
  pole (i : ℕ) : (T.a i).threshold ≤ J.k
  isle (i : ℕ) : Rue.IsleB SU.group (T.a i).threshold
  large : 61 ≤ (oYY V N0 J x).val
  size : T.q ≤ (oYY V N0 J x).val
  sizeC : W.C.i ≤ (oYY V N0 J x).val
  tiny : commonQ R B (oYY V N0 J x) 0 ≤ Real.exp (- (R.L.val:ℝ))
  late : delay ≤ x
  prices (y) : x ≤ y → Prices R.L D y
variable {z E a : ℝ} (w : Walker T J z delay D)
section
omit hp
include H U₀ hh w
local notation "Z" => Branch.stopEarn T
/-- Downward extension (prove by induction how far we can reach *up* from the stopping volume).
We use n=m*sched etc later; here y is the reference aperture argument at top, with BudgetPoint u
at that hat, carried unchanged across all lower steps. k is total height of current branch. -/
theorem reach {F_:(s:Side)→Scree.Loom s→Prop} (pF:RackedΛ F_ J) (p0 : ∀ (X : GramM (cell (oYY V N0 J x) B R.L 0)) (S : Scree.Loom (cell (oYY V N0 J x) B R.L 0)), RoomAt (h:=h) J N0 x X S → E ≤ ‖compensated U X S‖)
    (he : Real.exp (-a) ≤ E) (ha : 0≤a) (Ht : -a≤ Branch.stopEarn T) (Hz : VolumeRate.propagation * (Branch.stopEarn T + a) > Branch.stopEarn T + pE + a / (R.L.val:ℝ)^4)
    {u : BudgetPoint} {y : ℝ} (hy : delay ≤ y) (ht : Location.Boot y u) (Hk : u.threshold ≤ J.k) (hi : Rue.IsleB SU.group u.threshold)
    (l : ℕ) (hk : 0<k) (hm : m=rung R (oYY V N0 J x) l)
    (hl : y ≤ hat R.L x k) (hu : hat R.L x (k+l) ≤ 4/3*y)
    (A : Branch W m k x N0) (v : A.T=T) (p : A.Bon J q h D delay) (t : A.Represents P u)
    (F : Record A P) : ∃ x : ℝ, |x|≤1/8 ∧ Real.exp (-a*sites (cell m B R.L 0)) ≤ ‖F.f x‖ := by
  induction l generalizing m k with
  | zero =>
    have hm: m=M := by simpa [rung,Vale.mesh] using hm
    refine ⟨0,by norm_num,?_⟩; rw [Complex.ofReal_zero]; exact (Real.exp_monotone (by nlinarith [sites_pos (cell m B R.L 0)])).trans (he.trans (Branch.in_window H hh p hm p0 F))
  | succ l ih =>
    let m':= rung R M l
    have hM : m=m'*ℓ:= by rw [hm]; exact mesh_succ ..
    let A0:= mesh (seat_u V J x N0) ℓ l; have hb' : J.h ≤ A0.val := le_trans (by change _ ≤ J.h+_+1; omega) (mesh_ge ..); have hm' : m'=A0*N:= Month.ruler ..
    have ps : ∃ S : Scree.Loom (cell m' B ℓ 0), RocketV V (mesh m' ℓ 0) (mesh m' ℓ 1) U W J S (apt m' B ℓ 0) q ∧ F_ _ S := by
      rw [hm']; refine gowns pF q (mesh A0 ℓ 0) _ _ (Month.ruler ..) (Grace.Robes.stretch J hb' _) ?_ _ rfl
      rw [Month.ruler,show 1=0+1 from rfl,mesh_succ]

    obtain ⟨S',hp',_⟩:=ps; have hv': (oYY V N0 J x).val ≤ m'.val := mesh_ge ..; have hv : (oYY V N0 J x).val ≤ m.val := hm ▸ mesh_ge ..
    obtain ⟨A₁,t',hf,hA⟩:= extend_under A.toSpine (p.can) hM (w.sizeC.trans hv') (commonFreq w.tiny (n:=0) (n':=0) (k:=l) le_rfl) S' hp' ((v.symm ▸ w.size).trans hv') (w.large.trans hv')
    have kw : hat R.L x (k+1+l) ≤ 4/3*y := by rw [show k+1+l=k+(l+1) by omega]; exact hu
    obtain ⟨U',hT⟩:= Branch.retag_build U₀ H A₁ (show A₁.Can J q T from v ▸ hA) w.prices w.late (w.music hv' _ _) w.width hy (hl.trans (hat_mono k.le_succ)) (le_trans (hat_mono (by omega : k+1≤k+1+l)) kw) u ht Hk hi
    let A':= (⟨A₁,T,U'⟩:Branch W m' (k+1) x N0); obtain ⟨F'⟩:= Branch.history H hh (A:=A') hT.1
    let V':= sites (cell m B ℓ 0); let s:= (R.L.val:ℝ)^4; have hV: 0 < V' := zero_lt_one.trans_le (sites_pos _); have e:= ih (by omega : 0<k+1) (show m'=rung R M l from rfl) (hl.trans (hat_mono k.le_succ)) kw A' rfl hT.1 hT.2 F'
    have hS: s≠0:= pow_ne_zero _ (by exact_mod_cast R.L.property.ne'); have hg: V'/s=sites (cell m' B ℓ 0):= by
      apply (div_eq_iff hS).mpr; exact (congrArg (fun m=> sites (mid m B)) (t'.mesh 0)).trans (sites_step ..)
    refine hop V' s Z pE a hV Ht Hz F.f F'.f F.ana (v ▸ F.budget) (hg.symm ▸ e) ?_
    intro y hy
    let r:= Rx x; have he':0<r:= Rx_pos (w.prices _ le_rfl).grade; have hY: |y*r| ≤ r/8:= by rw [abs_mul,abs_of_pos he']; nlinarith
    obtain ⟨g',Hg⟩:= Branch.existsSolve H hT.1 (z:=y*r) (by linarith)
    obtain ⟨τ,b,pτ,qτ,hτ⟩:= Branch.pay_next H (zero_le_one.trans hh) hk p t hT.1 hT.2 t' (w.allow hv' _ _ (by omega)) (y*r) hY (show Solved P A' _ g' from Hg)
    change |τ| ≤ r/4 at pτ
    refine ⟨τ/r,by rw [abs_div,abs_of_pos he']; apply (div_le_iff₀ he').2; linarith,?_⟩
    have hp:= range_scale (x:=x) (w.prices _ le_rfl).grade (t:=τ/r); rw [div_mul_cancel₀ τ he'.ne'] at hp; rw [F'.real y ((range_scale (w.prices _ le_rfl).grade).mpr (by linarith)) g' Hg,F.real (τ/r) (hp.mpr (by linarith)) b (by convert qτ; exact div_mul_cancel₀ τ he'.ne')]; rw [neg_mul]; exact hτ
end
include H U₀ hh w hp
theorem uniform_slit {F_:(s:Side)→Scree.Loom s→Prop}(pF:RackedΛ F_ J) (p0 : ∃ u > (0:ℝ), ∀ (X : GramM (cell (oYY V N0 J x) B R.L 0)) (S:Scree.Loom (cell (oYY V N0 J x) B R.L 0)), RoomAt (h:=h) J N0 x X S → u ≤ ‖compensated U X S‖) :
    ∃ a : ℝ, ∀ l k : ℕ, ∀ (A : Branch W (rung R M l) k x N0), 0<k → hat R.L x (k+l) ≤ 4/3*hat R.L x k → A.T=T → A.Bon J q h D delay → A.Represents P (T.a k) →
    ∀ F : Record A P, ∃ x' : ℝ, |x'| ≤ 1/8 ∧ Real.exp (-a*sites (cell (rung R M l) B R.L 0)) ≤ ‖F.f x'‖ := by
  obtain ⟨c,hc,Hc⟩:= p0; obtain ⟨a,ha,hA,t,z⟩:= barrier hc (pow_pos (Nat.cast_pos.mpr R.L.property) 4) hp (stopEarn T) pE
  refine ⟨a,fun l k A hk p u v s=> reach H U₀ hh w pF Hc z ha hA t (w.late.trans (Vale.crown ..)) ?_ (w.pole k) (w.isle k) l hk rfl le_rfl p A u v s⟩
  obtain ⟨p,u,v,t,z⟩:= T.boot k; exact ⟨p,u,v,t,z⟩
end YM.CF.Py.Rate
