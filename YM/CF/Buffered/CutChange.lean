import YM.CF.Buffered.Band
import YM.CF.Buffered.Trace

/-!
# The hot integral: reindex to put the non-wrap seam at the given plane

Translate exactly (including anticut signs). Then change the location of the
anticut in the axial coordinate only, at fixed cutoff/period. We do this for
the `VolumeBurn` hot integral (arbitrary `Pinning`), for bounded Borel tests.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure Nacre Window Tulip Skye Brace
attribute [local instance] opCStarAlgebra
variable {m B n : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "N" => CSide m B
local notation "Wμ" => wheel m B
local notation "U₊" => upperP (CSide m B)
local notation "β₀" => Brace.northZ m B

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)

private lemma move_fermion (Yy : Side) (t t' : FC (Model Yy)) (U : UNI (Model Yy))
    (H H' T0 T0' : Op (Model Yy)) (v : twist (quantU U) t=t') (g : congrC U T0=T0')
    (p : twist U H=H') (q : acts (quantU U).val (linearB Yy)=linearB Yy) :
    inner ℂ (linearB Yy) (acts (t*quant (grow H u)) (pairWave T0))=inner ℂ (linearB Yy) (acts (t'*quant (grow H' u)) (pairWave T0')) := by
  rw [←v,←g,←p,←quant_flow]
  unfold congrC; rw [←pair_cov, ← map_mul]; exact (bra U q _ _).symm
/-- Fringe change of basis. -/
lemma heatTerm_cut (l v : Foot m B) (f f' : RP.Test m B) (e : ℝ) (x : X)
    (h : f' x = twist (quantU (fringe l v)) (f x)) :
    heatTerm p W clip β t e u l f x = heatTerm p W clip β t e u v f' x := by
  unfold heatTerm
  by_cases y : x∈TallyR m B e 0; swap
  · rw [Set.indicator_of_notMem y, Set.indicator_of_notMem y]
  rw [Set.indicator_of_mem y, Set.indicator_of_mem y]
  apply congrArg (fun a:ℂ => (primal clip (Domain m B) β t x.1:ℂ) * a)
  -- inner rotation with precisely these phases
  apply congrArg (fun a:ℂ => ((net m B 0 x:ℂ)*Complex.exp (-(1:ℂ)*p.cabin W x)) * a)
  exact move_fermion u _ _ _ (fringe l v) _ _ _ _ h.symm (grade_fringe ..) (swingFringe l v _) (fixedSign l v)
section translation
-- z here a cover displacement in units of B matter sites (2B gauge sites) for Trip translations.
def shiftTrip (m : Side) (z : Cover) := northTrip m (wrap (More m) z)
lemma shift_tor (z : Cover) : torShift B (shiftTrip m z) = wrap _ (2 • (B.val • z)) := by
  rw [torShift,paneShift, show (shiftTrip m z).move = wrap _ z from rfl,Ratio.root_embed,Ratio.root_embed,Ratio.embed_wrap, Ratio.embed_wrap];
  rw [smul_comm]; rfl
lemma shift_anon (z : Cover) (x : Seat N) : (lagX (B.val • z)).anon N x=run B (shiftTrip m z) x := by
  rw [run,shift_tor]; rfl
lemma shift_pack (z : Cover) (x : Pack m B) : (onPack B (shiftTrip m z) x).1 = Yg (lagX (B.val • z)) x.1 := by
  unfold onPack Mir.Trip.through; dsimp only; rw [shift_tor]; rfl
lemma shift_site (z : Cover) : fperm m B (shiftTrip m z) = Tofu (lagX (B.val • z)) N := by
  ext x : 1; apply Tenant.needle; change node _=node ((lagX _).mills _ _)
  rw [Shape.nodex,shift_anon, Mir.Trip.track]
/-- Antiperiodic signed translation on the spatial Fock indexing. -/
def shiftFrame (z : Cover) (n : Side) := mealU (lagX z) 1 inert n
lemma shiftFrame_matrix (z : Cover) : (shiftFrame z n).val=
    jump (Tofu (lagX z) n) (fun x => (lagX z).payA x • (1 : Op (SpinIdx × SU.Slot))) := by
  unfold shiftFrame mealU portX; dsimp only; apply congrArg (jump (Tofu (lagX z) n)); ext1 x
  exact congrArg ((lagX z).payA x • ·) Matrix.one_kronecker_one
lemma shift_field (z : Cover) (x : Site n → Vect) : congrC (shiftFrame z n) (Cfield x)=Cfield (x ∘ Tofu (lagX z) n) := by
  have he : ccU (shiftFrame z n)=shiftFrame z n := by
    apply Subtype.ext; change cc (shiftFrame z n).val=_; rw [shiftFrame_matrix]; simp [jump_cc,Shape.real_payA]
  rw [congr_form,he,←twist_formula]; apply Mir.twist_comm
  rw [shiftFrame_matrix]; simp only [Cfield,jump_mul, Equiv.refl_trans, Equiv.trans_refl, Equiv.refl_apply,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul,mul_one,Function.comp_apply]
lemma shift_bra (z : Cover) (n : Side) : acts (quantU (shiftFrame z n)).val (linearB n)=linearB n :=
  turnsV _ (by rw [plane_diag]; change sings false _ (spin _ _ _) = _ ; unfold shiftFrame; rw [Scroll.swivel (lagX z) (1:UNI SpinIdx) inert]; congr 1; exact Fock.one_des _)
    (shift_field z (uniqueR n))
lemma shift_pair (z : Cover) (x : Pack m B) : congrC (shiftFrame (B.val • z) N) (Phase.pair m B x.1 x.2)=
    Phase.pair m B (onPack B (shiftTrip m z) x).1 (onPack B (shiftTrip m z) x).2 := by
  let i := shiftTrip m z
  have he (s : ArrayF m) (t : Sq) : bow m B (through B (shiftTrip m z) x.1) (i.riseF s) t =
      congrC (shiftFrame (B.val • z) N) (bow m B x.1 s t) := by
    rw [bow,played,shift_site]; exact (shift_field ..).symm
  exact (he (slot m x.2) (stick 0)).symm
lemma heatTerm_shift (z : Cover) (f f' : RP.Test m B) (e : ℝ) (x : X)
    (h : f' (onPack B (shiftTrip m z) x) = twist (quantU (shiftFrame (B.val • z) N)) (f x)) :
    heatTerm p W clip β t e u β₀ f x = heatTerm p W clip β t e u β₀ f' (onPack B (shiftTrip m z) x) := by
  classical
  let a := onPack B (shiftTrip m z) x
  let s := shiftFrame (B.val • z) N
  have hx : twist s (wiel m B β₀ x.1)=wiel m B β₀ a.1 := by
    unfold a; rw [shift_pack]; exact shutH (lagX _) 1 inert calmSX x.1
  have hc : p.cabin W a=p.cabin W x := by
    unfold a; rw [←Gloss.ζ_b,p.cabin_rotates]; unfold payZ; rw [Gloss.η_x (shiftTrip m z) (fun i=>rfl)]; rfl
  unfold heatTerm; rw [primal_trip]
  by_cases y : x∈ TallyR m B e 0; swap
  · rw [Set.indicator_of_notMem y, Set.indicator_of_notMem (fun t=>y ((turn_ineq (e:=e) (β:=0) (shiftTrip m z) x).mpr t))]
  rw [Set.indicator_of_mem y, Set.indicator_of_mem ((turn_ineq ..).mp y), newbill]
  unfold a at hc
  rw [hc]
  apply congrArg ((primal clip (Domain m B) β t x.1:ℂ) * ·)
  apply congrArg (fun a:ℂ => ((net m B 0 x:ℂ)*Complex.exp (-(1:ℂ)*p.cabin W x)) * a)
  exact move_fermion u _ _ _ s _ _ _ _ h.symm (shift_pair z x) hx (shift_bra ..)
lemma heatNum_shift (z : Cover) (f f' : RP.Test m B) (e : ℝ)
    (h : ∀ x,f' (onPack B (shiftTrip m z) x)=twist (quantU (shiftFrame (B.val • z) N)) (f x)) :
    heatNum p W clip β t e u β₀ f = heatNum p W clip β t e u β₀ f' := by
  unfold heatNum; nth_rw 2 [← use_trip (shiftTrip m z)]; exact integral_congr_ae (Eventually.of_forall (fun x=> heatTerm_shift p W clip β t u z f f' e x (h x)))
end translation
end YM.CF.Buffered.Heat
