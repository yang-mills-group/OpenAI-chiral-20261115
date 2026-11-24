import YM.SU5.LoomForce.Placement
import YM.SU5.LoomForce.SpinIncome

/-! Pull the Spin-table limit. Needs even the diagonal; use the resolution
prescription for exactly equal sites, never prices for accidentally-near pairs. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods
     Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear
     Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
     Classical
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open Ballad Hiro
open YM.Stationary (Gaia)

variable {s: ℕ→Side}{r:ℕ→ℕ}{U V:ℕ→ Cover}{M:ℕ→Jill.Male} {j : ℕ}
-- from Hiro.Morsel (its extraction argument adapted). Even retain on-diagonal appointments.
lemma expanseNear (L G:Twah.DirSpin)(X:Gaia)(u:Tendsto (fun i=> riseX (r i) (U i-V i)) atTop (𝓝 X))
    (e:X=0 → ∀ᶠ i in atTop,U i=V i) (W:Yard s (fun i=> (r i:ℝ))) (p:1 ≤ j) :
    Tendsto (fun i=>dietary (r i) (U i) (V i) L G (s i) j (M i)) atTop (𝓝 (shotL X L G)):=by
  by_cases h:X=0; swap; · exact roll_shot L G u h W p
  simp_rw [dietary,in_transcript]; let i:=sourceSlot; obtain ⟨c,hv,hT⟩:=lake_formal p
  have ht:=Emu.tally (L:=fun i=> (r i:ℝ)) (fun i=>too _) M (fun i=> lakeP _ j (M i)) (fun i=>0) W hv
    (by norm_num : (0:ℝ)<1) (fun x:Slot=>Eventually.of_forall fun i=>hT _ (W.even i) _ x) (alignedα L i)
    (alignedβ G i) U V X (Or.inr ⟨h,e h⟩) u p (fun _=>1)
  rw [show frank (alignedα L i) (alignedβ G i) X=shotL X L G from if_pos rfl] at ht; exact ht

lemma dietary_levy (L G : Twah.DirSpin) (w:1≤j)(r:ℕ→ℕ)(Q:Tendsto r atTop atTop) (W:∀ i,0<r i)
    (U V:ℕ→ Cover)(X:Gaia)(u:Tendsto (fun i=> riseX (r i) (U i-V i)) atTop (𝓝 X))
    (e:X=0 → ∀ᶠ i in atTop,U i=V i)(a:ℝ)(η:0<a):
     ∀ᶠ i in atTop,∀ᶠ N:Side in atTop,Even N.val →
       ∀ M:Jill.Male, dist (dietary (r i) (U i) (V i) L G N j M) (shotL X L G) ≤ a:=by
  by_contra h; obtain ⟨f,t,z⟩:= extraction_of_frequently_atTop (not_eventually.mp h)
  let u' (i:ℕ):=r (f i); have ht(i:ℕ):0<(u' i:ℝ):=by unfold u'; exact_mod_cast W (f i)
  choose Y m v p h using fun i=> (show ∃ (N:Side)(M:Jill.Male), Even N.val∧
      (u' i:ℝ)*Ember.pinch N≤ (2:ℝ)⁻¹^i∧ ¬ dist (dietary (r (f i)) (U (f i)) (V (f i)) L G N j M) (shotL X L G)≤ a from by
    obtain ⟨k,v⟩:=Glaze.pick_depth (p:=(show 0<(2:ℝ)⁻¹^i/(u' i:ℝ) from (by have e:= ht i; positivity)))
    have he:=z i; replace he :=not_eventually.mp he
    obtain ⟨N,h,vN⟩:= (he.and_eventually (eventually_ge_atTop (⟨k+1,by omega⟩:Side))).exists
    push Not at h; obtain ⟨H,M,g⟩:=h
    exact ⟨N,M,H,(mul_comm _ _).le.trans ((le_div_iff₀ (ht i)).1 (v (by change k+1 ≤ N.val at vN; omega))),g.not_ge⟩)
  let Q:= Q.comp t.tendsto_atTop
  have hx: Yard Y (fun i=> (u' i:ℝ)):= ⟨ht, tendsto_natCast_atTop_atTop.comp Q,squeeze_zero (fun i=>
    mul_nonneg (ht i).le (Ember.pinch_pos _).le) p (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),v⟩
  have H:= expanseNear (U:=U ∘ f) (V:=V ∘ f) (M:=m) L G X (r:=u') (u.comp t.tendsto_atTop)
    (fun v=> t.tendsto_atTop.eventually (e v)) hx w
  obtain ⟨i,f⟩:= (Metric.tendsto_nhds.mp H a η).exists; exact h _ f.le

open Py Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation Yoke
open EmberWind

variable (P : Spine) {I : Type*} {A : ℝ}
local notation "Y" => P.run
local notation "Λ" => P.par

def costsWith (d : I → I → ℂ) : Chart (loomZ I) := fun i j=>
  if i.2.2 then if j.2.2 then 0 else if i.2.1=j.2.1 then d i.1 j.1 else 0
  else if j.2.2 then -(if j.2.1=i.2.1 then d j.1 i.1 else 0) else 0

def wakeZ (b : I → Twah.DirSpin) (y : I → Gaia) : Chart (loomZ I) :=
  costsWith (fun i j=> shotL (y i-y j) (b i) (b j))
def readsZ (A : ℝ) (W : I → Staff) (s n : ℕ) := pairPrice (zoomR Λ A s)
    (fun i=> (W i).u) (fun i=> (W i).spin) (matterSide P s n)
    (Λ).K.j (RootBook Y (takenVolume P n) (takenCutoff P n) s).J.M

omit P in
lemma cure (R:ℕ)(v:I → Cover) (L : I → Twah.DirSpin) {b:Side} (G:Even b.val) (j:ℕ) (M:Jill.Male) :
    pairPrice R v L b j M = costsWith (fun i k=> dietary R (v i) (v k) (L i) (L k) b j M) := by
  funext x y; unfold pairPrice costsWith idPrice
  by_cases t:x.2.2
  · simp only [t,↓reduceIte]; by_cases w:y.2.2
    · simp only [w,↓reduceIte]; exact calm ..
    simp only [w,Bool.false_eq_true,↓reduceIte]; exact rank_hint R _ _ _ _ G _ _
  simp only [t,Bool.false_eq_true,↓reduceIte]; by_cases w:y.2.2
  · simp only [w,↓reduceIte]; rw [flipcost,rank_hint (Ht:=G)]
  simp only [w,Bool.false_eq_true,↓reduceIte]; exact still ..

variable {W : ℕ → I → Staff} {L : I → Twah.DirSpin} {y : I → Gaia}
theorem reachingZ {f : ℕ → ℕ} (hA : 0 < A) (p : ∀ i, Appoint P.par A (fun s=> (W s i).u) (y i))
    (u : ∀ i j, y i=y j → ∀ᶠ s in atTop, (W s i).u=(W s j).u) (t : ∀ i s, (W s i).spin=L i)
    (B : StrictMono f) (i j : loomZ I) :
    Tendsto (fun n : ℕ × ℕ => readsZ P A (W n.1) n.1 (f n.2) i j) successive (𝓝 (wakeZ L y i j)) := by
  let d (c : ℕ × ℕ) (i j:I) := dietary (zoomR Λ A c.1) (W c.1 i).u (W c.1 j).u (L i) (L j)
      (matterSide P c.1 (f c.2)) (Λ).K.j (RootBook Y (takenVolume P (f c.2)) (takenCutoff P (f c.2)) c.1).J.M
  have ht : (fun n : ℕ × ℕ => readsZ P A (W n.1) n.1 (f n.2) i j)= fun n=> costsWith (d n) i j := by
    funext n; unfold readsZ; rw [cure (G:=Vale.val_e ..)]; simp_rw [t]; rfl
  have he(i j:I): Tendsto (fun n=>d n i j) successive (𝓝 (shotL (y i-y j) (L i) (L j))) := by
    apply Metric.tendsto_nhds.mpr; intro ε hε
    apply eventually_curry_iff.mpr
    let U i := fun n:ℕ=> (W n i).u
    have hf(i:I): Tendsto (fun n=>riseX (zoomR Λ A n) (U i n)) atTop (𝓝 (y i)) := (appoint_as Λ hA _ _).mp (p i)
    filter_upwards [dietary_levy (L i) (L j) (nontrivial_spin Λ) (zoomR Λ A) (zoom_grows Λ hA)
      (fun s=>Nat.ceil_pos.mpr (half_pos (BProof.coin_pos ..))) (U i) (U j) (y i-y j)
      (((hf i).sub (hf j)).congr (fun i' => rise_sub _ _ _))
      (fun a=> u _ _ (sub_eq_zero.mp a)) (ε/2) (half_pos hε)] with s c
    filter_upwards [((matterSide_grows P s).comp B.tendsto_atTop).eventually c] with n c
    exact lt_of_le_of_lt (c (Vale.val_e ..) _) (half_lt_self hε)
  rw [ht]; unfold wakeZ costsWith
  by_cases k:i.2.2
  · simp only [k, ↓reduceIte]; by_cases q:j.2.2
    · simp only [q,if_true]; exact tendsto_const_nhds
    simp only [q,Bool.false_eq_true,↓reduceIte]; split_ifs
    exact he i.1 j.1
    exact tendsto_const_nhds
  simp only [k,Bool.false_eq_true,↓reduceIte]; by_cases q:j.2.2
  · simp only [q,↓reduceIte]; split_ifs
    exact (he j.1 i.1).neg
    exact tendsto_const_nhds
  simp only [q,Bool.false_eq_true,↓reduceIte]; exact tendsto_const_nhds

#print axioms reachingZ
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
