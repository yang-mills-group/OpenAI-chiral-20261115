import YM.SU5.CompassRose.Load

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open CF.Fir CF.Jill CF.Flare CF.Kea CF.Emu CF.Dial Lamour Lamour.Bridge Cache Glaze Next.Free Laurent CF.Pannier.Chancel.Rous Pressure
open Ballad.Twah (Stamp)

section Wick_spin
-- extension of the dietary convergence in Hiro/Morsel and Twah SPF;
-- use the ground extension and preserve also the EXACT touch (within one staff site paired legs).
private lemma inner_leaf {U V:ℕ→ Cover} {Q:ℕ→Side} {R:ℕ→ℕ} (M:ℕ→Jill.Male) (j:ℕ) (p:1≤j)
    (k:Yard Q (fun i=>(R i:ℝ))) (X:Gaia) (v:X≠0 ∨ X=0 ∧ U =ᶠ[atTop] V)
    (Z:Tendsto (fun i=> riseX (R i) (U i - V i)) atTop (𝓝 X))
    (L D:DirSpin) : Tendsto (fun i=> dietary (R i) (U i) (V i) L D (Q i) j (M i)) atTop (𝓝 (shotL X L D)):=by
 simp_rw [dietary,in_transcript]; let i:=sourceSlot; obtain ⟨c,hv,hT⟩:=lake_formal p
 have ht:=Emu.tally (L:=fun i=> (R i:ℝ)) (fun i=>too _) M (fun i=> lakeP _ j (M i)) (fun i=>0) k hv (by norm_num : (0:ℝ)<1) (fun x:SU.Slot=> Eventually.of_forall (fun i=>hT _ (k.even i) _ x)) (alignedα L i) (alignedβ D i) U V X v Z p (fun _=>1)
 rw [show frank (alignedα L i) (alignedβ D i) X=shotL X L D from if_pos rfl] at ht; exact ht
variable (P : Spine) (v : ℕ→ℕ) (T : StrictMono v)
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
local notation "Y" => P.run
local notation "ζ" s:max A:max => zoomR P.par A s
variable (L G:DirSpin) {U V:ℕ→ Cover}{X:Gaia}{r:ℕ→ℕ} (p:Tendsto r atTop atTop) (f:∀ i,0<r i) (e:X≠0 ∨ X=0∧U=ᶠ[atTop]V)
include T p f e
lemma dietMoves (u:Tendsto (fun i=>riseX (r i) (U i-V i)) atTop (𝓝 X)) :
    Tendsto (fun z : ℕ×ℕ => dietary (r z.1) (U z.1) (V z.1) L G (O z) P.par.K.j (pupil P z.1 (v z.2)).J.M) bobbin (𝓝 (shotL X L G)) := by
  refine Metric.tendsto_nhds.mpr fun a x=> bobbin_for.mpr ?_
  by_contra h
  obtain ⟨g,hg,ht⟩:= extraction_of_frequently_atTop (not_eventually.mp h)
  let W(z:ℕ×ℕ):=dietary (r z.1) (U z.1) (V z.1) L G (O z) P.par.K.j (pupil P z.1 (v z.2)).J.M
  let t:=shotL X L G; let R' (i:ℕ) : ℝ:= r (g i); have hz (i:ℕ):0<R' i:= Nat.cast_pos.mpr (f _)
  choose N hn he using fun i:ℕ=> (show ∃ q:ℕ, ¬dist (W (g i,q)) t < a ∧ R' i * Ember.pinch (O (g i,q)) ≤ (2:ℝ)⁻¹^i from by
    obtain ⟨k,w⟩:= Glaze.pick_depth (p:=(show 0< (2:ℝ)⁻¹^i/R' i from (by have z:= hz i; positivity)))
    obtain ⟨N,v,f⟩:= ((not_eventually.mp (ht i)).and_eventually ((thicken P T (g i)).eventually_ge_atTop (⟨k+1,by omega⟩:Side))).exists
    exact ⟨N,v,(mul_comm _ _).le.trans ((le_div_iff₀ (hz i)).1 (w (Nat.le_trans (by omega : k≤k+1) (show k+1 ≤ (O (g i,N)).val from f))))⟩)
  let Z(i:ℕ):= O (g i,N i)
  have K : Yard Z R' := ⟨hz,tendsto_natCast_atTop_atTop.comp (p.comp hg.tendsto_atTop),squeeze_zero (fun i=> mul_nonneg (hz i).le (Ember.pinch_pos _).le) he (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),fun i=>Vale.val_e ..⟩
  have hw:=inner_leaf (U:=U∘g) (V:=V∘g) (Q:=Z) (R:=r∘g) (fun i:ℕ=> (pupil P (g i) (v (N i))).J.M) P.par.K.j (by rw [P.par.kJ]; decide) K X (e.imp_right (fun t=>⟨t.1,(t.2.comp_tendsto hg.tendsto_atTop)⟩)) (u.comp hg.tendsto_atTop) L G
  obtain ⟨i,x⟩:= (Metric.tendsto_nhds.mp hw a x).exists; exact hn i x
omit p f e T
abbrev sIndex (I:Type*) := I × SU.Slot × Bool
abbrev enter {I:Type*}(V:I→ℕ→Staff) (A:ℝ) (z:ℕ×ℕ) (i:sIndex I) := (Hiro.unifyT (V i.1 z.1).u (V i.1 z.1).spin).chargeF (R:=ζ z.1 A) (N:=O z) i.2.1 i.2.2

def arms (A B : ℂ) (i j : SU.Slot × Bool) : ℂ := if i.2=j.2 ∨ i.1≠j.1 then 0 else if i.2 then A else -B
variable {I : Type*}
abbrev spinRow (C:I→Gaia) (L:I→DirSpin) (i j:sIndex I) :ℂ := arms
     (shotL (C i.1-C j.1) (L i.1) (L j.1)) (shotL (C j.1-C i.1) (L j.1) (L i.1)) i.2 j.2
abbrev meshRow (V:I→ℕ→Staff) (A:ℝ) (z:ℕ×ℕ) (i j:sIndex I) :ℂ := rankG (lake (O z) P.par.K.j (pupil P z.1 (v z.2)).J.M) (enter P v V A z i) (enter P v V A z j)

lemma arm_price (L0 :ℕ) (o a : Cover) (k n₀:SU.Slot) (i j:Bool) (M:Jill.Male) (m:Side) (b:ℕ) (w:Even m.val) :
    rankG (lake m b M) ((unifyT o L).chargeF (N:=m) (R:=L0) k i) ((unifyT a G).chargeF (N:=m) (R:=L0) n₀ j) =
      arms (dietary L0 o a L G m b M) (dietary L0 a o G L m b M) (k,i) (n₀,j) := by
  by_cases p:k=n₀
  · cases i<;> cases j
    · exact Hiro.still ..
    · rw [show rankG _ _ _= _ from (flipcost (M:=M) (N:=m) (j:=b) L0 o a L G k n₀), rank_hint L0 _ _ _ _ w]; simp [arms,p]
    · rw [show rankG _ _ _= _ from (rank_hint (M:=M) (j:=b) L0 o a L G w k n₀)]; simp [p,arms]
    exact Hiro.calm ..
  cases i<;> cases j
  · exact Hiro.still ..
  · rw [show rankG _ _ _= _ from (flipcost (M:=M) (N:=m) (j:=b) L0 o a L G k n₀),rank_hint (M:=M) L0 a o G L w n₀ k]; simp [arms,p,Ne.symm p]
  · rw [show rankG _ _ _= _ from (rank_hint (M:=M) (j:=b) L0 o a L G w k n₀)]; simp [arms,p]
  exact Hiro.calm ..

variable (C:I→Gaia) (L':I→DirSpin) (X : I→ℕ→Staff) {A : ℝ}
  (z : ∀ i, Appoint P.par A (fun s=>(X i s).u) (C i)) (w:∀ i s,(X i s).spin=L' i)
include z w T
lemma pole_value (t : ∀ i j,C i=C j→ (fun s=> (X i s).u)=ᶠ[atTop](fun s=>(X j s).u))
    (h : 0<A) (i j:sIndex I): Tendsto (fun v'=>meshRow P v X A v' i j) bobbin (𝓝 (spinRow C L' i j)):=by
  have hx (i j): Tendsto (fun k : ℕ×ℕ=> dietary (ζ k.1 A) (X i k.1).u (X j k.1).u (X i k.1).spin (X j k.1).spin (O k) P.par.K.j (pupil P k.1 (v k.2)).J.M) bobbin (𝓝 (shotL (C i-C j) (L' i) (L' j))):=by
    simp_rw [w]; refine dietMoves (U:=fun s=> (X i s).u) (V:=fun s=> (X j s).u) (r:=zoomR P.par A) (X:=C i-C j) P v T (L' i) (L' j) (zoom_grows P.par h) (zoom_pos (A:=A) P) ?_ ?_
    · by_cases v:C i=C j; · exact Or.inr ⟨sub_eq_zero.mpr v,t i j v⟩
      exact Or.inl (sub_ne_zero.mpr v)
    simp_rw [rise_step]; exact ((appoint_as P.par h _ _).mp (z i)).sub ((appoint_as P.par h _ _).mp (z j))
  let V(i j : I) (z:ℕ×ℕ):= dietary (ζ z.1 A) (X i z.1).u (X j z.1).u (X i z.1).spin (X j z.1).spin (O z) P.par.K.j (pupil P z.1 (v z.2)).J.M
  have hp(y:ℕ×ℕ) : meshRow P v X A y i j = arms (V i.1 j.1 y) (V j.1 i.1 y) i.2 j.2:= arm_price _ _ _ _ _ _ _ _ _ _ _ _ (Vale.val_e ..)
  simp_rw [hp]
  change Tendsto _ _ (𝓝 (arms _ _ i.2 j.2))
  unfold arms; split_ifs
  all_goals first| exact tendsto_const_nhds| exact hx i.1 j.1 | exact (hx j.1 i.1).neg

omit z w T in
lemma spin_leap {U:Type*}(p:Filter U) (K:I→I→ℂ) (V:U→I→I→ℂ) (h:∀ i j,Tendsto (fun f=> V f i j) p (𝓝 (K i j))) (L:List I) : Tendsto (fun f=>runes (V f) L) p (𝓝 (runes K L)):=by -- adapted from offer_v
 have he(W: List (I × I)):Tendsto (fun i=> (W.map fun v=> V i v.1 v.2).prod) p (𝓝 ((W.map fun v=> K v.1 v.2).prod)):=by
   induction W with| nil=> exact tendsto_const_nhds| cons i t ih=> exact (h i.1 i.2).mul ih
 have hp(W:Cl I) : Tendsto (fun i=>spinC (V i) W) p (𝓝 (spinC K W)):=by
   unfold Emu.spinC; split_ifs; exact (he _).const_mul _; exact tendsto_const_nhds
 unfold runes; generalize claps L=W; induction W with| nil=>exact tendsto_const_nhds| cons a l ih=> exact (hp a).add ih

-- implement at the actual torus spun. call fully contracted op table.
omit z w T in
lemma season_f (s:ℕ×ℕ) (u : Kea.Pad P.par.K.j (O s)) (G:List (sIndex I)) :
  (ζbank P v s) (rollC (ton ∘ (enter P v X A s)) G)=runes (meshRow P v X A s) G:=by
 let Z(q:I) := Hiro.unifyT (X q s.1).u (X q s.1).spin; let z:I→ Lead.Clan:= fun _=> (0,false); let M:= (pupil P s.1 (v s.2)).J.M; let v0:= flatSea Y s.1 (pᵥ s) (cᵥ s)
 have hv:= Twah.bank_chant (R:=(ζ s.1 A)) Z z [] (by rw [P.par.kJ]; decide : 1≤ P.par.K.j) u M v0 (preparedFlat Y s.1 (pᵥ s) (cᵥ s)) G; rw [show plait _ _ [] _ _ _=1 from rfl, mul_one] at hv; exact hv
-- #print axioms pole_value
-- #print axioms season_f
end Wick_spin
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
