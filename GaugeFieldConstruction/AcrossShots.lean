import GaugeFieldConstruction.AcrossCost
import GaugeFieldConstruction.AcrossPrices
import YM.CF.Vp929.Fixed.Delivery

/-!
# Canonical real shot credentials with the prescribed common bare
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2600
set_option maxHeartbeats 450000
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

namespace AcrossShots
open LayerOverlap Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h x delay : ℝ} {D C R0 : ℝ → ℝ} {m m' N B : Side} {U : Grasp V.U B d}
variable {W : GivenX V U} {J : Robes N V W} {q : Chi} {z:ℝ} {P : Prescription R B} {N0 k k' l₀ : ℕ} {T : Month x 1 6 2 N0 V W}

open AcrossLands
variable {X:Cape m B R.L} (p: T.q ≤ m.val) (H:Service V U W J q h D C R0 P N0 delay)(hh:1≤h)
 {f:ℕ→ℝ} {k:ℕ}
local notation "Ω"=> mid (mesh m R.L k) B
local notation "Y"=> Actual T p X f k
variable (hp:K.top.clip.direct≤1) (a:Bon J q h D delay (Actual T p X f k))

/-- Preserve the same wavelength tests & all Price steps. `z` only approximately zero. The
palette of heights, meters, fiscal engine, matchTest argument and the settling of the regular
limits don't authorize a different terminal x behind these coordinates. -/
abbrev RealizedAt (p0: T.q ≤ m.val)(X:Cape m B R.L)(P:Prescription R B)(k:ℕ)(f:ℕ→ℝ)(b z:ℝ) (μ:Bet k) : Prop:=
    let M:= Actual T p0 X f k
    let Z:= M.gram P μ
    Solved P M z μ ∧
    (Z 0).beta=x+z ∧ (Z k).beta=b ∧ denZ (Z k) U (X k)=sharpHat (mesh m R.L k) U (T.a k) b ∧
    ∀ s:ℕ, s≤k→ entersReal (hat R.L x s) (Z s).beta ∧
        Envelope (denZ (Z s) U (X s)) ∧ partitionZ (Z s) U (X s) = sharpWeight (mesh m R.L k) U (T.a k) b ∧
        partitionZ (Z s) U (X s)≠0 ∧ (s<k→ M.active P μ s=Z s ∧ Canonical (f s) (Z s) K.j)

structure CanonicalAt (p0: T.q ≤ m.val)(X:Cape m B R.L)(P:Prescription R B)(k:ℕ)(f:ℕ→ℝ)(b z:ℝ) : Prop where
  solved : ∃ μ:Bet k, RealizedAt p0 X P k f b z μ
include a hp H hh
lemma tipBalance {b':Bet k} {u : ℝ} (e : Solved P (Actual T p X f k) z b') (pU:(b'.read k).re=u) :
  sharpWeight (mesh m R.L k) U (T.a k) u ≠0 → RealizedAt p X P k f u z b' := by
 let B':= (Y); intro hv
 have he(i):=a.beta_ok H e.toRealQ i
 have hT: denZ (B'.gram P b' k) U (X k) = sharpHat (mesh m R.L k) U (T.a k) u := by
   change denZ ((Y).gram P b' k) U _=_; unfold Actual; rw [unchanged_boot]; let e:= a.can.cape k
   rw [←pU]
   exact funext (core_b (D:=U) (β:=(b'.read k).re) (q:=T.a k) V.L _ _ { e.paid with paid:=fun y=>(e.paid.paid y).shrink J.hr.le } (a.can.pole k) hp (J.gran.trans e.size))
 have hz : partitionZ (B'.gram P b' k) U (X k) = sharpWeight (mesh m R.L k) U (T.a k) u:=by unfold partitionZ; rw [hT]
 have h0 (i:ℕ)(hi:i≤k):partitionZ (B'.gram P b' i) U (X i) = sharpWeight (mesh m R.L k) U (T.a k) u:=by
    induction hi using Nat.decreasingInduction with
    | self=> exact hz
    | of_succ i hi ih=> exact (a.partition H e i hi).trans ih
 refine ⟨e,?_,pU,hT,fun s h=>?_⟩
 · change (b'.read 0).re=_; simp [Bon.anchor e]
 have hr:=a.can.cape s; let T':=hr.paid; let Ht:Roof _ J.k d J.n (X s):={T' with paid:=fun i=>(T'.paid i).shrink J.hr.le}
 have v: Envelope (denZ (B'.gram P b' s) U (X s)):= denInt W Ht (k-s) (J.gran.trans hr.size) _ _ ((a.charged H e.toRealQ _ h).toCost.lot ((Y).gram P b' s).beta _)
 refine ⟨(he s h).1,v,h0 s h,(h0 s h).trans_ne hv,fun w=>?_⟩
 have hv:=a.success H e.toRealQ s w (a.paysStep H e s w); exact ⟨hv,hv ▸ (a.active_law H e.toRealQ s w).2.1⟩


lemma tipped {b':Bet k} {u : ℝ} (e : Solved P (Actual T p X f k) z b') (pU:(b'.read k).re=u) :
  sharpWeight (mesh m R.L k) U (T.a k) u ≠0 → CanonicalAt p X P k f u z:=fun w=> ⟨b',tipBalance p H hh hp a e pU w⟩

-- `true terminal` is x itself on the old license. Give deterministic Spin timing relation &
-- all-height professional estimates on any of these slightly shifted licenses. No assertion on
-- normalized prices from new couplings just from this proximity on every intermediate scale.
local notation "nX" s:max=> cell m B R.L s
local notation "𝕩" s:max=> hat R.L x s
local notation "Ππ"=> (ActualSpine T p X f k)
structure CreditedBet {P:Prescription R B}(b z:ℝ)(r:Bet k) :Prop where
  core: Branch.Solved P (Actual T p X f k) z r
  terminal : (((Y).gram P r) 0).beta=x+z ∧ ((Y).gram P r k).beta=b ∧ (Y).gram P r k=Vale.launch V.L b (T.a k) _
  paid (s:ℕ) (h':s ≤ k) :
      Laurel ((Y).gram P r s) K.j h (dleaf R.L (𝕩 s)) (dleaf R.L (𝕩 s)) R.L.val ∧
      matchedX (𝕩 s) ((Y).gram P r s).beta ∧
      (s<k → Location.Request V U W J q ((Ππ).address s) N0 (𝕩 s) (T.a s) (T.a (s+1)) ∧
        (Y).active P r s=(Y).gram P r s ∧
        (Y).gram P r (s+1)= ((Ππ).address s).buildIn V (T.a (s+1)) (r.read (s+1)).re ((Y).chargeLevel P r (s+1)) ((Y).offset P r (s+1))∧
        Frequency R.L (cell m B R.L s) (f s) ∧ Canonical (f s) ((Y).gram P r s) K.j ∧
        (∀ v: Orbit (cell m B R.L s), Rue.FleetS (T.a s).threshold v.1 → stove U (X s) ((Y).gram P r (s+1)) (X (s+1)) (apt m B R.L s) (V.L.op (k-1-s) (kint m B R.L s)) q J.d ((Y).wave P r s).val v= denZ ((Y).gram P r s) U (X s) v) ∧
        ‖(Y).wave P r s‖ ≤ R0 (𝕩 s) ∧
        |(((Y).gram P r s).v).re-(((Y).gram P r (s+1)).v).re| ≤ C (𝕩 s)*sites (cell m B R.L s)∧
        ((Y).gram P r (s+1)).beta-(Ππ).pilot x (s+1)-(((Y).gram P r s).beta-(Ππ).pilot x s)= ((Y).fee P s r).re∧
        ‖(Y).fee P s r‖ ≤ D (𝕩 s)
      )

-- proof mimics Parcel.send over these shapes for a value of z≠0.
lemma cashSet (b:ℝ)(r:Bet k) (s: Solved P (Actual T p X f k) z r) (u:((Y).gram P r k).beta=b) : CreditedBet (J:=J) (f:=f) (X:=X) (q:=q) (h:=h) (R0:=R0) (C:=C) (D:=D) (P:=P) p b z r:=by
 let E:=(Y); let Z:= E.gram P r; let g:=(Ππ).pilot x; let t:=s.toRealQ
 refine ⟨s,⟨?_,u,?_⟩,fun i hi=>?_⟩
 · change (r.read 0).re=_; rw[Bon.anchor s]; simp
 · rw [show b=(r.read k).re from u.symm]; exact unchanged_boot ..
 have hb:= (a.charged H t i hi).mono (show _ ≤ dleaf R.L (hat R.L x i) from (by linarith [(a.clocks i).leaf])); refine ⟨hb.laurel ..,matched_of_enters (a.clocks i) (a.beta_ok H t _ hi).2,fun hx=>?_⟩
 have he:= a.success H t i hx (a.paysStep H s i hx); have hv:= a.active_law H t i hx; refine ⟨a.request _ hx,he,(Y).gram_fine P r i hx,a.can.frequencies _,he ▸ hv.2.1,fun v u=>(he ▸ hv.2.2.1 v u).symm, hv.1,hv.2.2.2,?_,(a.posts H).bound _ hx _ (a.area H t _)⟩
 -- triggered binder ℝ inferred here.
 let μ:=((Y).fee P i r).re; have p:=a.paysStep H s i hx; change (Z (i+1)).beta+E.last.move i-(E.op P i).posted _ _ = _ at p; have hp:μ=(E.op P i).posted (r.read (i+1)).re (E.chargeLevel P r (i+1)):= by have he:= congrArg Complex.re (a.fee_eq H t i hx).symm; rwa [Complex.ofReal_re] at he
 change (Z (i+1)).beta-g (i+1)-((Z i).beta-g i)=μ; linarith only [hp,p, E.toSpine.pilot_move (x:=x) i]

lemma dueCredited {b z:ℝ}(e:CanonicalAt p X P k f b z) : ∃ r:Bet k, CreditedBet p (P:=P) (k:=k) (X:=X) (J:=J) (q:=q) (h:=h) (R0:=R0) (C:=C) (D:=D) (f:=f) b z r:=by obtain ⟨r,h,q,pQ,i,t⟩:= e.solved; exact ⟨r,cashSet p H hh hp a b r h pQ⟩
#print axioms dueCredited
lemma moves_top {b':Bet k}{β ε:ℝ}(g:Solved P (Actual T p X f k) 0 b') (e:0<ε)(u:ε<Rx x) (hx:|β-(b'.read k).re| ≤ ε/2)
    (v:sharpWeight (mesh m R.L k) U (T.a k) β ≠0) : ∃ τ:ℝ, |τ| ≤ ε ∧ CanonicalAt p X P k f β τ := by
 obtain ⟨Z,t,Ht⟩:= (a.posts H).solve
 have h:0 < strip (hat R.L x 0)/8:=by rw [hat_zero]; exact Rx_pos (a.prices _ le_rfl).grade
 have hg(τ:ℝ)(s:|τ|<strip (hat R.L x 0)/8): (τ:ℂ)∈ball (0:ℂ) (strip (hat R.L x 0)/8):= by rw [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs]; exact s
 have h0:b'= Z (↑(0:ℝ)):= (Ht _ (hg 0 (by rw [abs_zero]; exact h))).2.2.2.1 _ g.paid g.fixp
 rw [h0,Bet.read_of_le _ le_rfl] at hx
 obtain ⟨τ,q,z⟩:= feasible_payment (a.posts H) (g:=Z) (fun i p=>(Ht i p).2.1) (fun i p=> (Ht i p).2.2.1) t.continuousOn ε e (hat_zero.symm ▸ u) β hx
 refine ⟨τ,q,tipped p H hh hp a (b':=Z τ) ?_ ?_ v⟩
 · obtain ⟨_,q,h,t,z⟩:= Ht (τ:ℂ) (hg τ <| lt_of_le_of_lt q <| hat_zero.symm ▸ u); exact ⟨⟨q,z rfl⟩,h⟩
 rw [Bet.read_of_le _ le_rfl]; exact z

#print axioms moves_top
end AcrossShots
end YM.CF.Py.Rate
end
