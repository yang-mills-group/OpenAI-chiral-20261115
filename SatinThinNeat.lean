import SatinThinBeaconPath
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/
variable {z A c:ℝ}




open Regis Head.Garland Head.Etch Lamour.Bridge Celeste Clock Hookah Hookah.Blaze

open Papal -- needed addgap namespace
set_option linter.unusedVariables false
-- probes fare template incumbent
variable (z:PlaqAxes→ℝ) {I:Type}[Fintype I]
local notation "xθ" s:max=>hat P.R.L P.x s
local notation "ρ" s:max=>Real.sqrt (hat P.R.L P.x s)
local notation "ℰ" s:max=> meterC (xθ s)
variable {A B b:ℝ} (E':Trip I)(K H:ℕ→ℕ) (P_ :Real.exp 1≤ P.x)
variable (a:ℝ)
variable {K H} {T:ℕ→Buffered.Family (tent Y P_)→ℕ→ℂ}{E:ℕ→ Buffered.Family (tent Y P_) →ℂ}(V:Universal Y P_ K H T E)
open Regis Circuit Head.Brecht
open YM.Stationary (Gaia)
variable {R:ℕ→ℝ}{x y:ℕ→ Cover}{w:Gaia}(p:∀ i,0<R i)(zR:Tendsto R atTop atTop)(hv:Tendsto (fun i:ℕ=>Onyx.riseX (R i) (x i-y i)) atTop (𝓝 w))(hw:w≠0) (k:Tendsto (fun i:ℕ=> R i^8/trailℓ A (hat P.R.L P.x i)) atTop (𝓝 0))
open Signal.Interval (separationCost)
open BProof
lemma rangeFrame(x y:Cover)(h:x∈ Hookah.Blaze.stencilFrame y)(v:Axis): (x v).natAbs ≤ (y v).natAbs+ breadth 0 noonFrame:=by
 obtain ⟨t,u,rfl⟩:= mem_image.mp h; have hx: (t v).natAbs ≤ separationCost 0 t:=by
    have hf:= Finset.le_sup (s:=univ) (f:=fun i=>(((0:Cover)-t) i).natAbs) (mem_univ v); change _ ≤ separationCost _ _ at hf -- tune
    simpa using hf
 have he: separationCost 0 t≤ breadth 0 noonFrame:= Finset.le_sup (f:=fun i=>separationCost 0 i) u
 change (t v+y v).natAbs ≤ _; rw [add_comm (t v)]; exact (Int.natAbs_add_le ..).trans (Nat.add_le_add_left (hx.trans he) _) -- tune
lemma helmSe {v:ℝ} (x:ℝ) : |(↑(Nat.ceil (trailℓ v x)):ℝ) - trailℓ v x| ≤1:=by
 rw [abs_of_nonneg (sub_nonneg.mpr (Nat.le_ceil _))]; linarith only [Nat.ceil_lt_add_one (trainℓ v x).le]
lemma helmBound (v:ℝ)(t:0<v) : Worth.Pays 0 v 0 (fun x=> (Nat.ceil (trailℓ v x):ℝ)):=by
 apply Pays.by_floor (C:=2); filter_upwards [(summit0 v t)] with x p
 rw [abs_of_nonneg (by positivity)]; have he:= Nat.ceil_lt_add_one (trainℓ v x).le; change _ ≤ 2*trailℓ v x; linarith
where summit0 (v:ℝ)(h:0<v): ∀ᶠ x:ℝ in atTop,1≤ trailℓ v x :=by filter_upwards [coin_budget (a:=0) (b:=0) (c:=0) (d:=0) (e:=v) (f:=0) (by right; left; exact ⟨rfl,h⟩) 1 1 (by norm_num)] with x hx; rw [coin_zero,one_mul,one_mul] at hx; exact hx.le
lemma pathEquipment (J:ℝ)(hv:0<J)(u: ∀ᶠ s in atTop,∀ i :Axis, (((x s) i).natAbs:ℝ) ≤ trailℓ J (hat P.R.L P.x s) ∧ (((y s) i).natAbs:ℝ) ≤ trailℓ J (hat P.R.L P.x s)):equip_width P x y:=by
 let W:=breadth 0 noonFrame; let X(x:ℝ):=Nat.ceil (trailℓ J x); let S(v:ℝ):= (X v+W)*2; have hZ: Worth.Pays 0 J 0 (fun x=> (S x:ℝ)) :=by unfold S; push_cast; exact Pays.right 2 (Pays.plus (helmBound J hv) (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,hv⟩))))
 refine ⟨fun i:ℕ=>S (xθ i), ?_, ?_⟩
 · refine ⟨J+1,by positivity,?_⟩; exact (turnover P).eventually (leap (p:=J+1) (w:=0) (q:=0) hZ (by right; left; constructor; rfl; linarith))
 filter_upwards [u] with s hp; let x':=x s; let y':=y s; let C:Trip Bool:= twinTrip x' y'; let c:=C.canvasC
 refine ⟨c, ⟨x s,C.touchedC true (loc_frame _)⟩, Nat.mul_le_mul_right 2 ?_,subset_refl _⟩
 unfold Celeste.breadth; apply Finset.sup_le; intro i b; obtain ⟨j,k,F⟩:=mem_biUnion.mp b; change i ∈stencilFrame (C.loc j) at F
 have he(v:Axis):((C.loc j) v).natAbs ≤ X (xθ s):=Nat.cast_le (α:=ℝ).mp (((show (((C.loc j) v).natAbs:ℝ) ≤ _ from (by cases j; exact (hp v).2; exact (hp v).1))).trans (Nat.le_ceil _))
 change separationCost 0 _ ≤ _; unfold separationCost; apply Finset.sup_le; intro z _; have h:= (rangeFrame i (C.loc j) F z).trans (Nat.add_le_add_right (he z) W); change ((0-i) z).natAbs ≤_; simpa using h
lemma summitT (v:ℝ)(t:0<v) : Tendsto (trailℓ v) atTop atTop:=by
 apply Filter.tendsto_atTop.mpr; intro p; filter_upwards [coin_budget (Or.inr (Or.inl (show (0:ℝ)=0∧(0:ℝ)<v from ⟨rfl,t⟩))) p 1 zero_lt_one (c:=0) (f:=0)] with x h; simpa only [one_mul,coin_zero,mul_one] using h.le
lemma prismPath (v:ℝ)(t:0<v): Tendsto (fun x:ℝ=>(Nat.ceil (trailℓ v x):ℝ)) atTop atTop := tendsto_atTop_mono (fun x=> Nat.le_ceil (trailℓ v x)) (summitT v t) -- tune exact
abbrev scout (P:Preparation)(v:ℝ)(i:ℕ):= Nat.ceil (trailℓ v (hat P.R.L P.x i))
noncomputable abbrev CheckPoint(P:Preparation) (v:ℝ)(i:ℕ):Cover:= scout P v i • (Lattice.step 3)
lemma scouts_height(P:Preparation)(v:ℝ)(t:0<v) : Tendsto (fun i:ℕ=> (scout P v i:ℝ)) atTop atTop:= (prismPath v t).comp (turnover P)
lemma monthsPast(P:Preparation)(v:ℝ)(t:0<v): equip_width P (CheckPoint P v) 0:=by
 refine pathEquipment (v+1) (by linarith only [t]) ?_; filter_upwards [(turnover P).eventually (leap (w:=0) (p:=v+1) (q:=0) (helmBound v t) (by right; left; constructor; rfl; linarith))] with s u i; constructor
 · by_cases f:i=(3:Axis)<;> simp [CheckPoint,f]
   exact u -- order simp?
   exact (trainℓ _ _).le
 simpa only [Pi.zero_apply,Int.natAbs_zero,Nat.cast_zero] using (trainℓ (v+1) (hat P.R.L P.x s)).le
lemma heightMerit (P:Preparation)(v:ℝ)(i:ℕ): 0< (scout P v i:ℝ):= Nat.cast_pos.mpr (Nat.ceil_pos.mpr (coin_pos ..))
lemma paintedJourney (P:Preparation)(v:ℝ)(i:ℕ): Onyx.riseX (scout P v i) (CheckPoint P v i)= YM.basis 3:=by
 ext j; change (( (scout P v i • (Lattice.step 3:Cover)) j:ℤ):ℝ)/(scout P v i:ℝ)= YM.basis 3 j
 by_cases h:j=(3:Axis)<;> simp [h,basis_eq]
lemma landed (P:Preparation)(v:ℝ)(h:0<v){X:ℝ}(u:8*v<X): Tendsto (fun i:ℕ=>(scout P v i:ℝ)^8*trailℓ (-X) (hat P.R.L P.x i)) atTop (𝓝 0):= (Pays.limit (Pays.times (Pays.pot (helmBound v h) 8) (Pays.whole 0 (-X) 0)) (by right; left; constructor; norm_num; push_cast; linarith only [u])).comp (turnover P)
lemma routeCharge (P:Preparation)(v:ℝ)(h:0<v){X:ℝ}(u:8*v<X): Tendsto (fun i:ℕ=>(scout P v i:ℝ)^8/trailℓ X (hat P.R.L P.x i)) atTop (𝓝 0):=by
 refine (landed P v h u).congr fun i=> ?_; unfold trailℓ; rw [div_eq_mul_inv,coin_inv]; ring_nf
variable {w:ℝ}(Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → ShelterCost b Y s i k)
include V Z
lemma capable (v:ℝ)(h:0<v)(A:ℝ)(c:8*v<w)(p:8+w<A):∀ᶠ s in atTop, canonWeight/32 ≤ (scout P v s:ℝ)^8 * (budgetQ P (tent Y P_) E s witnessZ (CheckPoint P v s) 0).re:=by
 let d(s:ℕ):ℝ:= scout P v s; have he:8*v < A:=by linarith
 have hU:Tendsto (fun i:ℕ=> Onyx.riseX (d i) (CheckPoint P v i - (0:ℕ→ Cover) i)) atTop (𝓝 (YM.basis 3)):=by simp_rw [Pi.zero_apply,sub_zero, d, paintedJourney]; exact tendsto_const_nhds
 have hi:=focus_positive; filter_upwards [nearEnd Y witnessZ P_ V (heightMerit P v) (scouts_height P v h) hU (by intro p; simpa using congrArg norm p) (routeCharge P v h he) (by linarith only [c,h] : 0<w) p (monthsPast P v h) (landed P v h c) Z (canonWeight/32) (by positivity)] with s t; -- orientation order check
 let S:= Aster Y K H s; let C:=d s; let T':= budgetQ P (tent Y P_) E s witnessZ (CheckPoint P v s) 0; change ‖(C:ℂ)^8*T'-(S:ℂ)^4*spectrumℓ witnessZ SU.group (YM.basis 3)‖≤ _ at t; rw [focusEst] at t; have ht : -(canonWeight/32) ≤ ((((C:ℂ)^8*T'-(S:ℂ)^4*(canonWeight:ℂ)):ℂ)).re:= (abs_le.mp ((Complex.abs_re_le_norm _).trans t)).1; simp only [← Complex.ofReal_pow,←Complex.ofReal_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im, zero_mul,sub_zero] at ht; have hg:=pow_le_pow_left₀ (show 0≤(1/2:ℝ) by norm_num) (show (1/2:ℝ) ≤ S from (astral Y K H s).1.1) 4; change _≤ C^8*T'.re; linarith only [mul_le_mul_of_nonneg_right hg hi.le,ht]
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.capable
