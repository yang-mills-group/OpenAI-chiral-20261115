import YM.SU5.Registration.Rise.AtFull
import SatinThinSymphony
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid

/-!
# From tilted clover to bought coalition, in OPERATOR entry

Uses `Pilgrim` type B allocations but must control at their going physical width
(not strictly late). From `reflectorSum` and common full operator identity. `Δ`
heat time here already covers both sides; grains still finite-width.
-/
open SatinNucleus
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "M"=>timeMesh P.par
local notation "N" s:max w:max=> whenly M s w
local notation "E" => (P.physicalEnergy j x).E
local notation "H" => P.ColorHil j x
variable {ι:Type} (A:ι→P.Apron)(z:ι→ℂ)(I:Finset ι)(B:P.Apron)

private lemma entersRoom (s:ℕ)(d:P.Apron)(p:d.s ≤ s) (w:ℕ): d.allowance P j ≤ N s w ↔ d.zoom P s j ≤ w:=by
 rw [← P.zoomMoney j d s p]; exact when_le ..
lemma buys_total (s:ℕ)(q:∀ i∈ I,(A i).s ≤ s)(h:B.s=s)(u:B.F=∑ i∈ I,z i • (A i).full P s)(g:∀ i∈ I,(A i).allowance P j ≤ B.allowance P j) : P.stageH j x B (B.allowance P j) (B.allowance P j) = ∑ i∈ I,z i • P.stageH j x (A i) (B.allowance P j) (B.allowance P j):=by
 let W:= B.allowance P j; let w:=B.u j; have he:W=N s w:=by unfold W Apron.allowance; rw [h]
 rw [show B.allowance P j=_ from he]; let t:= N s w
 let D(i:ι):=z i • P.shifts j w ((A i).full P s); let W'(i:ι): (H).Op:= z i • P.stageH j x (A i) t t
 have hp:0<w+w:= add_pos (B.pos _) (B.pos _)
 have hh(i:ι)(v:i∈ I): ∃ g:P.InCase j s (w+w) (D i), g.charges x hp=W' i:=by
    let Z:= A i; have hh: Z.zoom P s j≤w:= (P.entersRoom j s (A i) (q i v) w).1 ((g i v).trans he.le); let b:= Z.entrusted P j s (q i v) w w hh hh
    refine ⟨b.scale _,?_⟩; change (b.scale (z i)).charges x hp=z i • P.stageH j x Z t t; rw [b.charges_scale]; exact congrArg (z i • ·) (Z.entrusted_pays P j x s (q i v) w w hh hh hp)
 obtain ⟨L,hL⟩:= InCase.collect P j x s _ D W' I hp hh
 refine Eq.trans ?_ hL; apply Eq.symm; apply B.consumes P j x s h.le w w L _ _ hp
 · unfold D; rw [Apron.full,h,Nat.sub_self]; change _=P.shifts j w B.F; rw [u,map_sum]; exact sum_congr rfl fun i v=> (map_smul (P.shifts j (w:ℤ)) _ _).symm
 all_goals exact (P.entersRoom j s B h.le w).1 he.le

-- clear both sides first. For all later radius transfer on siteH.
lemma canvasing (s:ℕ)(q:∀ i∈ I,(A i).s ≤ s)(h:B.s=s)(u:B.F=∑ i∈ I,z i • (A i).full P s)(g:∀ i∈ I,(A i).allowance P j ≤ B.allowance P j) (t t':ℝ≥0)(hv:B.allowance P j≤ t)(hy:B.allowance P j≤ t') : P.stageH j x B t t'= ∑ i∈ I,z i • P.stageH j x (A i) t t':=by
 let w:= B.allowance P j; let L':= E (t-w); let R':= E (t'-w)
 rw [P.stage_more j x B (show w≤w from le_rfl) hv le_rfl hy, P.buys_total j x A z I B s q h u g, Finset.mul_sum,Finset.sum_mul]; refine sum_congr rfl fun i v=>?_ ; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; exact congrArg (z i • ·) ( (P.stage_more j x (A i) (g i v) hv (g i v) hy).symm)
lemma pivot_boxes (s:ℕ) (w:Axis→ℕ)(q:∀ i∈ I,(A i).s ≤ s)(p:∀ j,0<w j)(d:∀ i∈ I,∀ j,(A i).zoom P s j ≤ w j)(R:ι→ℝ) (l:List Axis)
    (t:ℝ≥0)(u : N s (w j) ≤ t) : P.stageH j x ((P.canvas A I w s p q d (fun i=>(R i:ℂ))).pivot P l) t t=∑ i∈ I,(R i:ℂ) • P.stageH j x ((A i).pivot P l) t t := by
 let B:= P.canvas A I w s p q d (fun i=>(R i:ℂ)); let A':= B.pivot P l
 have hx (X:P.Apron): (X.pivot P l).allowance P j=X.allowance P j:= NNReal.eq ( ( ( (X.pivot P l).width_real P j).symm.trans ((X.pivot_w -- binder
     j P l).trans (X.width_real P j))))
 have ht:A'.allowance P j=B.allowance P j:= hx B
 refine P.canvasing j x _ (fun i=>(R i:ℂ)) _ A' s (fun i v=>(Apron.pivot_s P (A i) l).le.trans (q i v)) (B.pivot_s P l) (P.reflectorSum A I w s p q d ..) (fun i v=> (hx (A i)).trans_le ?_) t t (ht.trans_le u) (ht.trans_le u)
 exact ((P.entersRoom j s (A i) (q i v) (w j)).2 (d i v j)).trans_eq ht.symm

-- apply in pleading. `admissible_wh` & `.zoom` private; use elimination helper to capture defeq their anonymous witnesses.
variable (v:ℕ→ℕ)(q:StrictMono v)(a:ℕ→ℝ)(L:Coalition)
variable (g h i:ℕ)
local notation "ξ" => P.advocate 3
lemma stage_pledges (x:P.Spectrum0 3) (l:List Axis)(t:ℝ≥0)(p:whenly (timeMesh P.par) (v i) P.roomy ≤ t):
    P.stageH j (P.advocate 3 x j) ((P.pleading x g h i L v a q).pivot P l) t t= ∑ j'∈ L.voters,(L.w j':ℂ) • ((P.rewardK g h:ℂ) • ((a (i+j'):ℂ) • P.stageH j (P.advocate 3 x j) ((P.basePlay x g (v (i+j'))).pivot P l) t t)):= by
 let s:= parliament i L v; let y(k:ℕ):=P.basePlay x g (v (i+k)); let D:=P.basePlay x g (v i); let R(j:ℕ):= L.w j * (P.rewardK g h*a (i+j)); let w:=D.zoom P s
 let T:= P.pleading x g h i L v a q
 have w' : N s (w j)=N (v i) P.roomy:= P.zoomMoney j D s (le_max_left ..)
 have hb(k:ℕ)(p:k∈ L.voters): (y k).s ≤ s:= le_trans (le_sup (f:=fun k=>v (i+k)) p) (le_max_right ..)
 -- prove zoom from steps; avoid elimination reducing definitions of `pleading` in theorem passed args except at last
 have ht(k:ℕ)(e:k∈L.voters)(a:Axis): (y k).zoom P s a≤ w a:=by
    -- p.time monotone. Can use zoom def arithmetic
    have he:v i≤ v (i+k):=q.monotone (by omega); apply Nat.mul_le_mul_right P.roomy (Nat.pow_le_pow_right P.par.R.L.property (by change s-v (i+k) ≤ s-v i; omega)) -- syntax tune
 refine (P.pivot_boxes j (P.advocate 3 x j) y L.voters s w hb (fun i=> D.zoomP P i s) ht R l t (w'.trans_le p)).trans ?_
 refine sum_congr rfl fun k h=>?_ ; unfold R; rw [Complex.ofReal_mul, Complex.ofReal_mul,mul_smul,mul_smul]; -- maybe h shadow
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.stage_pledges
