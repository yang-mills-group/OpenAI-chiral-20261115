import Velour.Crepe.Caring
import Velour.Tassel.Put
set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
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



open MacroGrid SatinNucleus Velour

variable (P:Spine) 
local notation "τ"=> P.macroStep

lemma halvesClock(k:ℕ): τ (k+1)≤ τ k/2:=by
 have u:P.par.R.L.val≥2:=by have he:=P.par.V.tallX; omega
 rw [←P.daysF (k+1) k (Nat.le_succ k)]
 rw [add_tsub_cancel_left,pow_one]
 have h: (2:ℝ)≤P.par.R.L.val:=by exact_mod_cast u
 nlinarith only [h,P.macroStep_pos (k+1)]

variable {P}{j:Axis}{x:P.Spectrum0 j}{T:ℕ→P.Apron}
local notation "𝒞"=> P.ColorHil j x
local notation "σ"=> P.physicalEnergy j x

lemma Veloured.wvary (h:P.Veloured j x T){L R:ℕ→ℝ}{a:ℝ}
    (p:0<a)(u:Tendsto L atTop (𝓝 a))(v:Tendsto R atTop (𝓝 a)):
    Gleams 𝒞 (fun i=> (T i).dye P j x (L i) (R i)) (h.printOp a):=by
 let r:=a/2
 have t:0<r:=half_pos p; have d:r<a:= half_lt_self p
 rw [h.print_wrap t d.le]
 refine ((h.printed t).pad (σ) (u.sub_const r) (v.sub_const r)).agree ?_
 filter_upwards [h.thin.eventually (gt_mem_nhds t), u.eventually (lt_mem_nhds d),v.eventually (lt_mem_nhds d)] with i z y w


 change (T i).realWidth P j<r at z
 change r<L i at y; change r<R i at w
 exact (T i).dye_twice P j x z.le z.le y.le w.le
lemma Veloured.rich(h:P.Veloured j x T):
 ∃ C D:ℝ, 1≤C ∧ 1≤D ∧ ∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ in atTop,
   ∀a:ℝ,τ k/2≤a → ∀b:ℝ,τ k/2≤b → ‖(T i).dye P j x a b‖ ≤ C*D^k:=by
 obtain ⟨B,D,u,v,hc⟩:=h.bill
 refine ⟨B*D,D,one_le_mul_of_one_le_of_one_le u v,v,?_⟩
 have mon: Tendsto (fun k:ℕ=>k+1) atTop atTop:=tendsto_add_atTop_nat 1
 filter_upwards [mon.eventually hc] with k cost
 let r:=τ (k+1)
 have p:r≤τ k /2:=P.halvesClock k
 filter_upwards [cost,h.thin.eventually (ge_mem_nhds (P.macroStep_pos (k+1)))] with i c e a v b w
 exact ((T i).dye_le P j x e e (p.trans v) (p.trans w)).trans
   (le_trans c (le_of_eq (by ring)))

end Spine
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus Velour
variable (P:Spine) (Z:Lead.Clan)
local notation "π₀"=> (purePrice Z:ℂ)
variable (x:P.Spectrum0 3)(A:ℕ→P.Apron) {c r n:ℕ→ℕ}
local notation "ξ"=> P.advocate 3 x 3
local notation "𝒞"=> P.ColorHil 3 ξ
local notation "τ"=> P.macroStep
variable (m:P.HandleWith x c r A n) (h:P.VelvetHandle c r A x n)
  (v:P.Veloured 3 (P.advocate 3 x 3) A)
local notation "Q₀" i:max=> (P.stitchApron Z (A i) (c (n i)) (r (n i)))
local notation "w" i:max=> (A i).realWidth P 3
local notation "W" i:max=> (Q₀ i).realWidth P 3
local notation "V!" i:max s:max=> (Q₀ i).velour P 3 ξ s
local notation "Y!" i:max a:max b:max=> (A i).dye P 3 ξ a b

include m h
lemma weight_silver (i:ℕ) {t:ℝ}(e:W i≤ t):
 ‖V! i t - π₀ • Y! i (t+w i) (t-w i)‖ ≤ τ i:=by
 obtain ⟨b,ρ,y,p,q⟩:=h i
 exact (P.silvered Z _ _ _ (m.already i) y p e e).trans q

variable (g:Tendsto (fun i=> (P.stitchApron Z (A i) (c (n i)) (r (n i))).realWidth P 3) atTop (𝓝 0))


include g v
lemma stitch_printed (t:ℝ)(p:0<t):
 Gleams (𝒞) (fun i=>V! i t) ((purePrice Z:ℂ) • v.printOp t):=by
 have k:Gleams (𝒞) (fun i=>π₀ • Y! i (t+w i) (t-w i)) (π₀ • v.printOp t):= by
    refine (v.wvary p ?_ ?_).smul tendsto_const_nhds
    · simpa using v.thin.const_add t
    simpa using (tendsto_const_nhds (x:=t)).sub v.thin
 have d':Tendsto (fun i=>V! i t - π₀ • Y! i (t+w i) (t-w i)) atTop (𝓝 0):=
    squeeze_zero_norm' ((g.eventually (ge_mem_nhds p)).mono fun i y=>
                          P.weight_silver Z x A m h i y)
                         P.macroStep_zero
 have e:=(Gleams.tightly (H:=(𝒞)) d').add k
 simp only [zero_add,sub_add_cancel] at e; exact e


lemma stitched_cap:
 P.Veloured 3 ξ (fun i=>Q₀ i):=by
 refine ⟨g, fun t z=> ⟨_,P.stitch_printed Z x A m h v g t z⟩,?_⟩
 obtain ⟨B,D,s,d,kG⟩:=v.rich
 let E:=‖π₀‖*B
 have e:0≤E:=mul_nonneg (norm_nonneg _) (zero_le_one.trans s)
 refine ⟨1+E,D,le_add_of_nonneg_right e,d,?_⟩
 filter_upwards [kG] with k pay
 let t:=τ k
 have p:0<t:=P.macroStep_pos _
 filter_upwards [pay,v.thin.eventually (ge_mem_nhds (by linarith:0<t/2)),
     g.eventually (ge_mem_nhds p),P.macroStep_zero.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1))]
    with i y hz U t'
 let c:=π₀ • Y! i (t+w i) (t-w i)
 refine (norm_le_norm_sub_add _ c).trans (by
    rw [add_mul]
    refine add_le_add ((P.weight_silver Z x A m h i U).trans (le_trans t' ((one_le_pow₀ d).trans_eq (one_mul _).symm))) ?_
    change ‖π₀ • Y! i (t+w i) (t-w i)‖ ≤ _
    unfold E
    rw [norm_smul, mul_assoc]
    refine mul_le_mul_of_nonneg_left (y (t+w i) ?_ (t-w i) ?_) (norm_nonneg _)
    · change t/2 ≤ _
      linarith only [(A i).real_width_pos P 3,p]
    change w i ≤ t/2 at hz
    change t/2 ≤ _
    linarith only [hz])


omit g
lemma night_stitch {K:P.Register}{J:P.Ellis 3 x}
    (z:P.Experiment K c r x J): P.Veloured 3 ξ (fun i=>Q₀ i):=by
 refine P.stitched_cap Z x A m h v ?_
 simp_rw [P.stitch_width _ Z _ (m.already _)]
 have t:= (v.thin.add (v.thin.const_mul 3)).add ((limit_width z.launch 3).comp m.fast.tendsto_atTop)
 rw [mul_zero,zero_add,zero_add] at t
 exact t
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

