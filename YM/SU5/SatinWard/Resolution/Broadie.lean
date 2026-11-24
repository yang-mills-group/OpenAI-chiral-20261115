import YM.SU5.SatinWard.Resolution.Domic
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Tapestry
open SlabMark Papal Papal.Moon Papal.Moon.Moonlit SwitchC Garland Terrace Juniper
namespace CasaF
open Swell Sonar Fock Tapestry.StageW LitCurrent LitCurrent.Chamber
open QuadClock Preparation.Tabletop
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)(s:ℕ)(i k:ℕ → ℕ) {r v:ℕ} {a b φ:ℝ} (A:∀ n,s<Y.uv (k n))
variable (X:∀ n,MaskPoint Y r s (i n) (k n) a b)(E:(n:ℕ) → eraτ Y s (i n) (k n) r a φ)
local notation "N" j:max=> side Y (i j) s
local notation "Yt"=> tent Y H
local notation "R"=> (Y.meter.a s)
local notation "S✩"=> pavilion (nodeC (0:Cover)) ((Y.meter.a s).B+12)
local notation "p_" j:max=> RootBook Y (i j) (k j) s
local notation "M✔" j:max=> (Y.voyage (i j)).CapeT s
-- Normalized residue geometry and EOM family statement.
open Vacancy VacuumSelection.VelourWiggle
local notation "Q†"=> qHull Λ.R.L (hat Λ.R.L Λ.x s)
local notation "J†"=> jHull Λ.R.L (hat Λ.R.L Λ.x s)
local notation "S†"=> hueW Λ.R.L (hat Λ.R.L Λ.x s)
noncomputable abbrev pmZ (r:ℕ)(j:Axis)(b:Bool):Cover:=(if b then (r:ℤ) else -(r:ℤ)) • step j
noncomputable def fullStar (Λ:Preparation)(s r:ℕ){K:Calibration}(F: Visit →  Cover →  Family K) : Cover →  Family K := let x:=hat Λ.R.L Λ.x s; let a:= hueW Λ.R.L x; let G(i:Axis)(b:Bool)(p:Cover):= F (some i) (p+pmZ r i b)
 (a/qHull Λ.R.L x :ℝ) • F none + (a/jHull Λ.R.L x:ℝ) • ∑ j:Axis,(G j true-G j false)
lemma shiftQo (r:ℕ)(i j:Axis)(b:Bool) : ((pmZ r i b) j).natAbs ≤ r := by unfold pmZ; by_cases p:i=j<;> cases b <;>simp [p]<;>simp [Ne.symm p]
lemma fullStar_live {Z:Calibration}{F:Visit →  Cover →  Family Z}{k:ℕ} (Λ:Preparation)(h:∀ v,Domicile k (F v)) (r:ℕ): Domicile (k+2*r) (fullStar Λ s r F):=by
 let A(i b)(p:Cover):= F (some i) (p+pmZ r i b)
 have hz(i:Axis)(b:Bool):Domicile (k+2*r) (A i b):= Domicile.flow_d _ (fun j=>shiftQo ..) (h _)
 refine Domicile.more (Domicile.tinted _ ((h none).lift (by omega: k≤k+2*r))) (Domicile.tinted _ (Domicile.count univ _ fun i _=>?_))
 exact (hz i true).less (hz i false)
abbrev hourBound :ℕ := (Y.meter.a s).B+12
local notation "B🌒"=> hourBound Y s
variable (D:Division)
-- exact coherence path.Oriented.Preserve for any futures.
structure Broadside (Z:ℕ → Visit →  Cover → Family (tent Y H)) (F:Visit → Cover →  Family (tent Y H)) :Prop where
 valid (u): Domicile (hourBound Y s) (F u)
 grants (j p): Domicile (hourBound Y s) (Z j p)
 bills(u a): BQueue (pavilion (nodeC a) (hourBound Y s)) (fun j=> Z j u a) (F u a)
 learns:∀ x j u, exhibit Y H s (i j) (Z j u x)= nearSprite Y D (E j) u (wrap (side Y (i j) s) x)
include A X
variable {Z:ℕ → Visit →  Cover → Family (tent Y H)}{F: Visit → Cover →  Family (tent Y H)}
lemma broad (U:∀ j, Roomy (pavilion (nodeC (0:Cover)) (hourBound Y s)) (side Y (i j) s)) (ha:0<a): ∃ L,∃ Z F, StrictMono (L:ℕ → ℕ)∧ Broadside Y H s (i ∘ L) (k ∘ L) (fun j=> E (L j)) D Z F:=by
 obtain ⟨v,Z,U',h,u⟩:=decidedAs Y H s i k A X E D ha U
 refine ⟨v,fun i p x=>carriage x (Z p i),fun p x=> carriage x (U' p),h,fun i=> Domicile.solo (u i).1.landing (u i).2.1,fun j p=> Domicile.solo ((u p).1.whereTo j) ((u p).2.2.1 j),fun p y=>?_,fun x j u'=> (u u').2.2.2 j x⟩
 simpa only [zero_add] using cueArr y (u p).1
omit X A
open LitCurrent
namespace Broadside
local notation "X✩"=> hat Λ.R.L Λ.x s
variable (W:Broadside Y H s i k E D Z F)
include W
lemma starBudget (u:Cover): BQueue (pavilion (nodeC u) (B🌒+2*r)) (fun i'=> fullStar Λ s r (Z i') u) (fullStar Λ s r F u):=by
 let A(j b):= u+pmZ r j b; have hk(j b):= cueMono (W.bills (some j) (A j b)) (Domicile.pavLord u (pmZ r j b) (fun j'=>shiftQo r j j' b) (B🌒))
 let U':=cueWords univ _ _ (fun j _=>cueSub (hk j true) (hk j false)); let S_:=cueMono (W.bills none u) (inclPav (nodeC u) _ (B🌒+2*r) (by omega))
 let T:=(S†)/(J†); let Y':=(S†)/(Q†)
 unfold fullStar; dsimp only; simp only [←Complex.coe_smul,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,Finset.sum_apply] -- order x occurrence.Stamp
 exact cueSum (cue_scale S_ (fun _=> (Y':ℂ)) (Y':ℂ) tendsto_const_nhds) (cue_scale U' (fun _=>(T:ℂ)) (T:ℂ) tendsto_const_nhds)
omit W
section
-- EOM formula at field heights K & Δ. REAL expts. Does not identify with physics.Space except under our actual amplitude comparisons; witness preparation & passage costs next.
local notation "Au"=> (RootBook Y (i 0) (k 0) s)
include W X
lemma starPrice (q:Cover)(j:ℕ)(g:0<lapQ Y s) : exhibit Y H s (i j) (fullStar Λ s r (Z j) q)= starField Y (E j) (wrap (side Y (i j) s) q) D:=by
 let n':= N j; let x:=wrap n' q; let C:= X✩; let T:= M✔ j; let p:= RootBook Y (i j) (k j) s; let k':=p.p.B/10; let aS:= (S†); let q':= Q†; let j':= J†
 let J(u:Axis)(y:Site n'):= jewelJ D y (E j) T p.p k' (1/2) (u,false); let W₀:= jewelY D x (E j) T p.p k'; let d:Mark n':= ∑ l:Axis,(J l (x+r • step l)-J l (x-r • step l))
 let y(i b):= q+pmZ r i b; have hx(i:Axis): y i true=q+r • step i ∧ y i false=q-r • step i:=by unfold y pmZ; simp [sub_eq_add_neg]
 have ht: jewelO D x (E j) T p.p k' (1/2)= W₀+d:= by
    funext i; let h':= physical_spelling D T p.p k' (1/2) x (E j) (X j).C i; rw [Pi.add_apply,show d i=_ from Finset.sum_apply ..]; exact h'
 unfold fullStar; dsimp only; simp only [←Complex.coe_smul, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,Pi.sub_apply,map_add,map_smul,map_sum,map_sub,W.learns]; unfold starField;
 simp_rw [← map_add (wrap (side Y (i j) s)) q]
 change (↑(aS/q'):ℂ) • ((↑q':ℂ) • (Complex.I • W₀)) + (↑(aS/j'):ℂ) • (∑ l:Axis,((↑j':ℂ) • (Complex.I • J l (wrap n' (y l true))) - (↑j':ℂ) • (Complex.I • J l (wrap n' (y l false))))) = (↑aS:ℂ) • (Complex.I • jewelO D x (E j) T p.p k' (1/2))
 have hc:0 < Pressure.temp C:=(Y.meter.boot s).1 ▸ (Y.meter.a s).threshold_pos
 have hp: 0 < pinpr Λ.R.L C:= g; have hi:=intLive C; have q1:0<q':=mul_pos (div_pos hp (by positivity)) hi; have j1:0< j':=mul_pos hp hi
 have hu:(∑ l:Axis,((↑j':ℂ) • (Complex.I • J l (wrap n' (y l true))) - (↑j':ℂ) • (Complex.I • J l (wrap n' (y l false)))))=(↑j':ℂ) • (Complex.I • d):=by
    unfold d; rw [Finset.smul_sum,Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [(hx i).1,(hx i).2,map_add,map_sub,map_nsmul,wrap_step]; simp [smul_sub]; rfl -- maybe map_nsmul same binder both
 rw [ht,hu,Complex.ofReal_div,Complex.ofReal_div,smul_smul _ (↑q':ℂ),smul_smul _ (↑j':ℂ), div_mul_cancel₀ _ (by exact_mod_cast q1.ne'), div_mul_cancel₀ _ (by exact_mod_cast j1.ne'), smul_add,smul_add]
end
end Broadside
end CasaF
end YM.CF.Buffered.Afterglow.Tower
