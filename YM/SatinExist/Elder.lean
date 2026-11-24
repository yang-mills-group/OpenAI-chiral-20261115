import YM.SatinExist.Chocolate
import SatinThinHarmonica
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 330000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
variable (P:Spine)(R : P.Register)(j:Axis){C A:ℝ}{Y:Supplier}(T:uniform P R Y C A)(D:P.NightCop)
variable (c r:ℕ→ℕ)
local notation "M"=>timeMesh P.par
local notation "R!"=>Real.sqrt (RedD+3)
local notation "E!" s:max i:max=> whenly (timeMesh P.par) s i
local notation "q'" n:max=> P.probeClock n
abbrev clubZ (Z:Lead.Clan)(j:Axis)(x: P.Spectrum0 j) (s n w:ℕ):=
 let Y:=P.thinMat Z s n; let E:= (P.physicalEnergy j x).E (whenly (timeMesh P.par) s (w-P.probeClock n j)); E*Y.engine P j x* E - demerit Z • (P.physicalEnergy j x).E (whenly (timeMesh P.par) s (w+w))
-- δ i * Op load secured ANY x. persists width budgets independent of x
abbrev dynC(j:Axis) (Z:Lead.Clan)(n w s i:ℕ) := (q' n) j < w ∧ whenly (timeMesh P.par) s w ≤ whenly (timeMesh P.par) i 1 ∧
   ∀ x:P.Spectrum0 j, ‖clubZ P Z j x s n w‖ ≤ R!/(i+1:ℕ)
structure LargeM (c r:ℕ→ℕ):Prop where
  buys (j:Axis)(Z:Lead.Clan):∀ i,∃ w:ℕ, dynC P j Z (r i) w (c i) i
variable (z:ℕ→ℕ)
open CF.Velvet
open Regis.Head.Brecht Regis.Circuit Regis.Head.Garland Papal
include T D
lemma sustain_large (D':ℝ)(hX:0<D'){C':ℝ}(p:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → Yoke.ShelterCost C' P.run s i k):∃ (c r:ℕ→ℕ), z≤r ∧ LargeM P c r ∧ ∀ᵐ x∂P.pillars 3,
  (∃ J:P.Ellis 3 x,Spine.Experiment P R c r x J) ∧ ∀ᶠ i in atTop,P.haloCost D' (c i) x < Yoke.canonWeight/32:=by
 have h(i:ℕ)(j:Axis)(Z:Lead.Clan):∀ᶠ n in atTop,∀ᶠ s in atTop,∃ w, dynC P j Z n w s i:=by
    filter_upwards [P.cardSerif R j C A Y T D Z (show (0:ℝ)<(↑(i+1:ℕ):ℝ) from (by positivity))] with n u
    obtain ⟨w,h,p⟩:= u
    have ht: Tendsto (fun s:ℕ=>whenly (timeMesh P.par) s w) atTop (𝓝 0):=by simpa [whenly] using ((vanishes (timeMesh P.par)).const_mul (w:ℝ≥0))
    filter_upwards [p, ht.eventually (ge_mem_nhds (when_pos (timeMesh P.par) i 1 (by decide)))] with s v t; exact ⟨_, h,t,v⟩
 let W(i n):Prop:=∀ j Z,∀ᶠ s in atTop,∃ w, dynC P j Z n w s i
 choose p' hp using fun i=>eventually_atTop.1 (show ∀ᶠ n:ℕ in atTop,W i n from eventually_all.mpr (fun j=>eventually_all.mpr (h i j)))
 obtain ⟨r,g,B,b⟩:= Prototype.outing T keyV keyV_positive (fun i=>max (z i) (p' i))
 obtain ⟨f,q⟩:= P.chooseFarther p D' (Yoke.canonWeight/32) hX (by have ht:=Yoke.focus_positive; positivity);
 choose l L using fun i=> eventually_atTop.mp (eventually_all.mpr (fun j=> eventually_all.mpr (hp i (r i) ((le_max_right ..).trans (g i)) j)))
 obtain ⟨c,h,t⟩:= choose_gradients fun i=> max (f i) (max (B i) (l i))
 have hd i:= (le_max_right ..).trans (t i); obtain ⟨e,v,m⟩:= b c h fun i=> (le_max_left ..).trans (hd i)
 refine ⟨c,r,fun i=>(le_max_left ..).trans (g i),⟨fun j Z i=> L i (c i) ((le_max_right ..).trans (hd i)) j Z⟩,?_⟩
 filter_upwards [P.many_stars 3 R,m,q c fun i=> (le_max_left ..).trans (t i)] with x j e' X'; obtain ⟨J⟩:=P.ellisP 3 x R; let hu:= P.parting 3 x R (P.homes_weather R 3 (P.all_phases 3 x j)); exact ⟨⟨J,e,e',hu, Spine.final_issues R J hu, P.footway _ J R hu⟩,X'⟩
omit T D
variable (U:LargeM P c r)
variable (x:P.Spectrum0 j) (Z:Lead.Clan)
local notation "X"=>P.ColorHil j x
local notation "ℰ" => P.physicalEnergy j x
local notation "E"=> (ℰ).E
local notation "W" i:max => E! (c i) (P.probeClock (r i) j)
def swordA (L:P.Apron) (R S:ℝ≥0) := (E R) * L.engine P j x * (E S)
local notation "A" i:max=> P.thinMat Z (c i) (r i)
-- get uniform on 2 heat. actual calendar sign/width
lemma larger_ed {R S:ℝ≥0}{i w:ℕ}(p:dynC P j Z (r i) w (c i) i)(u:E! i 1≤ R)(v:E! i 1 ≤ S) :
 dist (P.swordA j x (A i) R S) (demerit Z • E (R+(W i+W i)+S)) ≤ R!/(i+1:ℕ):=by
 obtain ⟨hd,ht,p⟩:=p;
 let d:=w-(q' (r i)) j; let X':= E! (c i) d; let W':= W i; let t:= E! (c i) w; let y:=R-X'; let f:=S-X'
 have hb:X' + W'= t:= by unfold X' d t W' whenly; rw [←add_mul,← Nat.cast_add, Nat.sub_add_cancel hd.le]
 have hv:X'≤t:=hb ▸ le_self_add
 have hr:y+X'= R:= tsub_add_cancel_of_le (hv.trans (ht.trans u))
 have he: X'+f=S:= add_tsub_cancel_of_le (hv.trans (ht.trans v))
 have h0:E! (c i) (w+w)= t+t:=by unfold t whenly; rw [←add_mul,Nat.cast_add]
 let B:=P.thinMat Z (c i) (r i)
 let C':= P.clubZ Z j x (c i) (r i) w
 have Cz:C'= E X' * B.engine P j x* E X' - demerit Z • E (t+t):=by unfold C' clubZ; rw [h0]
 have hq:∀ k l,E k * E l = E (k+l):= fun k l=> ((ℰ).time k l).symm
 have he': y+(t+t)+f=R+(W'+W')+S:=by rw [← hb]; calc
      _=(y+X')+(W'+W')+(X'+f):=by ac_rfl
      _=_:=by rw [hr,he]
 have hK:E y*C'*E f=P.swordA j x (A i) R S - demerit Z • E (R+(W'+W')+S):=by
    rw [Cz, mul_sub, _root_.sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hq,hq,he']; apply congrArg (· - _);
    calc
       _= (E y * E X')*B.engine P j x * (E X'* E f):=by simp only [mul_assoc]
       _=_ :=by rw [hq,hq,hr,he]; rfl
 rw [dist_eq_norm,←hK]; exact (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans ((mul_le_mul_of_nonneg_right ((ℰ).shrinks _) (norm_nonneg _)).trans_eq (one_mul ..))) ((ℰ).shrinks _) (norm_nonneg _) (norm_nonneg _)).trans ((mul_one ..).le.trans (p x)))
include U
lemma edelweiss (Z:Lead.Clan) :Tendsto (fun i=> W i) atTop (𝓝 0):=by
 apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds P.burst_zero (fun i=>zero_le) (fun i=>?_)
 obtain ⟨w,p,h,u⟩:= U.buys j Z i; exact ((when_le M _ _ _).2 p.le).trans h
set_option maxHeartbeats 800000 in
lemma sharpClub (R S:ℝ≥0) (p:0<R)(t:0<S) {A' B:ℕ→ℝ≥0}{X₀ Z':ℝ≥0}(u:Tendsto A' atTop (𝓝 X₀))(v:Tendsto B atTop (𝓝 Z')) :
 Tendsto (fun i=> P.swordA j x (P.thinMat Z (c i) (r i)) (R+A' i) (S+B i)) atTop (𝓝 (demerit Z • E (R+X₀+(S+Z')))):=by
 let U₁(i):=R+A' i; let U₂(i):=S+B i
 let M₁(i):=U₁ i+(W i+W i)+U₂ i; let k:= R+X₀+(S+Z')
 let C':= E k
 have h₁:= P.edelweiss j c r U Z
 have he:Tendsto M₁ atTop (𝓝 k):=by
    have h:= ((u.const_add R).add (h₁.add h₁)).add (v.const_add S); rw [add_zero,add_zero] at h; exact h
 have hu:Tendsto (fun i=> E (M₁ i)) atTop (𝓝 C'):= by
    let f(i:ℝ):= E i.toNNReal
    have hk:(0:ℝ)<(k:ℝ):=by unfold k; positivity
    have h:=Aria.steam_contPos (ℰ) k hk|>.tendsto.comp (NNReal.continuous_coe.continuousAt.tendsto.comp he); rw [Real.toNNReal_coe] at h
    exact h.congr fun i=>by simp [Function.comp_def]
 let X'(i):=demerit Z • E (M₁ i)
 have hz: Tendsto (fun i:ℕ=> R!/(↑(i+1:ℕ):ℝ)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (strictMono_nat_of_lt_succ (f:=fun i:ℕ=>i+1) fun i=>by omega).tendsto_atTop)
 have hr:Tendsto (fun i=> P.swordA j x (A i) (U₁ i) (U₂ i)-X' i) atTop (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' _ _ hz
    · exact Eventually.of_forall (fun i=> norm_nonneg _)
    filter_upwards [P.burst_zero.eventually (ge_mem_nhds p), P.burst_zero.eventually (ge_mem_nhds t)] with i h t; obtain ⟨w,hp⟩:= U.buys j Z i;
    exact (dist_eq_norm ..).ge.trans (P.larger_ed j c r x Z hp (h.trans (le_self_add)) (t.trans (le_self_add)))
 have hx:=hr.add (hu.const_smul (demerit Z)); rw [zero_add] at hx; exact hx.congr fun i=> sub_add_cancel _ _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
