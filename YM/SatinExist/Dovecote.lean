import YM.SatinExist.HymnB
import YM.SatinExist.Luminous
import YM.SatinExist.Igloo

/-!
 # P.S point signatures in every axis. Coupled P.Power invoices, no angular assumptions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry TopologicalSpace
namespace Spine
open Aria Casting
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld LineDeriv
open _root_.YM.Boundary Spectral
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) (j:Axis)
local notation "ξ"=>P.advocate 3 x j
local notation "CX"=> P.ManyF j (P.advocate 3 x j)
local notation "ν"=> P.seasons j (P.advocate 3 x j)
local notation "λ'"=> P.ColorHil j (P.advocate 3 x j)
local notation "ω"=> P.heaven j (P.advocate 3 x j)
local notation "g"=>P.pillar j (P.advocate 3 x j)
local notation "G"=> P.cartage j (P.advocate 3 x j)
local notation "Φ"=> Bench (P.seasons j (P.advocate 3 x j))
local notation "η"=> (P.seasons j (P.advocate 3 x j)).E
local notation "T"=> M (P.seasons j (P.advocate 3 x j))
local notation "K"=> Cache (P.seasons j (P.advocate 3 x j))
local notation "χ" i:max J:max=> (A i).pivot P J
variable (F:(P.ManyF j (P.advocate 3 x j)).Op) (r:ℕ)
variable (l:List Axis) (U:ℝ → (P.ManyF j (P.advocate 3 x j)).Op)(t:P.ActualScarab x A j l U)(h:RealMint (P.seasons j (P.advocate 3 x j)) r U F)
-- Every axis navigation (absolute Mink p, Vantage j perpendicular via cart).
lemma actual_times (p:E4): (P.seasons j (P.advocate 3 x j)).U (OS.Semigroup.SEP j p)=G (lens p):=by -- namespace
 rw [P.uses_cart]; apply congrArg _; rw [eyes_toFace j (OS.Semigroup.SEP j p)]; apply congrArg _
 funext i; change (p-p j • basis j) i.val=p i.val; have ht:i.val ≠ j:=i.property; simp only [PiLp.sub_apply,PiLp.smul_apply]; simp [ht]
lemma actual_tours (p:E4): T (sepV j p)=G (lens p):=by unfold sepV; rw [laneslot, P.actual_times] -- tune
lemma transportsK (p:E4): T p ω=ω:=by
 let z:=(ν); have h: ω∈z.ground:= ((ν).fixed _).2 (P.heaven_hot j ξ)
 change z.edge (p j) (z.U _ _) = _; rw [show z.U _=_ from P.actual_times x j p, P.cart_empty]; exact Spectral.Alps.mink_invar z ω (p j) h
noncomputable def Asp: Bench (P.seasons j (P.advocate 3 x j)):= ⟨ω, hail (ν) ω (P.heaven_hot j ξ)⟩
-- any one-gap seal. gap coords real not ticks. Bare positions still future.
lemma moves_edge (D:P.Apron) (p:E4) (a b:ℝ):
    P.pillar j ξ D a b (lens p)= T (sepV j p) * P.pillar j ξ D (a-p j) (b-p j) 0*T (-sepV j p):=by
 let Q:=g D (a-p j) (b-p j) 0
 rw [P.actual_tours,← tstar,P.actual_tours]; change _=G (lens p)*Q*star (G (lens p)); rw [show star (G (lens p))=G (- lens p) from P.cart_reverses ..]; refine Eq.trans ?_ (P.travels_door j ξ D (a-p j) (b-p j) 0 (lens p)); congr 2 <;> (first| rfl| (simp [lens])) -- tune
section
include t h
lemma doors_open {a b :ℝ}(d:0 < a)(v:0 < b): Brakes (fun i=> g (χ i l) (-a) b 0) (Par (ν) r (Real.toNNReal a)*F*Par (ν) r b.toNNReal) := by
 let s:= min a b; have hx:s≤a:= min_le_left ..; have ht:s≤b:=min_le_right ..; have hz:0 < s:= lt_min d v; have hh:= (t.prices.paid s hz); simp_rw [one_smul] at hh
 let y:=s.toNNReal; let W:=η (a-s).toNNReal; let X:=η (b-s).toNNReal; have hW:Brakes (fun _:ℕ=>W) W:= Brakes.by_budget tendsto_const_nhds; have hX:Brakes (fun _:ℕ=>X) X:=Brakes.by_budget tendsto_const_nhds
 apply ((hW.weave hh).weave hX).sameC
 · filter_upwards [t.prices.thin.eventually (gt_mem_nhds hz)] with i e; let D:= χ i l; change D.realWidth P j < s at e; have he:= P.bigger_door j ξ D (-a) b (-s) s 0 (neg_le_neg hx) ht (by unfold Apron.time_panel; simp only [Pi.zero_apply]; linarith only [e]) (by unfold Apron.time_edge; simp only [Pi.zero_apply]; linarith only [e]); rw [show -s - -a=a-s from by abel] at he
   exact he.symm
 let Z:=F; have t':0< y:=Real.toNNReal_pos.mpr hz; have hu: U s = Par (ν) r y* F* Par (ν) r y:=by have u:= h y t'; simpa only [show (y:ℝ)=s from Real.coe_toNNReal _ hz.le] using u
 rw [hu]; have hw(t:ℝ)(v:s≤t): Par (ν) r y*η (t-s).toNNReal=Par (ν) r t.toNNReal:=by have e:=landDiv (ν) t.toNNReal r y t' (Real.toNNReal_le_toNNReal v); rw [show t.toNNReal-y=(t-s).toNNReal from NNReal.eq (by rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal v), Real.coe_toNNReal _ (hz.le.trans v), Real.coe_toNNReal _ (sub_nonneg.mpr v)]; rw [show (y:ℝ)=s from Real.coe_toNNReal _ hz.le])] at e; exact e.symm
 have hw': W * Par (ν) r y=Par (ν) r a.toNNReal:=by
    have H:=congrArg star (hw a hx); rw [star_mul,(parRev (ν) y r t').star_eq, show star (η _) = η (a-s).toNNReal from (ν).sym _, (parRev (ν) _ _ (Real.toNNReal_pos.mpr d)).star_eq] at H; exact H
 change W*(Par _ _ _ * _ * _)*X=_; simp only [mul_assoc]; rw [hw b ht,←mul_assoc W,hw'] -- tune X
lemma certificate {a b:ℝ} (p:E4) (v:a < p j)(u:p j < b): Brakes (fun i=>g (χ i l) a b (lens p)) (T (sepV j p)*Par (ν) r (p j-a).toNNReal *F* Par (ν) r (b-p j).toNNReal*T (-sepV j p)):=by
 simp_rw [P.moves_edge, show a-p j= -(p j-a) from by abel]; have he:=P.doors_open x A j F r l U t h (sub_pos.mpr v) (sub_pos.mpr u)
 have hp(X:(CX).Op):Brakes (fun _:ℕ => X) X:=Brakes.by_budget tendsto_const_nhds
 exact ((hp (T (sepV j p))|>.weave he|>.weave (hp _)).sameC (Eventually.of_forall fun i=>rfl) (by simp [mul_assoc])) -- order
end
lemma wanna (l:List Axis): (∃ U, P.ActualScarab x A j l U) → ∃ (r:ℕ) (F:(P.ManyF j (P.advocate 3 x j)).Op), ∃ U, P.ActualScarab x A j l U ∧ RealMint (P.seasons j (P.advocate 3 x j)) r U F:=by
 rintro ⟨U,t⟩; obtain ⟨K',u,m,v⟩:= t.order -- check name
 have X':=t.prices
 refine ⟨m+1,_,U,t,funds_heat (ν) m U K' (Mosaic.tariff _ _ _ _ _ X') u v⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
